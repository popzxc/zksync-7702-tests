use alloy::{
    eips::eip7702::SignedAuthorization,
    network::Ethereum,
    primitives::{Address, U256},
    providers::{PendingTransactionError, Provider},
    rpc::types::{Authorization, TransactionReceipt, TransactionRequest},
    signers::{SignerSync as _, local::PrivateKeySigner},
    transports::{RpcError, TransportErrorKind},
};
use anyhow::Context as _;

mod should_change_balance;
mod should_change_storage;
mod should_emit_log;
mod should_increment_nonce;
mod should_revert;
mod should_succeed;

pub use should_change_balance::Token;

#[derive(Debug)]
pub struct TxAssertion(Box<dyn Assertion>);

#[async_trait::async_trait]
pub trait Assertion: Send + Sync + 'static + std::fmt::Debug {
    async fn before_submission(
        &mut self,
        _provider: &dyn Provider<Ethereum>,
    ) -> anyhow::Result<()> {
        Ok(())
    }

    async fn on_failed_send(
        &mut self,
        _provider: &dyn Provider<Ethereum>,
        err: &RpcError<TransportErrorKind>,
    ) -> anyhow::Result<()> {
        anyhow::bail!("Transaction submission failed: {}", err.to_string());
    }

    async fn on_get_receipt_failure(
        &mut self,
        _provider: &dyn Provider<Ethereum>,
        err: &PendingTransactionError,
    ) -> anyhow::Result<()> {
        anyhow::bail!("Failed to get transaction receipt: {}", err.to_string());
    }

    async fn on_receipt(
        &mut self,
        _provider: &dyn Provider<Ethereum>,
        _receipt: TransactionReceipt,
    ) -> anyhow::Result<()> {
        Ok(())
    }
}

#[async_trait::async_trait]
pub trait AssertingProvider: Provider<Ethereum> + Sized {
    async fn send_with_assertions(
        &self,
        request: impl Into<TransactionRequest> + Send + Sync + 'static,
        assertions: impl IntoIterator<Item = TxAssertion> + Send + Sync + 'static,
    ) -> anyhow::Result<()> {
        let provider = self;
        let request = request.into();
        let mut assertions = assertions.into_iter().collect::<Vec<_>>();
        for assertion in &mut assertions {
            assertion
                .0
                .before_submission(provider)
                .await
                .with_context(|| format!("{assertion:?}::before_submission"))?;
        }

        let pending_tx = match provider.send_transaction(request).await {
            Ok(hash) => hash,
            Err(err) => {
                for assertion in &mut assertions {
                    assertion
                        .0
                        .on_failed_send(provider, &err)
                        .await
                        .with_context(|| format!("{assertion:?}::on_failed_send"))?;
                }
                return Ok(());
            }
        };
        tracing::info!("Submitted tx: {:?}", pending_tx.tx_hash());

        let receipt = match pending_tx.get_receipt().await {
            Ok(receipt) => receipt,
            Err(err) => {
                for assertion in &mut assertions {
                    assertion
                        .0
                        .on_get_receipt_failure(provider, &err)
                        .await
                        .with_context(|| format!("{assertion:?}::on_get_receipt_failure"))?;
                }
                return Ok(());
            }
        };
        tracing::debug!(?receipt, "Transaction receipt received");

        for assertion in &mut assertions {
            assertion
                .0
                .on_receipt(provider, receipt.clone())
                .await
                .with_context(|| format!("{assertion:?}::on_receipt"))?;
        }

        Ok(())
    }
}

#[async_trait::async_trait]
impl<P: Provider<Ethereum> + Send + Sync + 'static> AssertingProvider for P {}

#[async_trait::async_trait]
pub trait DelegatingProvider: Provider<Ethereum> + Sized {
    async fn sign_authorization(
        &self,
        nonce_increment: u64,
        delegated: &PrivateKeySigner,
        delegate_to: Address,
    ) -> anyhow::Result<SignedAuthorization> {
        let chain_id = U256::from(
            self.get_chain_id()
                .await
                .context("Unable to get chain ID for signing authorization")?,
        );

        let nonce = self
            .get_transaction_count(delegated.address())
            .await
            .context("Unable to get nonce for signing authorization")?
            + nonce_increment;

        let auth = Authorization {
            chain_id,
            address: delegate_to,
            nonce,
        };
        let signature = delegated
            .sign_hash_sync(&auth.signature_hash())
            .context("Unable to sign authorization")?;
        Ok(auth.into_signed(signature))
    }
}

#[async_trait::async_trait]
impl<P: Provider<Ethereum> + Send + Sync + 'static> DelegatingProvider for P {}
