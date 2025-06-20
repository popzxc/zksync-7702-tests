use alloy::{
    network::Ethereum, primitives::Address, providers::Provider, rpc::types::TransactionReceipt,
};

use crate::assertions::{Assertion, TxAssertion};

#[derive(Debug, Clone, Copy)]
pub struct ShouldIncremetNonce {
    account: Address,
    amount: u64,
    nonce: Option<u64>,
}

#[async_trait::async_trait]
impl Assertion for ShouldIncremetNonce {
    async fn before_submission(&mut self, provider: &dyn Provider<Ethereum>) -> anyhow::Result<()> {
        self.nonce = Some(provider.get_transaction_count(self.account).await?);
        Ok(())
    }

    async fn on_receipt(
        &mut self,
        provider: &dyn Provider<Ethereum>,
        _receipt: TransactionReceipt,
    ) -> anyhow::Result<()> {
        let new_nonce = provider.get_transaction_count(self.account).await?;
        match self.nonce {
            Some(old_nonce) if new_nonce == old_nonce + self.amount => Ok(()),
            Some(old_nonce) => anyhow::bail!(
                "Nonce was not incremented for account {}: expected {}, got {}",
                self.account,
                old_nonce + self.amount,
                new_nonce
            ),
            None => anyhow::bail!("Nonce was not fetched before submission"),
        }
    }
}

impl TxAssertion {
    pub fn should_increment_nonce(account: Address, amount: u64) -> Self {
        Self(Box::new(ShouldIncremetNonce {
            account,
            amount,
            nonce: None,
        }))
    }

    pub fn should_not_increment_nonce(account: Address) -> Self {
        Self(Box::new(ShouldIncremetNonce {
            account,
            amount: 0, // No increment expected
            nonce: None,
        }))
    }
}
