use alloy::{network::Ethereum, providers::Provider, rpc::types::TransactionReceipt};

use crate::assertions::{Assertion, TxAssertion};

#[derive(Debug, Clone, Copy)]
pub struct ShouldRevert;

#[async_trait::async_trait]
impl Assertion for ShouldRevert {
    async fn on_receipt(
        &mut self,
        _provider: &dyn Provider<Ethereum>,
        receipt: TransactionReceipt,
    ) -> anyhow::Result<()> {
        if receipt.status() {
            return Err(anyhow::anyhow!(
                "Transaction should have reverted, but suceeded"
            ));
        }
        Ok(())
    }
}

impl TxAssertion {
    pub fn should_revert() -> Self {
        Self(Box::new(ShouldRevert))
    }
}
