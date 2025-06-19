use alloy::{network::Ethereum, providers::Provider, rpc::types::TransactionReceipt};

use crate::assertions::{Assertion, TxAssertion};

#[derive(Debug, Clone, Copy)]
pub struct ShouldSucceed;

#[async_trait::async_trait]
impl Assertion for ShouldSucceed {
    async fn on_receipt(
        &mut self,
        _provider: &dyn Provider<Ethereum>,
        receipt: TransactionReceipt,
    ) -> anyhow::Result<()> {
        if !receipt.status() {
            return Err(anyhow::anyhow!(
                "Transaction should have succeeded, but failed"
            ));
        }
        Ok(())
    }
}

impl TxAssertion {
    pub fn should_succeed() -> Self {
        Self(Box::new(ShouldSucceed))
    }
}
