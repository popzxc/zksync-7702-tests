use alloy::{
    network::Ethereum,
    primitives::{Address, U256},
    providers::Provider,
    rpc::types::TransactionReceipt,
};

use crate::assertions::{Assertion, TxAssertion};

#[derive(Debug, Clone, Copy)]
pub struct ShouldChangeStorage {
    pub address: Address,
    pub slot: U256,
    pub expected_value: U256,
}

#[async_trait::async_trait]
impl Assertion for ShouldChangeStorage {
    async fn on_receipt(
        &mut self,
        provider: &dyn Provider<Ethereum>,
        _receipt: TransactionReceipt,
    ) -> anyhow::Result<()> {
        let value = provider.get_storage_at(self.address, self.slot).await?;
        if value != self.expected_value {
            return Err(anyhow::anyhow!(
                "Storage at address {} slot {} should be {}, but is {}",
                self.address,
                self.slot,
                self.expected_value,
                value
            ));
        }
        Ok(())
    }
}

impl TxAssertion {
    pub fn should_change_storage(address: Address, slot: U256, expected_value: U256) -> Self {
        Self(Box::new(ShouldChangeStorage {
            address,
            slot,
            expected_value,
        }))
    }
}
