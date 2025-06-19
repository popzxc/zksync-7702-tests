use std::fmt;

use alloy::{
    network::Ethereum,
    providers::Provider,
    rpc::types::{Log, TransactionReceipt},
};

use crate::assertions::{Assertion, TxAssertion};

pub struct ShouldEmitLog {
    filter: Box<dyn Fn(&Log) -> bool + Send + Sync + 'static>,
}

impl fmt::Debug for ShouldEmitLog {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ShouldEmitLog").finish()
    }
}

#[async_trait::async_trait]
impl Assertion for ShouldEmitLog {
    async fn on_receipt(
        &mut self,
        _provider: &dyn Provider<Ethereum>,
        receipt: TransactionReceipt,
    ) -> anyhow::Result<()> {
        if !receipt.logs().iter().any(|l| (self.filter)(l)) {
            return Err(anyhow::anyhow!(
                "ShouldEmitLog assertion failed: no log matching the filter found in receipt {receipt:?}",
            ));
        }
        Ok(())
    }
}

impl TxAssertion {
    pub fn should_emit_log(filter: impl Fn(&Log) -> bool + Send + Sync + 'static) -> Self {
        Self(Box::new(ShouldEmitLog {
            filter: Box::new(filter),
        }))
    }
}
