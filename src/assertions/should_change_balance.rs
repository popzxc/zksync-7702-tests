use alloy::{
    network::Ethereum,
    primitives::{Address, I256, U256},
    providers::{Provider, RootProvider},
    rpc::types::TransactionReceipt,
};

use crate::assertions::{Assertion, TxAssertion};
use crate::contracts::evm::Erc20;

// This wrapper is needed because in alloy, &dyn Provider does not implement Provider,
// which makes it impossible to use it to construct contract instances.
#[derive(Clone)]
struct WrappedProvider<'a>(&'a dyn Provider);

impl<'a> Provider for WrappedProvider<'a> {
    fn root(&self) -> &RootProvider {
        self.0.root()
    }
}

#[derive(Debug, Clone, Copy)]
pub enum Token {
    Base,
    Erc20(Address),
}

#[derive(Debug, Clone, Copy)]
pub struct ShouldChangeBalance {
    account: Address,
    amount: I256,
    token: Token,
    balance: Option<U256>,
}

impl ShouldChangeBalance {
    async fn fetch_balance(&self, provider: &dyn Provider<Ethereum>) -> anyhow::Result<U256> {
        match &self.token {
            Token::Base => Ok(provider.get_balance(self.account).await?),
            Token::Erc20(address) => {
                let erc20 = Erc20::Erc20Instance::new(*address, WrappedProvider(provider));
                Ok(erc20.balanceOf(self.account).call().await?._0)
            }
        }
    }
}

#[async_trait::async_trait]
impl Assertion for ShouldChangeBalance {
    async fn before_submission(&mut self, provider: &dyn Provider<Ethereum>) -> anyhow::Result<()> {
        self.balance = Some(self.fetch_balance(provider).await?);
        Ok(())
    }

    async fn on_receipt(
        &mut self,
        provider: &dyn Provider<Ethereum>,
        _receipt: TransactionReceipt,
    ) -> anyhow::Result<()> {
        let new_balance = self.fetch_balance(provider).await?;
        match self.balance {
            Some(old_balance) => {
                let abs_amount: U256 = self.amount.abs().try_into().unwrap();
                if self.amount.is_negative() {
                    anyhow::ensure!(
                        new_balance == old_balance - abs_amount,
                        "Balance didn't decrease as expected for account {}: expected {}, got {}",
                        self.account,
                        old_balance - abs_amount,
                        new_balance
                    );
                    Ok(())
                } else {
                    anyhow::ensure!(
                        new_balance == old_balance + abs_amount,
                        "Balance didn't increase as expected  for account {}: expected {}, got {}",
                        self.account,
                        old_balance + abs_amount,
                        new_balance
                    );
                    Ok(())
                }
            }
            None => anyhow::bail!("Balance was not fetched before submission"),
        }
    }
}

impl TxAssertion {
    pub fn should_change_balance(account: Address, token: Token, amount: I256) -> Self {
        Self(Box::new(ShouldChangeBalance {
            account,
            token,
            amount,
            balance: None,
        }))
    }
}
