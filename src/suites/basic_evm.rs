use crate::{
    contracts::{
        self,
        evm::{
            DelegationTarget::DelegationTargetInstance, Erc20::Erc20Instance,
            Evm7702Checker::Evm7702CheckerInstance,
            SimpleDelegateContract::SimpleDelegateContractInstance,
        },
    },
    utils::Deployer,
};
use alloy::{
    network::{Ethereum, TransactionBuilder, TransactionBuilder7702},
    primitives::{Address, Bytes, U256, address, keccak256},
    providers::{DynProvider, Provider},
    rpc::types::{Authorization, TransactionRequest},
    signers::{SignerSync as _, local::PrivateKeySigner},
    transports::RpcError,
};

use e2e::test_suite;

use super::TestConfig;

#[derive(Debug, Clone)]
pub(crate) struct BasicEvmFlow {
    deployer: Deployer,
    alice: PrivateKeySigner,
    evm_provider: DynProvider<Ethereum>,
    erc20: Erc20Instance<(), DynProvider<Ethereum>>,
    simple_delegate_contract: SimpleDelegateContractInstance<(), DynProvider<Ethereum>>,
    delegation_target_evm: DelegationTargetInstance<(), DynProvider<Ethereum>>,
    delegation_target_eravm: DelegationTargetInstance<(), DynProvider<Ethereum>>,
    checker: Evm7702CheckerInstance<(), DynProvider<Ethereum>>,
}

#[test_suite("Basic EVM flow")]
impl BasicEvmFlow {
    #[constructor]
    async fn new(config: &TestConfig) -> anyhow::Result<Self> {
        // let main_pk: PrivateKeySigner = config.main_pk.parse().unwrap();

        let deployer = Deployer::Evm;
        let alice = PrivateKeySigner::random();

        let evm_provider = alloy::providers::builder::<Ethereum>()
            .with_recommended_fillers()
            .wallet(alice.clone())
            .on_http(config.rpc_url.parse().unwrap())
            .erased();

        let _res: bool = evm_provider
            .raw_request(
                "anvil_setBalance".into(),
                [
                    alice.address().to_string(),
                    "0x100000000000000000000".to_string(), // 100 ETH in wei
                ],
            )
            .await?;
        anyhow::ensure!(
            evm_provider.get_balance(alice.address()).await? > U256::from(0),
            "Alice's balance should be greater than 0",
        );

        let erc20 = deployer
            .deploy_erc20(alice.clone(), &config.rpc_url)
            .await?;
        erc20
            .mint(U256::from(1000000), alice.address())
            .send()
            .await?
            .watch()
            .await?;

        let simple_delegate_contract = deployer
            .deploy_simple_delegate_contract(alice.clone(), &config.rpc_url)
            .await?;

        let delegation_target_evm = deployer
            .deploy_delegation_target(alice.clone(), &config.rpc_url)
            .await?;
        let delegation_target_eravm = deployer
            .opposite()
            .deploy_delegation_target(alice.clone(), &config.rpc_url)
            .await?;

        let checker = contracts::evm::Evm7702Checker::deploy(evm_provider.clone()).await?;

        Ok(Self {
            deployer,
            alice,
            evm_provider,
            erc20,
            simple_delegate_contract,
            delegation_target_evm,
            delegation_target_eravm,
            checker,
        })
    }

    #[test_case("Set authorization")]
    async fn set_authorization(&self) -> anyhow::Result<()> {
        tracing::info!("Setting auth to the deployed contract");
        let auth = Authorization {
            chain_id: U256::from(self.evm_provider.get_chain_id().await?),
            address: *self.simple_delegate_contract.address(),
            nonce: self
                .evm_provider
                .get_transaction_count(self.alice.address())
                .await?
                + 1, // Should use next nonce
        };
        let signature = self.alice.sign_hash_sync(&auth.signature_hash())?;
        let signed_authorization = auth.into_signed(signature);
        let tx = TransactionRequest::default()
            .with_to(Address::default())
            .with_authorization_list(vec![signed_authorization]);
        let pending_tx = self.evm_provider.send_transaction(tx).await?;
        tracing::info!("Submitted tx: {:?}", pending_tx.tx_hash());
        let receipt = pending_tx.get_receipt().await?;
        tracing::debug!(?receipt, "Transaction receipt received");
        if !receipt.status() {
            return Err(anyhow::anyhow!("Transaction failed: {:?}", receipt));
        }
        tracing::info!("Authorization set successfully");
        Ok(())
    }

    #[test_case("Can get code")]
    async fn get_code(&self) -> anyhow::Result<()> {
        let code = self.evm_provider.get_code_at(self.alice.address()).await?;

        // Expected code is `0xef0100` || address of contract.
        let expected_code = format!("0xef0100{:x}", self.simple_delegate_contract.address());

        anyhow::ensure!(
            code.to_string() == expected_code,
            "Code does not match expected: {} != {}",
            code.to_string(),
            expected_code
        );

        Ok(())
    }

    /// Check that all the properties in system contracts (e.g. `ContractDeployer::get_delegation_address`)
    /// perform as expected.
    #[test_case("Delegation artifacts in system contracts")]
    async fn delegation_artifacts_in_system_contracts(&self) -> anyhow::Result<()> {
        let account_code_storage =
            crate::contracts::era_vm::contract_deployer(self.evm_provider.clone());
        let delegation_address = account_code_storage
            .getAccountDelegation(self.alice.address())
            .call()
            .await?
            ._0;
        anyhow::ensure!(
            delegation_address == *self.simple_delegate_contract.address(),
            "Delegation address does not match: expected {}, got {}",
            self.simple_delegate_contract.address(),
            delegation_address
        );

        let account_code_storage =
            crate::contracts::era_vm::account_code_storage(self.evm_provider.clone());
        let versioned_bytecode_hash = account_code_storage
            .getRawCodeHash(self.alice.address())
            .call()
            .await?
            .codeHash;
        let mut expected_bytecode_hash = [0u8; 32];
        expected_bytecode_hash[0..12]
            .copy_from_slice(&hex::decode("020200170000000000EF0100").unwrap());
        expected_bytecode_hash[12..32].copy_from_slice(delegation_address.as_slice());
        anyhow::ensure!(
            versioned_bytecode_hash == expected_bytecode_hash,
            "Versioned bytecode hash does not match expected: {:?} != {:?}",
            versioned_bytecode_hash,
            expected_bytecode_hash
        );

        let evm_hashes_storage =
            crate::contracts::era_vm::evm_hashes_storage(self.evm_provider.clone());
        let evm_bytecode_hash = evm_hashes_storage
            .getEvmCodeHash(versioned_bytecode_hash)
            .call()
            .await?
            ._0;
        let expected_keccak_hash = keccak256(&expected_bytecode_hash[9..]);
        anyhow::ensure!(
            evm_bytecode_hash == expected_keccak_hash,
            "EVM bytecode hash does not match expected: {:?} != {:?}",
            evm_bytecode_hash,
            expected_keccak_hash
        );

        Ok(())
    }

    #[test_case("EVM code properties")]
    async fn evm_code_properties(&self) -> anyhow::Result<()> {
        // First check with `eth_call`

        let bytecode = self
            .checker
            .getAddressBytecode(self.alice.address())
            .call()
            .await?
            ._0;
        let expected_code: Bytes = format!("0xef0100{:x}", self.simple_delegate_contract.address())
            .parse()
            .unwrap();
        anyhow::ensure!(
            bytecode == expected_code,
            "Bytecode does not match expected: {} != {}",
            bytecode,
            expected_code
        );

        let code_hash = self
            .checker
            .getAddressBytecodeHash(self.alice.address())
            .call()
            .await?
            ._0;
        let expected_hash = keccak256(&expected_code);
        anyhow::ensure!(
            code_hash == expected_hash,
            "Code hash does not match expected: {:?} != {:?}",
            code_hash,
            expected_hash
        );

        // Now check with submitted transactions.
        let receipt = self
            .checker
            .assertAddressBytecode(self.alice.address(), expected_code.clone())
            .send()
            .await?
            .get_receipt()
            .await?;
        anyhow::ensure!(receipt.status(), "Transaction failed: {:?}", receipt);
        let receipt = self
            .checker
            .assertAddressBytecodeHash(self.alice.address(), expected_hash)
            .send()
            .await?
            .get_receipt()
            .await?;
        anyhow::ensure!(receipt.status(), "Transaction failed: {:?}", receipt);

        Ok(())
    }

    #[test_case("Check msg.sender")]
    async fn check_msg_sender(&self) -> anyhow::Result<()> {
        let execute_calldata = self
            .simple_delegate_contract
            .ensureMsgSender(self.alice.address())
            .calldata()
            .clone();
        let tx = TransactionRequest::default()
            .with_to(self.alice.address())
            .with_input(execute_calldata);
        let pending_tx = self.evm_provider.send_transaction(tx).await?;
        tracing::info!("Submitted tx: {:?}", pending_tx.tx_hash());
        let receipt = pending_tx.get_receipt().await?;
        tracing::debug!(?receipt, "Transaction receipt received");
        if !receipt.status() {
            return Err(anyhow::anyhow!("Transaction failed: {:?}", receipt));
        }

        Ok(())
    }

    #[test_case("Send operation")]
    async fn send_operation(&self) -> anyhow::Result<()> {
        tracing::info!("Sending operation...");

        let bob_address = Address::repeat_byte(0x5c);
        let value_to_send = U256::from(1000);
        let call = contracts::evm::SimpleDelegateContract::Call {
            to: bob_address,
            value: value_to_send,
            data: Default::default(),
        };
        let execute_calldata = self
            .simple_delegate_contract
            .execute(vec![call])
            .calldata()
            .clone();
        let tx = TransactionRequest::default()
            .with_to(self.alice.address())
            .with_value(value_to_send)
            .with_input(execute_calldata);
        let pending_tx = self.evm_provider.send_transaction(tx).await?;
        tracing::info!("Submitted tx: {:?}", pending_tx.tx_hash());
        let receipt = pending_tx.get_receipt().await?;
        tracing::debug!(?receipt, "Transaction receipt received");
        if !receipt.status() {
            return Err(anyhow::anyhow!("Transaction failed: {:?}", receipt));
        }
        let bob_balance = self.evm_provider.get_balance(bob_address).await?;
        if bob_balance < value_to_send {
            return Err(anyhow::anyhow!(
                "Bob's balance is less than expected: {bob_balance}, expected: {value_to_send}"
            ));
        }

        Ok(())
    }

    #[test_case("Fail transaction with revert")]
    async fn revert_processed(&self) -> anyhow::Result<()> {
        let execute_calldata = self
            .simple_delegate_contract
            .triggerRevert()
            .calldata()
            .clone();
        let tx = TransactionRequest::default()
            .with_to(self.alice.address())
            .with_input(execute_calldata)
            .with_gas_limit(1_000_000);
        let pending_tx = self.evm_provider.send_transaction(tx).await?;
        tracing::info!("Submitted tx: {:?}", pending_tx.tx_hash());
        let receipt = pending_tx.get_receipt().await?;
        tracing::debug!(?receipt, "Transaction receipt received");
        if receipt.status() {
            return Err(anyhow::anyhow!("Transaction succeeded: {:?}", receipt));
        }

        Ok(())
    }

    #[test_case("Revert reason in eth_call")]
    async fn revert_reason_in_eth_call(&self) -> anyhow::Result<()> {
        let execute_calldata = self
            .simple_delegate_contract
            .triggerRevert()
            .calldata()
            .clone();
        let tx = TransactionRequest::default()
            .with_to(self.alice.address())
            .with_input(execute_calldata)
            .with_gas_limit(1_000_000);
        let call_result = self.evm_provider.call(tx).await;
        let Err(RpcError::ErrorResp(error)) = call_result else {
            return Err(anyhow::anyhow!("Call succeeded"));
        };
        anyhow::ensure!(
            error.message == "execution reverted: This is a revert",
            "Expected revert reason, got: {}",
            error.message,
        );

        Ok(())
    }

    #[test_case("Can still use as an EOA (contract invocation)")]
    async fn use_eoa(&self) -> anyhow::Result<()> {
        let bob = Address::repeat_byte(0x66);
        tracing::info!("Checking if EOA can still be used for contract invocation");
        let bob_balance_before = self.erc20.balanceOf(bob).call().await?._0;
        tracing::info!("Bob's balance before: {:?}", bob_balance_before);

        let pending_tx = self.erc20.transfer(bob, U256::from(500)).send().await?;
        tracing::info!("Submitted tx: {:?}", pending_tx.tx_hash());
        let receipt = pending_tx.get_receipt().await?;
        tracing::debug!(?receipt, "Transaction receipt received");
        if !receipt.status() {
            return Err(anyhow::anyhow!("Transaction failed: {:?}", receipt));
        }

        // Check that the balance has changed
        let bob_balance = self.erc20.balanceOf(bob).call().await?._0;
        anyhow::ensure!(
            bob_balance - bob_balance_before == U256::from(500),
            "Bob's balance did not increase as expected"
        );

        Ok(())
    }

    #[test_case("Can still use as an EOA (with value)")]
    async fn use_eoa_with_value(&self) -> anyhow::Result<()> {
        let bob = Address::repeat_byte(0x5d);
        let bob_balance_before = self.evm_provider.get_balance(bob).await?;

        let tx = TransactionRequest::default()
            .with_to(bob)
            .with_value(U256::from(500));
        let pending_tx = self.evm_provider.send_transaction(tx).await?;
        tracing::info!("Submitted tx: {:?}", pending_tx.tx_hash());
        let receipt = pending_tx.get_receipt().await?;
        tracing::debug!(?receipt, "Transaction receipt received");
        if !receipt.status() {
            return Err(anyhow::anyhow!("Transaction failed: {:?}", receipt));
        }

        // Check that the balance has changed
        let bob_balance = self.evm_provider.get_balance(bob).await?;
        anyhow::ensure!(
            bob_balance - bob_balance_before == U256::from(500),
            "Bob's balance did not increase as expected"
        );

        Ok(())
    }

    #[test_case("Can delegate to within runtime")]
    async fn delegate_within_runtime(&self) -> anyhow::Result<()> {
        let contract = match self.deployer {
            Deployer::Evm => &self.delegation_target_evm,
            Deployer::EraVm => &self.delegation_target_eravm,
        };
        let address = *contract.address();

        let value_to_set = U256::from(42);
        let call = contracts::evm::SimpleDelegateContract::Call {
            to: address,
            value: Default::default(),
            data: contract.setValue(value_to_set).calldata().clone(),
        };
        let execute_calldata = self
            .simple_delegate_contract
            .executeDelegate(vec![call])
            .calldata()
            .clone();
        let tx = TransactionRequest::default()
            .with_to(self.alice.address())
            .with_input(execute_calldata);
        let pending_tx = self.evm_provider.send_transaction(tx).await?;
        tracing::info!("Submitted tx: {:?}", pending_tx.tx_hash());
        let receipt = pending_tx.get_receipt().await?;
        tracing::debug!(?receipt, "Transaction receipt received");
        if !receipt.status() {
            return Err(anyhow::anyhow!("Transaction failed: {:?}", receipt));
        }

        // Now do a call to check if the value was set correctly
        let value = self
            .evm_provider
            .get_storage_at(self.alice.address(), U256::from(0))
            .await?;

        anyhow::ensure!(
            value == value_to_set,
            "Value was not set correctly: expected {}, got {}",
            value_to_set,
            value
        );

        // Contract storage should be empty
        let storage = self
            .evm_provider
            .get_storage_at(address, U256::from(0))
            .await?;
        anyhow::ensure!(
            storage == U256::from(0),
            "Storage at contract address is not empty: expected 0, got {}",
            storage
        );

        Ok(())
    }

    #[test_case("Cannot delegate to another runtime")]
    async fn cannot_delegate_to_another_runtime(&self) -> anyhow::Result<()> {
        let contract = match self.deployer {
            Deployer::Evm => &self.delegation_target_eravm,
            Deployer::EraVm => &self.delegation_target_evm,
        };
        let address = *contract.address();

        let call = contracts::evm::SimpleDelegateContract::Call {
            to: address,
            value: Default::default(),
            data: contract.setValue(U256::from(42)).calldata().clone(),
        };
        let execute_calldata = self
            .simple_delegate_contract
            .executeDelegate(vec![call])
            .calldata()
            .clone();
        let tx = TransactionRequest::default()
            .with_to(self.alice.address())
            .with_input(execute_calldata)
            .with_gas_limit(1_000_000);
        let pending_tx = self.evm_provider.send_transaction(tx).await?;
        tracing::info!("Submitted tx: {:?}", pending_tx.tx_hash());
        let receipt = pending_tx.get_receipt().await?;
        tracing::debug!(?receipt, "Transaction receipt received");
        if receipt.status() {
            return Err(anyhow::anyhow!("Transaction succeeded: {:?}", receipt));
        }

        Ok(())
    }

    #[test_case("Delegate to 7702-delegated account")]
    async fn delegate_to_7702(&self) -> anyhow::Result<()> {
        let call = contracts::evm::SimpleDelegateContract::Call {
            to: self.alice.address(),
            value: Default::default(),
            data: self
                .simple_delegate_contract
                .triggerSuccess()
                .calldata()
                .clone(),
        };
        let execute_calldata = self
            .simple_delegate_contract
            .executeDelegate(vec![call])
            .calldata()
            .clone();
        let tx = TransactionRequest::default()
            .with_to(*self.simple_delegate_contract.address())
            .with_input(execute_calldata)
            .with_gas_limit(1_000_000);
        let pending_tx = self.evm_provider.send_transaction(tx).await?;
        tracing::info!("Submitted tx: {:?}", pending_tx.tx_hash());
        let receipt = pending_tx.get_receipt().await?;
        tracing::debug!(?receipt, "Transaction receipt received");
        if !receipt.status() {
            return Err(anyhow::anyhow!("Transaction failed: {:?}", receipt));
        }
        if !receipt.logs().iter().any(|log| {
            log.topics().first().map(|l| &l.as_slice()[..4]) == Some(&[0x39, 0x5a, 0x9a, 0xb3])
        }) {
            return Err(anyhow::anyhow!(
                "Event for `TriggerSuccess` not found in logs"
            ));
        }

        Ok(())
    }

    #[test_case("Delegate to 7702-delegated account (with revert)")]
    async fn delegate_to_7702_with_revert(&self) -> anyhow::Result<()> {
        let call = contracts::evm::SimpleDelegateContract::Call {
            to: self.alice.address(),
            value: Default::default(),
            data: self
                .simple_delegate_contract
                .triggerRevert()
                .calldata()
                .clone(),
        };
        let execute_calldata = self
            .simple_delegate_contract
            .executeDelegate(vec![call])
            .calldata()
            .clone();
        let tx = TransactionRequest::default()
            .with_to(*self.simple_delegate_contract.address())
            .with_input(execute_calldata)
            .with_gas_limit(1_000_000);
        let pending_tx = self.evm_provider.send_transaction(tx).await?;
        tracing::info!("Submitted tx: {:?}", pending_tx.tx_hash());
        let receipt = pending_tx.get_receipt().await?;
        tracing::debug!(?receipt, "Transaction receipt received");
        if receipt.status() {
            return Err(anyhow::anyhow!("Transaction succeeded: {:?}", receipt));
        }

        Ok(())
    }

    #[test_case("Static call to 7702-delegated account")]
    async fn static_call_to_7702(&self) -> anyhow::Result<()> {
        let call = contracts::evm::SimpleDelegateContract::Call {
            to: self.alice.address(),
            value: Default::default(),
            data: self
                .simple_delegate_contract
                .ensureMsgSender(*self.simple_delegate_contract.address())
                .calldata()
                .clone(),
        };
        let execute_calldata = self
            .simple_delegate_contract
            .executeStatic(vec![call])
            .calldata()
            .clone();
        let tx = TransactionRequest::default()
            .with_to(*self.simple_delegate_contract.address())
            .with_input(execute_calldata)
            .with_gas_limit(1_000_000);
        let pending_tx = self.evm_provider.send_transaction(tx).await?;
        tracing::info!("Submitted tx: {:?}", pending_tx.tx_hash());
        let receipt = pending_tx.get_receipt().await?;
        tracing::debug!(?receipt, "Transaction receipt received");
        if !receipt.status() {
            return Err(anyhow::anyhow!("Transaction failed: {:?}", receipt));
        }

        Ok(())
    }

    #[test_case("Static call to 7702-delegated account (should revert)")]
    async fn static_call_to_7702_failure(&self) -> anyhow::Result<()> {
        let call = contracts::evm::SimpleDelegateContract::Call {
            to: self.alice.address(),
            value: Default::default(),
            data: self
                .simple_delegate_contract
                .triggerSuccess()
                .calldata()
                .clone(),
        };
        let execute_calldata = self
            .simple_delegate_contract
            .executeStatic(vec![call])
            .calldata()
            .clone();
        let tx = TransactionRequest::default()
            .with_to(*self.simple_delegate_contract.address())
            .with_input(execute_calldata)
            .with_gas_limit(1_000_000);
        let pending_tx = self.evm_provider.send_transaction(tx).await?;
        tracing::info!("Submitted tx: {:?}", pending_tx.tx_hash());
        let receipt = pending_tx.get_receipt().await?;
        tracing::debug!(?receipt, "Transaction receipt received");
        if receipt.status() {
            return Err(anyhow::anyhow!("Transaction succeeded: {:?}", receipt));
        }

        Ok(())
    }

    #[test_case("Reset authorization")]
    async fn reset_authorization(&self) -> anyhow::Result<()> {
        let auth = Authorization {
            chain_id: U256::from(self.evm_provider.get_chain_id().await?),
            address: Address::default(), // Resetting to default address
            nonce: self
                .evm_provider
                .get_transaction_count(self.alice.address())
                .await?
                + 1, // Should use next nonce
        };
        let signature = self.alice.sign_hash_sync(&auth.signature_hash())?;
        let signed_authorization = auth.into_signed(signature);
        let tx = TransactionRequest::default()
            .with_to(Address::default())
            .with_authorization_list(vec![signed_authorization]);
        let pending_tx = self.evm_provider.send_transaction(tx).await?;
        tracing::info!("Submitted tx: {:?}", pending_tx.tx_hash());
        let receipt = pending_tx.get_receipt().await?;
        tracing::debug!(?receipt, "Transaction receipt received");
        if !receipt.status() {
            return Err(anyhow::anyhow!("Transaction failed: {:?}", receipt));
        }
        let code = self.evm_provider.get_code_at(self.alice.address()).await?;
        anyhow::ensure!(
            code.to_string() == "0x",
            "Code at Alice's address is not empty after reset: {}",
            code.to_string()
        );

        tracing::info!("Authorization reset successfully");
        Ok(())
    }

    /// Check that all the properties in system contracts (e.g. `ContractDeployer::get_delegation_address`)
    /// are reset when authorization is reset.
    #[test_case("Delegation artifacts in system contracts (cleanup)")]
    async fn delegation_artifacts_in_system_contracts_cleanup(&self) -> anyhow::Result<()> {
        let account_code_storage =
            crate::contracts::era_vm::contract_deployer(self.evm_provider.clone());
        let delegation_address = account_code_storage
            .getAccountDelegation(self.alice.address())
            .call()
            .await?
            ._0;
        anyhow::ensure!(
            delegation_address == Address::default(),
            "Delegation address does not match: got {}, expected empty",
            delegation_address
        );

        let account_code_storage =
            crate::contracts::era_vm::account_code_storage(self.evm_provider.clone());
        let versioned_bytecode_hash = account_code_storage
            .getRawCodeHash(self.alice.address())
            .call()
            .await?
            .codeHash;
        anyhow::ensure!(
            versioned_bytecode_hash == [0u8; 32],
            "Versioned bytecode hash does not match expected: got {:?}, expected empty",
            versioned_bytecode_hash,
        );

        let mut expected_bytecode_hash = [0u8; 32];
        expected_bytecode_hash[0..12]
            .copy_from_slice(&hex::decode("020200170000000000EF0100").unwrap());
        expected_bytecode_hash[12..32].copy_from_slice(delegation_address.as_slice());
        let evm_hashes_storage =
            crate::contracts::era_vm::evm_hashes_storage(self.evm_provider.clone());
        let evm_bytecode_hash = evm_hashes_storage
            .getEvmCodeHash(expected_bytecode_hash.into())
            .call()
            .await?
            ._0;
        anyhow::ensure!(
            evm_bytecode_hash == [0u8; 32],
            "EVM bytecode hash does not match expected: got {:?}, expected empty",
            evm_bytecode_hash
        );

        Ok(())
    }

    #[test_case("EVM code properties (after reset)")]
    async fn evm_code_properties_after_reset(&self) -> anyhow::Result<()> {
        // First check with `eth_call`

        let bytecode = self
            .checker
            .getAddressBytecode(self.alice.address())
            .call()
            .await?
            ._0;
        let expected_code = Bytes::default();
        anyhow::ensure!(
            bytecode == expected_code,
            "Bytecode does not match expected: {} != {}",
            bytecode,
            expected_code
        );

        let code_hash = self
            .checker
            .getAddressBytecodeHash(self.alice.address())
            .call()
            .await?
            ._0;
        let expected_hash = keccak256(expected_code.as_ref());
        anyhow::ensure!(
            code_hash == expected_hash,
            "Code hash does not match expected: {:?} != {:?}",
            code_hash,
            expected_hash
        );

        // Now check with submitted transactions.
        let receipt = self
            .checker
            .assertAddressBytecode(self.alice.address(), expected_code.clone())
            .send()
            .await?
            .get_receipt()
            .await?;
        anyhow::ensure!(receipt.status(), "Transaction failed: {:?}", receipt);
        let receipt = self
            .checker
            .assertAddressBytecodeHash(self.alice.address(), expected_hash)
            .send()
            .await?
            .get_receipt()
            .await?;
        anyhow::ensure!(receipt.status(), "Transaction failed: {:?}", receipt);

        Ok(())
    }

    #[test_case("Set authorization in a reverting transaction")]
    async fn set_authorization_in_a_reverting_tx(&self) -> anyhow::Result<()> {
        let delegation_address = Address::repeat_byte(0x3f);

        let auth_list_nonce = self
            .evm_provider
            .get_transaction_count(self.alice.address())
            .await?
            + 1; // Should use next nonce
        let auth = Authorization {
            chain_id: U256::from(self.evm_provider.get_chain_id().await?),
            address: delegation_address,
            nonce: auth_list_nonce,
        };
        let signature = self.alice.sign_hash_sync(&auth.signature_hash())?;
        let signed_authorization = auth.into_signed(signature);

        // Transaction should revert, but authorization should be set.
        let tx = TransactionRequest::default()
            .with_to(*self.simple_delegate_contract.address())
            .with_authorization_list(vec![signed_authorization])
            .with_input(
                self.simple_delegate_contract
                    .triggerRevert()
                    .calldata()
                    .clone(),
            )
            .with_gas_limit(1_000_000);
        let pending_tx = self.evm_provider.send_transaction(tx).await?;
        tracing::info!("Submitted tx: {:?}", pending_tx.tx_hash());
        let receipt = pending_tx.get_receipt().await?;
        if receipt.status() {
            return Err(anyhow::anyhow!("Transaction suceeded: {:?}", receipt));
        }

        let account_code_storage =
            crate::contracts::era_vm::contract_deployer(self.evm_provider.clone());
        let actual_delegation_address = account_code_storage
            .getAccountDelegation(self.alice.address())
            .call()
            .await?
            ._0;
        anyhow::ensure!(
            actual_delegation_address == delegation_address,
            "Delegation address does not match: got {}, expected {}",
            actual_delegation_address,
            delegation_address
        );

        let actual_nonce = self
            .evm_provider
            .get_transaction_count(self.alice.address())
            .await?;
        anyhow::ensure!(
            actual_nonce == auth_list_nonce + 1,
            "Authorization list nonce was not incremented, expected {auth_list_nonce}, got {actual_nonce}, addr: {}",
            self.alice.address()
        );

        Ok(())
    }

    #[test_case("Delegation cycle")]
    async fn delegation_cycle(&self) -> anyhow::Result<()> {
        let bob = PrivateKeySigner::random();
        let charlie = PrivateKeySigner::random();

        let bob_authorization = Authorization {
            chain_id: U256::from(self.evm_provider.get_chain_id().await?),
            address: charlie.address(),
            nonce: 0,
        };
        let bob_signature = bob.sign_hash_sync(&bob_authorization.signature_hash())?;
        let charlie_authorization = Authorization {
            chain_id: U256::from(self.evm_provider.get_chain_id().await?),
            address: bob.address(),
            nonce: 0,
        };
        let charlie_signature = charlie.sign_hash_sync(&charlie_authorization.signature_hash())?;

        let tx = TransactionRequest::default()
            .with_to(Address::default())
            .with_authorization_list(vec![
                bob_authorization.into_signed(bob_signature),
                charlie_authorization.into_signed(charlie_signature),
            ]);
        let pending_tx = self.evm_provider.send_transaction(tx).await?;
        tracing::info!("Submitted tx: {:?}", pending_tx.tx_hash());
        let receipt = pending_tx.get_receipt().await?;
        if !receipt.status() {
            return Err(anyhow::anyhow!("Transaction failed: {:?}", receipt));
        }

        let invoke_bob_tx = TransactionRequest::default()
            .with_to(bob.address())
            .with_gas_limit(1_000_000);
        let invoke_charlie_tx = TransactionRequest::default()
            .with_to(charlie.address())
            .with_gas_limit(1_000_000);

        let bob_pending_tx = self.evm_provider.send_transaction(invoke_bob_tx).await?;
        tracing::info!("Submitted Bob's tx: {:?}", bob_pending_tx.tx_hash());
        let bob_receipt = bob_pending_tx.get_receipt().await?;
        if bob_receipt.status() {
            return Err(anyhow::anyhow!(
                "Bob's transaction succeeded: {:?}",
                bob_receipt
            ));
        }

        let charlie_pending_tx = self
            .evm_provider
            .send_transaction(invoke_charlie_tx)
            .await?;
        tracing::info!("Submitted Charlie's tx: {:?}", charlie_pending_tx.tx_hash());
        let charlie_receipt = charlie_pending_tx.get_receipt().await?;
        tracing::debug!(?charlie_receipt, "Charlie's transaction receipt received");
        if charlie_receipt.status() {
            return Err(anyhow::anyhow!(
                "Charlie's transaction succeeded: {:?}",
                charlie_receipt
            ));
        }

        Ok(())
    }

    #[test_case("Empty authorization list not allowed")]
    async fn empty_authorization_list_not_allowed(&self) -> anyhow::Result<()> {
        let tx = TransactionRequest::default()
            .with_to(Address::repeat_byte(0x88))
            .with_authorization_list(Vec::new());
        let Err(error) = self.evm_provider.estimate_gas(tx).await else {
            anyhow::bail!("Gas estimation should have failed");
        };
        let RpcError::ErrorResp(error) = error else {
            anyhow::bail!("Expected RpcError::ErrorResp, got: {:?}", error);
        };

        anyhow::ensure!(
            error
                .message
                .contains("Failed to process EIP-7702 authorization list"),
            "Expected revert reason, got: {}",
            error.message,
        );

        Ok(())
    }

    #[test_case("Authorization lists are preserved if tx runs out of gas")]
    async fn auth_lists_preserved_on_out_of_gas(&self) -> anyhow::Result<()> {
        let bob = PrivateKeySigner::random();
        let charlie = PrivateKeySigner::random();
        let bob_authorization = Authorization {
            chain_id: U256::from(self.evm_provider.get_chain_id().await?),
            address: charlie.address(),
            nonce: 0,
        };
        let bob_signature = bob.sign_hash_sync(&bob_authorization.signature_hash())?;

        let tx = TransactionRequest::default()
            .with_to(*self.checker.address())
            .with_input(self.checker.spendAllGas().calldata().clone())
            .with_authorization_list(vec![bob_authorization.into_signed(bob_signature)])
            .with_gas_limit(2_000_000); // Transaction can't be estimated.
        let pending_tx = self.evm_provider.send_transaction(tx).await?;
        tracing::info!("Submitted tx: {:?}", pending_tx.tx_hash());
        let receipt = pending_tx.get_receipt().await?;
        if receipt.status() {
            return Err(anyhow::anyhow!(
                "Transaction succeeded (should've spent all gas): {:?}",
                receipt
            ));
        }

        let account_code_storage =
            crate::contracts::era_vm::contract_deployer(self.evm_provider.clone());
        let actual_delegation_address = account_code_storage
            .getAccountDelegation(bob.address())
            .call()
            .await?
            ._0;

        anyhow::ensure!(
            actual_delegation_address == charlie.address(),
            "Delegation address does not match: got {}, expected {}",
            actual_delegation_address,
            charlie.address()
        );
        let actual_nonce = self
            .evm_provider
            .get_transaction_count(bob.address())
            .await?;
        anyhow::ensure!(
            actual_nonce == 1,
            "Authorization list nonce was not incremented, expected 1, got {actual_nonce}, addr: {}",
            bob.address()
        );

        Ok(())
    }

    #[test_case("Delegate to precompile")]
    async fn delegate_to_precompile(&self) -> anyhow::Result<()> {
        let precompile_address = address!("0x0000000000000000000000000000000000000001");
        let bob = PrivateKeySigner::random();
        let bob_authorization = Authorization {
            chain_id: U256::from(self.evm_provider.get_chain_id().await?),
            address: precompile_address,
            nonce: 0,
        };
        let bob_signature = bob.sign_hash_sync(&bob_authorization.signature_hash())?;
        let tx = TransactionRequest::default()
            .with_to(Default::default())
            .with_authorization_list(vec![bob_authorization.into_signed(bob_signature)]);
        let pending_tx = self.evm_provider.send_transaction(tx).await?;
        tracing::info!("Submitted tx: {:?}", pending_tx.tx_hash());
        let receipt = pending_tx.get_receipt().await?;
        tracing::debug!(?receipt, "Transaction receipt received");
        if !receipt.status() {
            return Err(anyhow::anyhow!("Transaction failed: {:?}", receipt));
        }

        let call_precompile = TransactionRequest::default().with_to(bob.address());
        let pending_tx = self.evm_provider.send_transaction(call_precompile).await?;
        tracing::info!("Submitted precompile call tx: {:?}", pending_tx.tx_hash());
        let receipt = pending_tx.get_receipt().await?;
        tracing::debug!(?receipt, "Precompile call receipt received");
        if !receipt.status() {
            return Err(anyhow::anyhow!("Precompile call failed: {:?}", receipt));
        }
        Ok(())
    }
}
