use crate::{
    assertions::{AssertingProvider as _, DelegatingProvider as _, Token, TxAssertion},
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
    eips::eip7702::SignedAuthorization,
    network::{Ethereum, TransactionBuilder, TransactionBuilder7702},
    primitives::{Address, Bytes, U256, address, keccak256},
    providers::{DynProvider, Provider},
    rpc::types::TransactionRequest,
    signers::{Signer, local::PrivateKeySigner},
    transports::RpcError,
};

use anyhow::Context as _;
use e2e::test_suite;

use super::TestConfig;

#[derive(Debug, Clone)]
pub(crate) struct Test7702 {
    deployer: Deployer,
    alice: PrivateKeySigner,
    evm_provider: DynProvider<Ethereum>,
    erc20: Erc20Instance<(), DynProvider<Ethereum>>,
    simple_delegate_contract: SimpleDelegateContractInstance<(), DynProvider<Ethereum>>,
    delegation_target_evm: DelegationTargetInstance<(), DynProvider<Ethereum>>,
    delegation_target_eravm: DelegationTargetInstance<(), DynProvider<Ethereum>>,
    checker: Evm7702CheckerInstance<(), DynProvider<Ethereum>>,
}

#[test_suite("EIP7702 tests")]
impl Test7702 {
    #[constructor("EVM")]
    async fn evm(config: &TestConfig) -> anyhow::Result<Self> {
        Self::new_inner(config, Deployer::Evm).await
    }

    #[constructor("EraVM")]
    async fn eravm(config: &TestConfig) -> anyhow::Result<Self> {
        Self::new_inner(config, Deployer::EraVm).await
    }

    async fn new_inner(config: &TestConfig, deployer: Deployer) -> anyhow::Result<Self> {
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
            .await
            .context("Can't deploy ERC20")?;

        evm_provider
            .send_with_assertions(
                erc20
                    .mint(U256::from(1000000), alice.address())
                    .into_transaction_request(),
                [TxAssertion::should_succeed()],
            )
            .await?;

        let simple_delegate_contract = deployer
            .deploy_simple_delegate_contract(alice.clone(), &config.rpc_url)
            .await
            .context("Can't deploy simple delegate contract")?;

        let delegation_target_evm = Deployer::Evm
            .deploy_delegation_target(alice.clone(), &config.rpc_url)
            .await
            .context("Can't deploy simple delegate target (EVM)")?;
        let delegation_target_eravm = Deployer::EraVm
            .deploy_delegation_target(alice.clone(), &config.rpc_url)
            .await
            .context("Can't deploy simple delegate target (EraVM)")?;

        let checker = contracts::evm::Evm7702Checker::deploy(evm_provider.clone())
            .await
            .context("Can't deploy Evm7702Checker")?;

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

        let auth = self
            .evm_provider
            .sign_authorization(1, &self.alice, *self.simple_delegate_contract.address())
            .await?;
        let tx = TransactionRequest::default()
            .with_to(Address::default())
            .with_authorization_list(vec![auth]);

        self.evm_provider
            .send_with_assertions(
                tx,
                [
                    TxAssertion::should_succeed(),
                    // Has to be incremented by 2: 1 for tx, 1 for authorization
                    TxAssertion::should_increment_nonce(self.alice.address(), 2),
                ],
            )
            .await?;
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
            .copy_from_slice(&hex::decode("030200170000000000EF0100").unwrap());
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
        let tx = self
            .simple_delegate_contract
            .ensureMsgSender(self.alice.address())
            .into_transaction_request()
            .with_to(self.alice.address());
        self.evm_provider
            .send_with_assertions(tx, [TxAssertion::should_succeed()])
            .await?;
        Ok(())
    }

    #[test_case("Send operation")]
    async fn send_operation(&self) -> anyhow::Result<()> {
        tracing::info!("Sending operation...");

        let bob = Address::repeat_byte(0x5c);
        let value_to_send = U256::from(1000);
        let call = contracts::evm::SimpleDelegateContract::Call {
            to: bob,
            value: value_to_send,
            data: Default::default(),
        };
        let tx = self
            .simple_delegate_contract
            .execute(vec![call])
            .into_transaction_request()
            .with_to(self.alice.address())
            .with_value(value_to_send);
        self.evm_provider
            .send_with_assertions(
                tx,
                [
                    TxAssertion::should_succeed(),
                    TxAssertion::should_change_balance(bob, Token::Base, "1000".parse().unwrap()),
                ],
            )
            .await?;

        Ok(())
    }

    #[test_case("Fail transaction with revert")]
    async fn revert_processed(&self) -> anyhow::Result<()> {
        let tx = self
            .simple_delegate_contract
            .triggerRevert()
            .into_transaction_request()
            .with_to(self.alice.address())
            .with_gas_limit(1_000_000);
        self.evm_provider
            .send_with_assertions(tx, [TxAssertion::should_revert()])
            .await?;

        Ok(())
    }

    #[test_case("Revert reason in eth_call")]
    async fn revert_reason_in_eth_call(&self) -> anyhow::Result<()> {
        let tx = self
            .simple_delegate_contract
            .triggerRevert()
            .into_transaction_request()
            .with_to(self.alice.address())
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

        self.evm_provider
            .send_with_assertions(
                self.erc20
                    .transfer(bob, U256::from(500))
                    .into_transaction_request(),
                [
                    TxAssertion::should_succeed(),
                    TxAssertion::should_change_balance(
                        bob,
                        Token::Erc20(*self.erc20.address()),
                        "500".parse().unwrap(),
                    ),
                ],
            )
            .await?;

        Ok(())
    }

    #[test_case("Can still use as an EOA (with value)")]
    async fn use_eoa_with_value(&self) -> anyhow::Result<()> {
        let bob = Address::repeat_byte(0x5d);

        let tx = TransactionRequest::default()
            .with_to(bob)
            .with_value(U256::from(500));
        self.evm_provider
            .send_with_assertions(
                tx,
                [
                    TxAssertion::should_succeed(),
                    TxAssertion::should_change_balance(bob, Token::Base, "500".parse().unwrap()),
                ],
            )
            .await?;

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
        let tx = self
            .simple_delegate_contract
            .executeDelegate(vec![call])
            .into_transaction_request()
            .with_to(self.alice.address());
        self.evm_provider
            .send_with_assertions(
                tx,
                [
                    TxAssertion::should_succeed(),
                    TxAssertion::should_change_storage(
                        self.alice.address(),
                        U256::from(0),
                        value_to_set,
                    ),
                    TxAssertion::should_change_storage(address, U256::from(0), U256::from(0)),
                ],
            )
            .await?;

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
        let tx = self
            .simple_delegate_contract
            .executeDelegate(vec![call])
            .into_transaction_request()
            .with_to(self.alice.address())
            .with_gas_limit(1_000_000);
        self.evm_provider
            .send_with_assertions(tx, [TxAssertion::should_revert()])
            .await?;

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
        let tx = self
            .simple_delegate_contract
            .executeDelegate(vec![call])
            .into_transaction_request()
            .with_to(*self.simple_delegate_contract.address())
            .with_gas_limit(1_000_000);
        self.evm_provider
            .send_with_assertions(
                tx,
                [
                    TxAssertion::should_succeed(),
                    TxAssertion::should_emit_log(|log| {
                        // Signature for `TriggerSuccess` event.
                        log.topics().first().map(|l| &l.as_slice()[..4])
                            == Some(&[0x39, 0x5a, 0x9a, 0xb3])
                    }),
                ],
            )
            .await?;

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
        let tx = self
            .simple_delegate_contract
            .executeDelegate(vec![call])
            .into_transaction_request()
            .with_to(*self.simple_delegate_contract.address())
            .with_gas_limit(1_000_000);
        self.evm_provider
            .send_with_assertions(tx, [TxAssertion::should_revert()])
            .await?;

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
        let tx = self
            .simple_delegate_contract
            .executeStatic(vec![call])
            .into_transaction_request()
            .with_to(*self.simple_delegate_contract.address())
            .with_gas_limit(1_000_000);
        self.evm_provider
            .send_with_assertions(tx, [TxAssertion::should_succeed()])
            .await?;

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
        let tx = self
            .simple_delegate_contract
            .executeStatic(vec![call])
            .into_transaction_request()
            .with_to(*self.simple_delegate_contract.address())
            .with_gas_limit(1_000_000);
        self.evm_provider
            .send_with_assertions(tx, [TxAssertion::should_revert()])
            .await?;

        Ok(())
    }

    #[test_case("Reset authorization")]
    async fn reset_authorization(&self) -> anyhow::Result<()> {
        // Resetting to default address
        let auth = self
            .evm_provider
            .sign_authorization(1, &self.alice, Address::default())
            .await?;
        let tx = TransactionRequest::default()
            .with_to(Address::default())
            .with_authorization_list(vec![auth]);
        self.evm_provider
            .send_with_assertions(tx, [TxAssertion::should_succeed()])
            .await?;

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

        let auth = self
            .evm_provider
            .sign_authorization(1, &self.alice, delegation_address)
            .await?;
        let auth_list_nonce = auth.inner().nonce;

        // Transaction should revert, but authorization should be set.
        let tx = TransactionRequest::default()
            .with_to(*self.simple_delegate_contract.address())
            .with_authorization_list(vec![auth])
            .with_input(
                self.simple_delegate_contract
                    .triggerRevert()
                    .calldata()
                    .clone(),
            )
            .with_gas_limit(1_000_000);
        self.evm_provider
            .send_with_assertions(tx, [TxAssertion::should_revert()])
            .await?;

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

        let bob_auth = self
            .evm_provider
            .sign_authorization(0, &bob, charlie.address())
            .await?;
        let charlie_auth = self
            .evm_provider
            .sign_authorization(0, &charlie, bob.address())
            .await?;

        let tx = TransactionRequest::default()
            .with_to(Address::default())
            .with_authorization_list(vec![bob_auth, charlie_auth]);
        self.evm_provider
            .send_with_assertions(tx, [TxAssertion::should_succeed()])
            .await?;

        let invoke_bob_tx = TransactionRequest::default()
            .with_to(bob.address())
            .with_gas_limit(1_000_000);
        self.evm_provider
            .send_with_assertions(invoke_bob_tx, [TxAssertion::should_revert()])
            .await?;

        let invoke_charlie_tx = TransactionRequest::default()
            .with_to(charlie.address())
            .with_gas_limit(1_000_000);
        self.evm_provider
            .send_with_assertions(invoke_charlie_tx, [TxAssertion::should_revert()])
            .await?;

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
        let bob_auth = self
            .evm_provider
            .sign_authorization(0, &bob, charlie.address())
            .await?;

        let tx = TransactionRequest::default()
            .with_to(*self.checker.address())
            .with_input(self.checker.spendAllGas().calldata().clone())
            .with_authorization_list(vec![bob_auth])
            .with_gas_limit(2_000_000); // Transaction can't be estimated.
        self.evm_provider
            .send_with_assertions(tx, [TxAssertion::should_revert()])
            .await?;

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
        let bob_auth = self
            .evm_provider
            .sign_authorization(0, &bob, precompile_address)
            .await?;

        let tx = TransactionRequest::default()
            .with_to(Default::default())
            .with_authorization_list(vec![bob_auth]);
        self.evm_provider
            .send_with_assertions(tx, [TxAssertion::should_succeed()])
            .await?;

        let call_precompile = TransactionRequest::default().with_to(bob.address());
        self.evm_provider
            .send_with_assertions(call_precompile, [TxAssertion::should_succeed()])
            .await?;
        Ok(())
    }

    #[test_case("Set multiple authorizations, ignore invalid")]
    async fn set_multiple_authorizations(&self) -> anyhow::Result<()> {
        let bob = PrivateKeySigner::random();
        let carl = PrivateKeySigner::random();
        let daisy = PrivateKeySigner::random();

        let auth_bob = self
            .evm_provider
            .sign_authorization(0, &bob, Address::repeat_byte(0x11))
            .await?;
        let auth_carl = self
            .evm_provider
            .sign_authorization(0, &carl, Address::repeat_byte(0x11))
            .await?;
        let auth_invalid = {
            let auth = self
                .evm_provider
                .sign_authorization(0, &daisy, Address::repeat_byte(0x11))
                .await?;
            // Authorization tuple with invalid signature
            SignedAuthorization::new_unchecked(
                auth.strip_signature(),
                0,
                U256::from(123),
                U256::from(456),
            )
        };

        let tx = TransactionRequest::default()
            .with_to(Address::default())
            .with_authorization_list(vec![auth_bob, auth_carl, auth_invalid]);

        self.evm_provider
            .send_with_assertions(
                tx,
                [
                    TxAssertion::should_succeed(),
                    TxAssertion::should_increment_nonce(self.alice.address(), 1),
                    TxAssertion::should_increment_nonce(bob.address(), 1),
                    TxAssertion::should_increment_nonce(carl.address(), 1),
                    TxAssertion::should_not_increment_nonce(daisy.address()),
                ],
            )
            .await?;
        Ok(())
    }

    #[test_case("Handle multiple tuples for the same authority")]
    async fn many_same_account_authorizations(&self) -> anyhow::Result<()> {
        // From EIP: When multiple tuples from the same authority are present,
        // set the code using the address in the last valid occurrence.

        let bob = PrivateKeySigner::random();
        let first_auth = self
            .evm_provider
            .sign_authorization(0, &bob, Address::repeat_byte(0x11))
            .await?;
        let second_auth = self
            .evm_provider
            .sign_authorization(1, &bob, Address::repeat_byte(0x22))
            .await?;
        // This auth should be skipped, because it uses the wrong nonce
        let skipped_auth = self
            .evm_provider
            .sign_authorization(3, &bob, Address::repeat_byte(0x33))
            .await?;
        let tx = TransactionRequest::default()
            .with_to(Address::default())
            .with_authorization_list(vec![first_auth, second_auth, skipped_auth]);
        self.evm_provider
            .send_with_assertions(
                tx,
                [
                    TxAssertion::should_succeed(),
                    // Nonce has to be incremented twice, for the first 2 tuples
                    TxAssertion::should_increment_nonce(bob.address(), 2),
                ],
            )
            .await?;

        // Check that the second auth tuple got accepted by checking code
        let code = self.evm_provider.get_code_at(bob.address()).await?;
        let expected_code = format!("0xef0100{:x}", Address::repeat_byte(0x22));
        anyhow::ensure!(
            code.to_string() == expected_code,
            "Code does not match expected: {} != {}",
            code.to_string(),
            expected_code
        );

        Ok(())
    }
}
