pub(crate) mod era_vm {
    use IAccountCodeStorage::IAccountCodeStorageInstance;
    use IContractDeployer::IContractDeployerInstance;
    use IEvmHashesStorage::IEvmHashesStorageInstance;

    alloy::sol!(
        #[sol(rpc)]
        #[derive(Debug)]
        Erc20,
        "contracts/zkout/SimpleDelegateContract.sol/ERC20.json"
    );

    alloy::sol!(
        #[sol(rpc)]
        #[derive(Debug)]
        SimpleDelegateContract,
        "contracts/zkout/SimpleDelegateContract.sol/SimpleDelegateContract.json"
    );

    alloy::sol!(
        #[sol(rpc)]
        #[derive(Debug)]
        DelegationTarget,
        "contracts/zkout/SimpleDelegateContract.sol/DelegationTarget.json"
    );

    alloy::sol!(
        #[sol(rpc)]
        #[derive(Debug)]
        interface IAccountCodeStorage {
            function getRawCodeHash(address _address) external view returns (bytes32 codeHash);
        }
    );

    pub fn account_code_storage(
        provider: alloy::providers::DynProvider,
    ) -> IAccountCodeStorageInstance<(), alloy::providers::DynProvider> {
        let address = "0x0000000000000000000000000000000000008002"
            .parse()
            .unwrap();
        IAccountCodeStorageInstance::new(address, provider)
    }

    alloy::sol!(
        #[sol(rpc)]
        #[derive(Debug)]
        interface IContractDeployer {
            function getAccountDelegation(address _addr) external view returns (address);
        }
    );

    pub fn contract_deployer(
        provider: alloy::providers::DynProvider,
    ) -> IContractDeployerInstance<(), alloy::providers::DynProvider> {
        let address = "0x0000000000000000000000000000000000008006"
            .parse()
            .unwrap();
        IContractDeployerInstance::new(address, provider)
    }

    alloy::sol!(
        #[sol(rpc)]
        #[derive(Debug)]
        interface IEvmHashesStorage {
            function getEvmCodeHash(bytes32 versionedBytecodeHash) external view returns (bytes32);
        }
    );

    pub fn evm_hashes_storage(
        provider: alloy::providers::DynProvider,
    ) -> IEvmHashesStorageInstance<(), alloy::providers::DynProvider> {
        let address = "0x0000000000000000000000000000000000008015"
            .parse()
            .unwrap();
        IEvmHashesStorageInstance::new(address, provider)
    }
}

pub(crate) mod evm {
    alloy::sol!(
        #[sol(rpc)]
        #[derive(Debug)]
        Erc20,
        "contracts/out/SimpleDelegateContract.sol/ERC20.json"
    );

    alloy::sol!(
        #[sol(rpc)]
        #[derive(Debug)]
        SimpleDelegateContract,
        "contracts/out/SimpleDelegateContract.sol/SimpleDelegateContract.json"
    );

    alloy::sol!(
        #[sol(rpc)]
        #[derive(Debug)]
        DelegationTarget,
        "contracts/out/SimpleDelegateContract.sol/DelegationTarget.json"
    );

    alloy::sol!(
        #[sol(rpc)]
        #[derive(Debug)]
        Evm7702Checker,
        "contracts/out/Evm7702Checker.sol/Evm7702Checker.json"
    );
}
