use crate::contracts::{
    self,
    evm::{
        DelegationTarget::DelegationTargetInstance, Erc20::Erc20Instance,
        SimpleDelegateContract::SimpleDelegateContractInstance,
    },
};
use alloy::{
    network::{Ethereum, ReceiptResponse},
    providers::{DynProvider, Provider},
    signers::local::PrivateKeySigner,
};

#[derive(Debug, Clone, Copy)]
pub(crate) enum Deployer {
    Evm,
    EraVm,
}

impl Deployer {
    pub fn opposite(self) -> Self {
        match self {
            Deployer::Evm => Deployer::EraVm,
            Deployer::EraVm => Deployer::Evm,
        }
    }

    pub async fn deploy_erc20(
        self,
        pk: PrivateKeySigner,
        node_url: &str,
    ) -> anyhow::Result<Erc20Instance<(), DynProvider<Ethereum>>> {
        match self {
            Deployer::Evm => deploy_erc20_evm(pk, node_url).await,
            Deployer::EraVm => deploy_erc20_eravm(pk, node_url).await,
        }
    }

    pub async fn deploy_simple_delegate_contract(
        self,
        pk: PrivateKeySigner,
        node_url: &str,
    ) -> anyhow::Result<SimpleDelegateContractInstance<(), DynProvider<Ethereum>>> {
        match self {
            Deployer::Evm => deploy_simple_delegate_contract_evm(pk, node_url).await,
            Deployer::EraVm => deploy_simple_delegate_contract_eravm(pk, node_url).await,
        }
    }

    pub async fn deploy_delegation_target(
        self,
        pk: PrivateKeySigner,
        node_url: &str,
    ) -> anyhow::Result<DelegationTargetInstance<(), DynProvider<Ethereum>>> {
        match self {
            Deployer::Evm => deploy_delegation_target_evm(pk, node_url).await,
            Deployer::EraVm => deploy_delegation_target_eravm(pk, node_url).await,
        }
    }
}

async fn deploy_erc20_evm(
    pk: PrivateKeySigner,
    node_url: &str,
) -> anyhow::Result<Erc20Instance<(), DynProvider<Ethereum>>> {
    let evm_provider = alloy::providers::builder::<Ethereum>()
        .with_recommended_fillers()
        .wallet(pk.clone())
        .on_http(node_url.parse().unwrap())
        .erased();

    let erc20 = contracts::evm::Erc20::deploy(&evm_provider, pk.address())
        .await?
        .with_cloned_provider();
    tracing::info!("Deployed ERC20 contract at: {:?}", erc20.address());

    Ok(erc20)
}

async fn deploy_erc20_eravm(
    pk: PrivateKeySigner,
    node_url: &str,
) -> anyhow::Result<Erc20Instance<(), DynProvider<Ethereum>>> {
    let evm_provider = alloy::providers::builder::<Ethereum>()
        .with_recommended_fillers()
        .wallet(pk.clone())
        .on_http(node_url.parse().unwrap())
        .erased();

    let zksync_wallet = alloy_zksync::wallet::ZksyncWallet::new(pk.clone());
    let zksync_provider = alloy_zksync::provider::zksync_provider()
        .with_recommended_fillers()
        .wallet(zksync_wallet)
        .on_http(node_url.parse().unwrap())
        .erased();

    let erc20_bytecode = contracts::era_vm::Erc20::BYTECODE.clone();
    let constructor_params = contracts::era_vm::Erc20::constructorCall {
        _minter: pk.address(),
    };
    let constructor_data = alloy::sol_types::SolConstructor::abi_encode(&constructor_params);
    let erc20_deployment_tx =
        alloy_zksync::network::transaction_request::TransactionRequest::default()
            .with_create_params(erc20_bytecode.into(), constructor_data, Vec::default())
            .unwrap();
    let erc20_tx = zksync_provider
        .send_transaction(erc20_deployment_tx)
        .await?
        .get_receipt()
        .await?;

    let erc20 = contracts::evm::Erc20::new(
        erc20_tx.contract_address().expect("No contract deployed"),
        evm_provider.clone(),
    );
    tracing::info!("Deployed ERC20 contract at: {:?}", erc20.address());

    Ok(erc20)
}

async fn deploy_simple_delegate_contract_evm(
    pk: PrivateKeySigner,
    node_url: &str,
) -> anyhow::Result<SimpleDelegateContractInstance<(), DynProvider<Ethereum>>> {
    let evm_provider = alloy::providers::builder::<Ethereum>()
        .with_recommended_fillers()
        .wallet(pk.clone())
        .on_http(node_url.parse().unwrap())
        .erased();

    let simple_delegate_contract = contracts::evm::SimpleDelegateContract::deploy(&evm_provider)
        .await?
        .with_cloned_provider();
    tracing::info!(
        "Deployed SimpleDelegate contract at: {:?}",
        simple_delegate_contract.address()
    );

    Ok(simple_delegate_contract)
}

async fn deploy_simple_delegate_contract_eravm(
    pk: PrivateKeySigner,
    node_url: &str,
) -> anyhow::Result<SimpleDelegateContractInstance<(), DynProvider<Ethereum>>> {
    let evm_provider = alloy::providers::builder::<Ethereum>()
        .with_recommended_fillers()
        .wallet(pk.clone())
        .on_http(node_url.parse().unwrap())
        .erased();

    let zksync_wallet = alloy_zksync::wallet::ZksyncWallet::new(pk.clone());
    let zksync_provider = alloy_zksync::provider::zksync_provider()
        .with_recommended_fillers()
        .wallet(zksync_wallet)
        .on_http(node_url.parse().unwrap())
        .erased();

    let simple_delegate_contract_bytecode =
        contracts::era_vm::SimpleDelegateContract::BYTECODE.clone();
    let simple_delegate_contract_deployment_tx =
        alloy_zksync::network::transaction_request::TransactionRequest::default()
            .with_create_params(
                simple_delegate_contract_bytecode.into(),
                Vec::new(),
                Vec::default(),
            )
            .unwrap();
    let simple_delegate_contract_tx = zksync_provider
        .send_transaction(simple_delegate_contract_deployment_tx)
        .await?
        .get_receipt()
        .await?;

    let simple_delegate_contract = contracts::evm::SimpleDelegateContract::new(
        simple_delegate_contract_tx
            .contract_address()
            .expect("No contract deployed"),
        evm_provider,
    );
    tracing::info!(
        "Deployed SimpleDelegate contract at: {:?}",
        simple_delegate_contract.address()
    );

    Ok(simple_delegate_contract)
}

async fn deploy_delegation_target_evm(
    pk: PrivateKeySigner,
    node_url: &str,
) -> anyhow::Result<DelegationTargetInstance<(), DynProvider<Ethereum>>> {
    let evm_provider = alloy::providers::builder::<Ethereum>()
        .with_recommended_fillers()
        .wallet(pk.clone())
        .on_http(node_url.parse().unwrap())
        .erased();

    let delegation_target = contracts::evm::DelegationTarget::deploy(&evm_provider)
        .await?
        .with_cloned_provider();
    tracing::info!(
        "Deployed DelegationTarget contract at: {:?}",
        delegation_target.address()
    );

    Ok(delegation_target)
}

async fn deploy_delegation_target_eravm(
    pk: PrivateKeySigner,
    node_url: &str,
) -> anyhow::Result<DelegationTargetInstance<(), DynProvider<Ethereum>>> {
    let evm_provider = alloy::providers::builder::<Ethereum>()
        .with_recommended_fillers()
        .wallet(pk.clone())
        .on_http(node_url.parse().unwrap())
        .erased();

    let zksync_wallet = alloy_zksync::wallet::ZksyncWallet::new(pk.clone());
    let zksync_provider = alloy_zksync::provider::zksync_provider()
        .with_recommended_fillers()
        .wallet(zksync_wallet)
        .on_http(node_url.parse().unwrap())
        .erased();

    let delegation_target_bytecode = contracts::era_vm::DelegationTarget::BYTECODE.clone();
    let delegation_target_deployment_tx =
        alloy_zksync::network::transaction_request::TransactionRequest::default()
            .with_create_params(
                delegation_target_bytecode.into(),
                Vec::new(),
                Vec::default(),
            )
            .unwrap();
    let delegation_target_tx = zksync_provider
        .send_transaction(delegation_target_deployment_tx)
        .await?
        .get_receipt()
        .await?;

    let delegation_target = contracts::evm::DelegationTarget::new(
        delegation_target_tx
            .contract_address()
            .expect("No contract deployed"),
        evm_provider,
    );
    tracing::info!(
        "Deployed DelegationTarget contract at: {:?}",
        delegation_target.address()
    );

    Ok(delegation_target)
}
