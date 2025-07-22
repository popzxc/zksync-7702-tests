pub(crate) mod basic_evm;

const DEFAULT_URL_L1: &str = "http://127.0.0.1:8545";
const DEFAULT_URL_L2: &str = "http://127.0.0.1:3050";
const DEFAULT_PK_ANVIL: &str = "0x8b3a350cf5c34c9194ca85829a2df0ec3153be0318b5e2d3348e872092edffba";
const DEFAULT_PK_MAIN: &str = "0x850683b40d4a740aa6e745f889a6fdc8327be76e122f5aba645a5b02d0248db8";

#[derive(Debug, Clone, Copy, clap::ValueEnum)]
pub enum Profile {
    Anvil,
    MainNode,
}

#[derive(Debug, Clone, clap::Args)]
#[group(id = "test arguments")]
pub struct TestConfig {
    #[clap(long, default_value = "Profile::Anvil")]
    profile: Profile,
    #[clap(long)]
    main_pk: Option<String>,
    #[clap(long)]
    l2_url: Option<String>,
    #[clap(long)]
    l1_url: Option<String>,
}

impl TestConfig {
    pub fn l2_url(&self) -> &str {
        self.l2_url.as_deref().unwrap_or(match self.profile {
            Profile::Anvil => DEFAULT_URL_L1, // Anvil uses L1 port by default
            Profile::MainNode => DEFAULT_URL_L2,
        })
    }

    pub fn l1_url(&self) -> &str {
        self.l1_url.as_deref().unwrap_or(match self.profile {
            Profile::Anvil => DEFAULT_URL_L1,
            Profile::MainNode => DEFAULT_URL_L1,
        })
    }

    pub fn main_pk(&self) -> &str {
        self.main_pk.as_deref().unwrap_or(match self.profile {
            Profile::Anvil => DEFAULT_PK_ANVIL,
            Profile::MainNode => DEFAULT_PK_MAIN,
        })
    }

    pub fn profile(&self) -> Profile {
        self.profile
    }
}
