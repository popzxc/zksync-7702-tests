pub(crate) mod basic_evm;

const DEFAULT_URL: &str = "http://127.0.0.1:8545";
const DEFAULT_PK: &str = "0x8b3a350cf5c34c9194ca85829a2df0ec3153be0318b5e2d3348e872092edffba";

#[derive(Debug, Clone, clap::Args)]
#[group(id = "test arguments")]
pub struct TestConfig {
    #[clap(default_value = DEFAULT_PK, long)]
    main_pk: String,
    #[clap(default_value = DEFAULT_URL, long)]
    l2_url: String,
    #[clap(long)]
    l1_url: Option<String>,
}
