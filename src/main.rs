use crate::suites::TestConfig;
use tracing_subscriber::{layer::SubscriberExt as _, util::SubscriberInitExt as _};

mod assertions;
mod contracts;
mod suites;
mod utils;

const DEFAULT_URL: &str = "http://127.0.0.1:8545";
const DEFAULT_PK: &str = "0x8b3a350cf5c34c9194ca85829a2df0ec3153be0318b5e2d3348e872092edffba";

fn init_tracing() {
    let env_filter =
        tracing_subscriber::filter::EnvFilter::try_from_default_env().unwrap_or_else(|_| {
            let app_name = env!("CARGO_PKG_NAME").replace('-', "_");
            let filter = format!("{app_name}=warn,e2e=info");
            tracing_subscriber::filter::EnvFilter::new(filter)
        });
    tracing_subscriber::registry()
        .with(tracing_subscriber::fmt::layer().without_time())
        .with(env_filter)
        .init();
}

#[tokio::main]
async fn main() {
    init_tracing();

    let config = TestConfig {
        rpc_url: DEFAULT_URL.to_string(),
        main_pk: DEFAULT_PK.to_string(),
    };
    let mut tester = e2e::Tester::new(config);
    tester.add_suite(suites::basic_evm::Test7702::evm());
    tester.add_suite(suites::basic_evm::Test7702::eravm());

    if let Err(err) = tester.run().await {
        tracing::error!(err = ?err, "Test run failed");
        std::process::exit(1);
    }
}
