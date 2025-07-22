use crate::suites::TestConfig;
use clap::Parser;
use tracing_subscriber::{layer::SubscriberExt as _, util::SubscriberInitExt as _};

mod assertions;
mod contracts;
mod suites;
mod utils;

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

#[derive(Debug, Parser)]
struct Cli {
    #[clap(flatten)]
    test_args: TestConfig,
    #[clap(flatten)]
    runner_config: e2e::TestRunnerConfiguration,
}

#[tokio::main]
async fn main() {
    init_tracing();
    let cli = Cli::parse();

    let mut tester = e2e::TestRunner::new(cli.test_args).with_runner_config(cli.runner_config);
    tester.add_suite(suites::basic_evm::Test7702::evm());
    // tester.add_suite(suites::basic_evm::Test7702::eravm());

    if let Err(err) = tester.run().await {
        tracing::error!(err = ?err, "Test run failed");
        std::process::exit(1);
    }
}
