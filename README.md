# Integration tests for ZKsync EIP7702 implementation

Disclaimer: the code in this repo is not polished, it was mainly edited as I worked on the implementation.
Huge refactoring is due.

## How to run

1. Check out the branch with implementation in `zksync-era` repository and build the contracts with

```
zkstack dev contracts
```

2. Launch `anvil-zksync` with appropriate system contracts (replace path!):

```
anvil-zksync --emulate-evm --chain-id 31337 --port 8545  -vvvvvv --offline --dev-system-contracts local --protocol-version 28 --system-contracts-path /path/to/zksync-era/contracts/system-contracts
```

3. Build the contracts in this folder

```
make build
```

4. Run the tests

```
make run
```
