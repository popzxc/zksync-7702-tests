build:
	forge build --root contracts
	forge build --root contracts --zksync src/SimpleDelegateContract.sol
	cargo build

clean:
	forge clean --root contracts
	cargo clean

run:
	cargo run
