// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

contract Evm7702Checker {
    function getAddressBytecode(
        address addr
    ) external view returns (bytes memory) {
        return addr.code;
    }

    function getAddressBytecodeHash(
        address addr
    ) external view returns (bytes32) {
        return addr.codehash;
    }

    function assertAddressBytecode(
        address addr,
        bytes memory expectedBytecode
    ) external view {
        bytes memory actualBytecode = addr.code;
        require(
            keccak256(actualBytecode) == keccak256(expectedBytecode),
            "Bytecode does not match"
        );
    }

    function assertAddressBytecodeHash(
        address addr,
        bytes32 expectedBytecodeHash
    ) external view {
        bytes32 actualBytecodeHash = addr.codehash;
        require(
            actualBytecodeHash == expectedBytecodeHash,
            "Bytecode hash does not match"
        );
    }

    function spendAllGas() external pure {
        while (true) {}
    }
}
