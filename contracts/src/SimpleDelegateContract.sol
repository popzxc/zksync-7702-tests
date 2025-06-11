// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

contract SimpleDelegateContract {
    event Success();
    event Executed(address indexed to, uint256 value, bytes data);

    struct Call {
        bytes data;
        address to;
        uint256 value;
    }

    function execute(Call[] memory calls) external payable {
        for (uint256 i = 0; i < calls.length; i++) {
            Call memory call = calls[i];
            (bool success, bytes memory result) = call.to.call{
                value: call.value
            }(call.data);
            require(success, string(result));
            emit Executed(call.to, call.value, call.data);
        }
    }

    function executeDelegate(Call[] memory calls) external payable {
        for (uint256 i = 0; i < calls.length; i++) {
            Call memory call = calls[i];
            // Just in case: this is not very safe, would not recommend in production.
            (bool success, bytes memory result) = address(call.to).delegatecall(
                call.data
            );
            require(success, string(result));
            emit Executed(call.to, call.value, call.data);
        }
    }

    function executeStatic(Call[] memory calls) external payable {
        for (uint256 i = 0; i < calls.length; i++) {
            Call memory call = calls[i];
            // Just in case: this is not very safe, would not recommend in production.
            (bool success, bytes memory result) = address(call.to).staticcall(
                call.data
            );
            require(success, string(result));
            emit Executed(call.to, call.value, call.data);
        }
    }

    function triggerSuccess() external {
        emit Success();
    }

    function triggerRevert() external pure {
        revert("This is a revert");
    }

    function ensureMsgSender(address expectedSender) external view {
        require(msg.sender == expectedSender, "Unexpected msg.sender");
    }

    receive() external payable {}
}

contract DelegationTarget {
    uint256 private value = 0;

    function setValue(uint256 _value) external {
        value = _value;
    }

    function getValue() external view returns (uint256) {
        return value;
    }
}

contract ERC20 {
    address public minter;
    mapping(address => uint256) private _balances;

    constructor(address _minter) {
        minter = _minter;
    }

    function mint(uint256 amount, address to) public {
        _mint(to, amount);
    }

    function balanceOf(address account) public view returns (uint256) {
        return _balances[account];
    }

    function transfer(address to, uint256 amount) public {
        require(to != address(0), "ERC20: transfer to the zero address");
        require(
            _balances[msg.sender] >= amount,
            "ERC20: transfer amount exceeds balance"
        );
        unchecked {
            _balances[msg.sender] -= amount;
            _balances[to] += amount;
        }
    }

    function _mint(address account, uint256 amount) internal {
        require(msg.sender == minter, "ERC20: msg.sender is not minter");
        require(account != address(0), "ERC20: mint to the zero address");
        unchecked {
            _balances[account] += amount;
        }
    }
}
