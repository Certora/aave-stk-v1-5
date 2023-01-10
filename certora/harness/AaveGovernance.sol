// SPDX-License-Identifier: agpl-3.0
pragma solidity 0.8.17;

import {ITransferHook} from 
    '../../src/interfaces/ITransferHook.sol';

contract AaveGovernance is ITransferHook {
    function onTransfer(address from, address to, uint256 amount) external override {

    }
}
