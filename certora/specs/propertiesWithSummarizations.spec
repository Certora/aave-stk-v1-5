import "Base.spec"

methods { 
    _getRewards(uint256, uint256, uint256) => NONDET
    _getAssetIndex(uint256, uint256, uint128, uint256) => NONDET
}

// Shares value cannot exceed actual locked amount of staked token
invariant allSharesAreBacked()
    previewRedeem(totalSupply()) <= stake_token.balanceOf(currentContract)
    {
        // preserved with (env e)
        // {
        //     require e.msg.sender != currentContract;
        // }
        preserved stake(address to, uint256 amount) with (env e2)
        {
            require e2.msg.sender != currentContract;
        }
        preserved stakeWithPermit(address from, address to, uint256 amount, 
                                    uint256 deadline, uint8 v, bytes32 r, bytes32 s) with (env e3)
        {
            require e3.msg.sender != currentContract;
            require from != currentContract;
        }
        preserved returnFunds(uint256 amount) with (env e4)
        {
            require e4.msg.sender != currentContract;
        }
    }

// All shares are backed by at enough underlying token
invariant allStakedAaveBacked(env e)
    stake_token.balanceOf(currentContract) >= totalSupply()/getExchangeRate()
