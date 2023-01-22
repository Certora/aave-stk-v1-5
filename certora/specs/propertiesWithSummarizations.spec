import "Base.spec"

methods { 
    _getRewards(uint256, uint256, uint256) => NONDET
    _getAssetIndex(uint256, uint256, uint128, uint256) => NONDET
}

// Shares value cannot exceed actual locked amount of staked token
invariant allSharesAreBacked()
    previewRedeem(totalSupply()) <= stake_token.balanceOf(currentContract)

// All shares are backed by at enough underlying token
invariant allStakedAaveBacked(env e)
    stake_token.balanceOf(currentContract) >= totalSupply()/getExchangeRate()
