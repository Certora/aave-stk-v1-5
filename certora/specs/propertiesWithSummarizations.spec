import "base.spec"
import "invariants.spec"

methods {
    _getRewards(uint256, uint256, uint256) => NONDET
    _getAssetIndex(uint256, uint256, uint128, uint256) => NONDET
}

// use invariant exchangeRateCorrectness
// use invariant allSharesAreBacked
use invariant balanceOfZero
use invariant cooldownAmountNotGreaterThanBalance
use invariant cooldownDataCorrectness
use invariant lowerBoundNotZero
use invariant PersonalIndexLessOrEqualGlobalIndex
use invariant totalSupplyGreaterThanUserBalance

// Shares value cannot exceed actual locked amount of staked token
// The update rewards functions are mutilated by returning
// a NONDET value for _getRewards & _getAssetIndex . The reason for this
// summarization is because the invariant does not claim anything about rewards.
invariant allSharesAreBacked()
    previewRedeem(totalSupply()) <= stake_token.balanceOf(currentContract)
    {
        preserved stake(address to, uint256 amount) with (env e2)
        {
            require e2.msg.sender != currentContract;
        }
        preserved stakeWithPermit(address from, uint256 amount, uint256 deadline,
            uint8 v, bytes32 r, bytes32 s) with (env e3)
        {
            require from != currentContract;
        }
        preserved returnFunds(uint256 amount) with (env e4)
        {
            require e4.msg.sender != currentContract;
        }
        preserved initialize(address slashingAdmin, address cooldownPauseAdmin, address claimHelper,
                            uint256 maxSlashablePercentage, uint256 cooldownSeconds) with (env e5)
        {
            require getExchangeRate() == INITIAL_EXCHANGE_RATE();
        }
    }

// invariant getActualAmountOfStakedIsBalanceOfContract()
//     getActualAmountOfStaked() == stake_token.balanceOf(currentContract)

// // All shares are backed by at enough underlying token
// invariant allStakedAaveBacked(env e)
//     stake_token.balanceOf(currentContract) >= totalSupply()/getExchangeRate()
//     {
//         preserved
//         {
//             requireInvariant exchangeRateCorrectness();
//             require(totalSupply() > 0 && totalSupply() < AAVE_MAX_SUPPLY());
//         }
//         preserved stake(address to, uint256 amount) with (env e2)
//         {
//             requireInvariant exchangeRateCorrectness();
//             require e2.msg.sender != currentContract;
//         }
//         preserved stakeWithPermit(address from, uint256 amount, uint256 deadline,
//             uint8 v, bytes32 r, bytes32 s) with (env e3)
//         {
//             require e3.msg.sender != currentContract;
//             require from != currentContract;
//         }
//         preserved returnFunds(uint256 amount) with (env e4)
//         {
//             requireInvariant exchangeRateCorrectness();
//             require e4.msg.sender != currentContract;
//         }
//     }