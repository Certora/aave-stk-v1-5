import "base.spec"

ghost mathint totalStaked {
    init_state axiom totalStaked == 0;
}

ghost uint216 exchangeRate {
    init_state axiom exchangeRate == INITIAL_EXCHANGE_RATE();
}

hook Sstore _currentExchangeRate uint216 new_rate (uint216 old_rate) STORAGE {
    exchangeRate = new_rate;
}

/*
    @Invariant exchangeRateCorrectness
    @Description:
    @Notes:
    @Link: https://prover.certora.com/output/40577/55c78438915b43cfa84014b153baee5e/?anonymousKey=cc47986c3d9dc44e8801e3e591ec56d048e26f30
*/
invariant exchangeRateCorrectness()
    getExchangeRate() ==
        // TODO: add this variable into munged contract:
        // getActualAmountOfStaked() * EXCHANGE_RATE_FACTOR() / totalSupply() {
        stake_token.balanceOf(currentContract) * EXCHANGE_RATE_FACTOR() / totalSupply() {
        preserved {
            // require totalSupply() != 0;
            // requireInvariant lowerBoundNotZero();
            require (totalSupply() < AAVE_MAX_SUPPLY());
            require (stake_token.balanceOf(currentContract) < AAVE_MAX_SUPPLY());
        }
    }

/*
    @Invariant balanceOfZero
    @Description: The balance of address zero is 0
    @Link: https://prover.certora.com/output/40577/55c78438915b43cfa84014b153baee5e/?anonymousKey=cc47986c3d9dc44e8801e3e591ec56d048e26f30
*/
invariant balanceOfZero()
    balanceOf(0) == 0

/*
    @Invariant lowerBoundNotZero
    @Link: https://prover.certora.com/output/40577/55c78438915b43cfa84014b153baee5e/?anonymousKey=cc47986c3d9dc44e8801e3e591ec56d048e26f30
*/
invariant lowerBoundNotZero()
    LOWER_BOUND() > 0

/*
    @Invariant cooldownDataCorrectness
    @Description: When cooldown amount of user nonzero, the cooldown had to be triggered
    @Link: https://prover.certora.com/output/40577/55c78438915b43cfa84014b153baee5e/?anonymousKey=cc47986c3d9dc44e8801e3e591ec56d048e26f30
*/
invariant cooldownDataCorrectness(address user, env e)
    cooldownAmount(user) > 0 => cooldownTimestamp(user) > 0
    {
        preserved with (env e2)
        {
            require e2.block.timestamp == e.block.timestamp;
            require e.block.timestamp > 0;
            require e.block.timestamp < 2^32;
        }
    }

/*
    @Invariant cooldownAmountNotGreaterThanBalance
    @Description: No user can have greater cooldown amount than is their balance.
    @Link: https://prover.certora.com/output/40577/55c78438915b43cfa84014b153baee5e/?anonymousKey=cc47986c3d9dc44e8801e3e591ec56d048e26f30
*/
invariant cooldownAmountNotGreaterThanBalance(address user)
    balanceOf(user) >= cooldownAmount(user)
    {
        preserved with (env e1)
        {
            requireInvariant cooldownDataCorrectness(user, e1);
            requireInvariant totalSupplyGreaterThanUserBalance(user);
        }
        preserved transferFrom(address from, address to, uint256 amount) with (env e2)
        {
            require balanceOf(from) + balanceOf(to) <= totalSupply();
            requireInvariant cooldownDataCorrectness(user, e2);
            requireInvariant totalSupplyGreaterThanUserBalance(user);
        }
        preserved transfer(address to, uint256 amount) with (env e3)
        {
            require balanceOf(e3.msg.sender) + balanceOf(to) <= totalSupply();
            requireInvariant cooldownDataCorrectness(user, e3);
            requireInvariant totalSupplyGreaterThanUserBalance(user);
        }
    }

/*
    @Invariant totalSupplyGreaterThanUserBalance
    @Description: The total supply amount of shares is greater or equal to any user's share balance.
    @Link: https://prover.certora.com/output/40577/55c78438915b43cfa84014b153baee5e/?anonymousKey=cc47986c3d9dc44e8801e3e591ec56d048e26f30
*/
invariant totalSupplyGreaterThanUserBalance(address user)
    totalSupply() >= balanceOf(user)
    {
        preserved transferFrom(address from, address to, uint256 amount) with (env e2)
        {
            require balanceOf(from) + balanceOf(to) <= totalSupply();
        }
        preserved transfer(address to, uint256 amount) with (env e3)
        {
            require balanceOf(e3.msg.sender) + balanceOf(to) <= totalSupply();
        }
        preserved redeem(address to, uint256 amount) with (env e4)
        {
            require to == user;
            require balanceOf(e4.msg.sender) + balanceOf(to) <= totalSupply();
        }
        preserved redeemOnBehalf(address from, address to, uint256 amount) with (env e5)
        {
            require to == user;
            require balanceOf(from) + balanceOf(to) <= totalSupply();
        }
        preserved claimRewardsAndRedeem(address to, uint256 claimAmount, uint256 redeemAmount) with (env e6)
        {
            require to == user;
            require balanceOf(e6.msg.sender) + balanceOf(to) <= totalSupply();
        }
        preserved claimRewardsAndRedeemOnBehalf(address from, address to, uint256 claimAmount, uint256 redeemAmount) with (env e7)
        {
            require to == user;
            require balanceOf(from) + balanceOf(to) <= totalSupply();
        }
    }

/*
    @Invariant PersonalIndexLessOrEqualGlobalIndex
    @Description: The personal index of a user on a specific asset is at most equal to the global index of the same asset.
                  As user's personal index is derived from the global index, and therefore cannot exceed it
    @Link: https://prover.certora.com/output/40577/55c78438915b43cfa84014b153baee5e/?anonymousKey=cc47986c3d9dc44e8801e3e591ec56d048e26f30
*/
invariant PersonalIndexLessOrEqualGlobalIndex(address asset, address user)
    getUserPersonalIndex(asset, user) <= getAssetGlobalIndex(asset)

// // Duplicate for usage in allProps.spec
// // This invariant is failing here and passing in propertiesWithSummarizations.spec
// // In the summarized spec the update reward functions are mutilated by returning
// // a NONDET value for _getRewards & _getAssetIndex . The reason for this
// // summarization is because the invariant does not claim anything about rewards.
// invariant allSharesAreBacked()
//     previewRedeem(totalSupply()) <= stake_token.balanceOf(currentContract)
//     {
//         preserved stake(address to, uint256 amount) with (env e2)
//         {
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
//             require e4.msg.sender != currentContract;
//         }
//         preserved initialize(address slashingAdmin, address cooldownPauseAdmin, address claimHelper,
//                             uint256 maxSlashablePercentage, uint256 cooldownSeconds) with (env e5)
//         {
//             require getExchangeRate() == INITIAL_EXCHANGE_RATE();
//         }
//     }
