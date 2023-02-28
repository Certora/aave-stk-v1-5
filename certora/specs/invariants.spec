import "base.spec"

ghost mathint totalStaked {
    init_state axiom totalStaked == 0;
}

ghost uint216 exchangeRate {
    init_state axiom exchangeRate == INITIAL_EXCHANGE_RATE();
}

// hook example
// hook Sstore _balances[KEY address user].delegationState uint8 new_state (uint8 old_state) STORAGE {
//     totalStaked = totalStaked - old_state + new_state;
// }

hook Sstore _currentExchangeRate uint216 new_rate (uint216 old_rate) STORAGE {
    exchangeRate = new_rate;
}

invariant exchangeRateCorrectness()
    getExchangeRate() == 
        stake_token.balanceOf(currentContract) * EXCHANGE_RATE_FACTOR() / totalSupply() {
        preserved {
            require (totalSupply() < AAVE_MAX_SUPPLY());
            require (stake_token.balanceOf(currentContract) < AAVE_MAX_SUPPLY());
        }
    }

// The balance of address zero is 0
invariant balanceOfZero()
    balanceOf(0) == 0

// When cooldown amount of user nonzero, the cooldown had to be triggered
invariant cooldownDataCorrectness(address user, env e)
    cooldownAmount(user) > 0 => cooldownTimestamp(user) > 0
    {
        // The problem is, that the timestamp used in this invariant within the function call
        // can become zero. We are unable to require it nonzero. Maybe it should not be
        // an invariant at all, when it takes timestamps into account.
        // preserved with (env e2)
        // {
        //     require e2.block.timestamp == e.block.timestamp;
        //     require e2.block.timestamp > 0;
        // }
        preserved cooldown() with (env e2)
        {
            require e2.block.timestamp == e.block.timestamp;
            require e2.block.timestamp > 0;
        }
        preserved cooldownOnBehalfOf(address from) with (env e2)
        {
            require e2.block.timestamp == e.block.timestamp;
            require e2.block.timestamp > 0;
        }
    }

// The cooldown amount does not exceed users balance.
invariant cooldownAmountNotGreaterThanBalance(address user)
    balanceOf(user) >= cooldownAmount(user)
    {
        preserved
        {
            require cooldownAmount(user) > 0 => cooldownTimestamp(user) > 0;
            // require balanceOf(user) <= totalSupply();
            requireInvariant totalSupplyGreaterThanUserBalance(user);
            //require totalSupply() + totalSupply() < max_uint256;
        }
        preserved transferFrom(address from, address to, uint256 amount) with (env e2)
        {
            require balanceOf(from) + balanceOf(to) <= totalSupply();
            require cooldownAmount(user) > 0 => cooldownTimestamp(user) > 0;
            // require balanceOf(user) <= totalSupply();
            requireInvariant totalSupplyGreaterThanUserBalance(user);
            //require totalSupply() + totalSupply() < max_uint256;
        }
        preserved transfer(address to, uint256 amount) with (env e3)
        {
            require balanceOf(e3.msg.sender) + balanceOf(to) <= totalSupply();
            require cooldownAmount(user) > 0 => cooldownTimestamp(user) > 0;
            // require balanceOf(user) <= totalSupply();
            requireInvariant totalSupplyGreaterThanUserBalance(user);
            //require totalSupply() + totalSupply() < max_uint256;
        }
    }


// The total supply amount of shares is greater or equal to any user's share balance
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

// The personal index of a user on a specific asset is at most equal to the global index of the same asset
// User's personal index is derived from the global index, and therefore cannot exceed it
invariant PersonalIndexLessOrEqualGlobalIndex(address asset, address user)
    getUserPersonalIndex(asset, user) <= getAssetGlobalIndex(asset)

// Duplicate for usage in allProps.spec
invariant allSharesAreBacked()
    previewRedeem(totalSupply()) <= stake_token.balanceOf(currentContract)