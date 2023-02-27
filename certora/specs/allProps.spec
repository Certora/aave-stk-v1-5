import "base.spec"
import "invariants.spec"

use invariant balanceOfZero
use invariant totalSupplyGreaterThanUserBalance
use invariant PersonalIndexLessOrEqualGlobalIndex
use invariant cooldownAmountNotGreaterThanBalance

/*
    @Rule integrityOfStaking
    @Description: successful stake function move amount of the stake token from the sender to the contract
                  and increases the sender's shares balance accordinly.
         
    @Formula: 
        {
            balanceStakeTokenDepositorBefore := stake_token.balanceOf(msg.sender),
            balanceStakeTokenVaultBefore := stake_token.balanceOf(currentContract),
            balanceBefore := balanceOf(onBehalfOf)
        }
            stake(onBehalfOf, amount)
        {
            balanceOf(onBehalfOf) = balanceBefore + amount * currentExchangeRate / EXCHANGE_RATE_FACTOR,
            stake_token.balanceOf(msg.sender) = balanceStakeTokenDepositorBefore - amount,
            stake_token.balanceOf(currentContract) = balanceStakeTokenVaultBefore + amount
        }

    @Notes:
    @Link:
*/
// stkAmount_t1 = amount * exchangeRate_t0 / 1e18
rule integrityOfStaking(address onBehalfOf, uint256 amount) {
    env e;
    require(amount < AAVE_MAX_SUPPLY());
    require(e.msg.sender != currentContract);

    uint256 balanceStakeTokenDepositorBefore = stake_token.balanceOf(e.msg.sender);
    uint256 balanceStakeTokenVaultBefore = stake_token.balanceOf(currentContract);
    uint256 balanceBefore = balanceOf(onBehalfOf);
    require(balanceStakeTokenDepositorBefore < AAVE_MAX_SUPPLY());
    require(balanceStakeTokenVaultBefore < AAVE_MAX_SUPPLY());
    require(balanceBefore < AAVE_MAX_SUPPLY());
    uint72 cooldownBefore;
    cooldownBefore, _ = stakersCooldowns(onBehalfOf);
    require(cooldownBefore == 0);
    stake(e, onBehalfOf, amount);
    uint256 balanceAfter = balanceOf(onBehalfOf);
    uint72 cooldownAfter;
    cooldownAfter, _ = stakersCooldowns(onBehalfOf);
    uint256 balanceStakeTokenDepositorAfter = stake_token.balanceOf(e.msg.sender);
    uint256 balanceStakeTokenVaultAfter = stake_token.balanceOf(currentContract);

    uint216 currentExchangeRate = getExchangeRate();

    assert balanceAfter == balanceBefore + 
        amount * currentExchangeRate / EXCHANGE_RATE_FACTOR();
    assert balanceStakeTokenDepositorAfter == balanceStakeTokenDepositorBefore - amount;
    assert balanceStakeTokenVaultAfter == balanceStakeTokenVaultBefore + amount;
}

/*
    @Rule noStakingPostSlashingPeriod
    @Description: Rule to verify that no user can stake while in post-slashing period.
         
    @Formula: 
            stake(onBehalfOf, amount)
        {
            inPostSlashingPeriod = true => function reverts
        }

    @Notes:
    @Link:
*/
rule noStakingPostSlashingPeriod(address onBehalfOf, uint256 amount) {
    env e;
    require(inPostSlashingPeriod());
    stake@withrevert(e, onBehalfOf, amount);
    assert lastReverted, "should not be able to stake in post slashing period";
}

/*
    @Rule noSlashingMoreThanMax
    @Description: Rule to verify that slashing can't exceed the available slashing amount.
         
    @Formula: 
        {
            vaultBalanceBefore := stake_token.balanceOf(currentContract),
            maxSlashable := vaultBalanceBefore * MaxSlashablePercentage / PERCENTAGE_FACTOR
        }
            slash(recipient, amount)
        {
            vaultBalanceBefore - stake_token.balanceOf(currentContract) = maxSlashable
        }

    @Notes:
    @Link:
*/
rule noSlashingMoreThanMax(uint256 amount, address recipient){
    env e;
    uint vaultBalanceBefore = stake_token.balanceOf(currentContract);
    require(vaultBalanceBefore < AAVE_MAX_SUPPLY());
    require(getMaxSlashablePercentage() >= PERCENTAGE_FACTOR() &&
        getMaxSlashablePercentage() <= MAX_PERCENTAGE());
    uint256 maxSlashable = vaultBalanceBefore * getMaxSlashablePercentage() / PERCENTAGE_FACTOR();
    
    require (amount > maxSlashable);
    require (recipient != currentContract);
    slash(e, recipient, amount);
    uint vaultBalanceAfter = stake_token.balanceOf(currentContract);

    assert vaultBalanceBefore - vaultBalanceAfter == maxSlashable;
}

/*
    @Rule integrityOfSlashing
    @Description: successful slash function increases the recipient balance by the slashed amount, 
                  decreases the vaults balance by the same amount and turns on the postSlashing period flag.
         
    @Formula: 
        {
            recipientStakeTokenBalanceBefore := stake_token.balanceOf(recipient),
            vaultStakeTokenBalanceBefore := stake_token.balanceOf(currentContract)
        }
            slash(recipient, amountToSlash)
        {
            stake_token.balanceOf(recipient) = recipientStakeTokenBalanceBefore + amountToSlash,
            stake_token.balanceOf(currentContract) = vaultStakeTokenBalanceBefore - amountToSlash,
            inPostSlashingPeriod = True
        }

    @Notes:
    @Link:
*/
rule integrityOfSlashing(address to, uint256 amount){
    env e;
    require(amount < AAVE_MAX_SUPPLY());
    require(e.msg.sender != currentContract && to != currentContract);
    require(getMaxSlashablePercentage() >= PERCENTAGE_FACTOR() &&
        getMaxSlashablePercentage() <= MAX_PERCENTAGE());

    require(totalSupply() > 0 && totalSupply() < AAVE_MAX_SUPPLY());
    uint256 total = totalSupply();

    uint256 balanceStakeTokenToBefore = stake_token.balanceOf(to);
    uint256 balanceStakeTokenVaultBefore = stake_token.balanceOf(currentContract);
    require(balanceStakeTokenToBefore < AAVE_MAX_SUPPLY());
    require(balanceStakeTokenVaultBefore < AAVE_MAX_SUPPLY());
    slash(e, to, amount);
    uint256 balanceStakeTokenToAfter = stake_token.balanceOf(to);
    uint256 balanceStakeTokenVaultAfter = stake_token.balanceOf(currentContract);
    uint256 maxSlashable = balanceStakeTokenVaultBefore * getMaxSlashablePercentage() / PERCENTAGE_FACTOR();

    uint256 amountToSlash;
    if (amount > maxSlashable) {
        amountToSlash = maxSlashable;
    } else {
        amountToSlash = amount;
    }

    assert balanceStakeTokenToAfter == balanceStakeTokenToBefore + amountToSlash;
    assert balanceStakeTokenVaultAfter == balanceStakeTokenVaultBefore - amountToSlash;
    assert inPostSlashingPeriod();

    // return uint128(((totalShares * TOKEN_UNIT) + TOKEN_UNIT) / totalAssets);
    // doesn't work - should be proven with invariant or dedicated rule for exchange rate change
    // assert getExchangeRate() == totalSupply() * EXCHANGE_RATE_FACTOR() / balanceStakeTokenVaultAfter;
}

/*
    @Rule integrityOfReturnFunds
    @Description: successful returnFunds function decreases the sender balance by the returned amount and  
                  increases the vaults balance by the same amount.
         
    @Formula: 
        {
            senderStakeTokenBalanceBefore := stake_token.balanceOf(msg.sender),
            vaultStakeTokenBalanceBefore := stake_token.balanceOf(currentContract)
        }
            returnFunds(amount)
        {
            stake_token.balanceOf(msg.sender) = recipientStakeTokenBalanceBefore - amount,
            stake_token.balanceOf(currentContract) = vaultStakeTokenBalanceBefore + amount
        }

    @Notes:
    @Link:
*/
rule integrityOfReturnFunds(uint256 amount){
    env e;
    require(amount < AAVE_MAX_SUPPLY());
    require(e.msg.sender != currentContract);

    uint256 balanceStakeTokenSenderBefore = stake_token.balanceOf(e.msg.sender);
    uint256 balanceStakeTokenVaultBefore = stake_token.balanceOf(currentContract);
    require(balanceStakeTokenSenderBefore < AAVE_MAX_SUPPLY());
    require(balanceStakeTokenVaultBefore < AAVE_MAX_SUPPLY());
    returnFunds(e, amount);
    uint256 balanceStakeTokenSenderAfter = stake_token.balanceOf(e.msg.sender);
    uint256 balanceStakeTokenVaultAfter = stake_token.balanceOf(currentContract);
    require(balanceStakeTokenVaultAfter > 0);

    assert balanceStakeTokenSenderAfter == balanceStakeTokenSenderBefore - amount;
    assert balanceStakeTokenVaultAfter == balanceStakeTokenVaultBefore + amount;
}

/*
    @Rule noEntryUntilSlashingSettled
    @Description: Rule to verify that users can't stake while until slashing is settled (after post-slashing period).
         
    @Formula: 
        {
        }
            stake@withrevert(msg.sender, amount)
        {
            inPostSlashingPeriod => stake function reverted.
        }

    @Notes:
    @Link:
*/
rule noEntryUntilSlashingSettled(uint256 amount){
    env e;

    stake@withrevert(e, e.msg.sender, amount);

    bool reverted = lastReverted;
    assert inPostSlashingPeriod() => reverted;
}

/*
    @Rule airdropNotMutualized
    @Description: Rule to verify that transfering tokens to the contract doesn't change the exchange rate.
         
    @Formula: 
        {
            exchangeRateBefore := getExchangeRate()
        }
            stake_token.transfer(currentContract, amount)
        {
            getExchangeRate() => exchangeRateBefore
        }

    @Notes:
    @Link:
*/
rule airdropNotMutualized(uint256 amount){
    env e;
    uint216 exchangeRateBefore = getExchangeRate();
    stake_token.transfer(e, currentContract, amount);
    uint216 exchangeRateAfter = getExchangeRate();
    assert exchangeRateBefore == exchangeRateAfter;
}

/*
    @Rule noRedeemOutOfUnstakeWindow
    @Description: Succesful redeem function means that the user's timestamp in within the unstake window or it's a post slashing period.
         
    @Formula: 
        {
            cooldown := stakersCooldowns(msg.sender)
        }
            redeem(to, amount)
        {
            (inPostSlashingPeriod = true) ||
            (block.timestamp > cooldown + getCooldownSeconds() &&
            block.timestamp - (cooldown + getCooldownSeconds()) <= UNSTAKE_WINDOW)
        }

    @Notes:
    @Link:
*/
rule noRedeemOutOfUnstakeWindow(address to, uint256 amount){
    env e;

    uint72 cooldown;
    cooldown, _ = stakersCooldowns(e.msg.sender);
    redeem(e, to, amount);

    // assert cooldown is inside the unstake window or it's a post slashing period
    assert inPostSlashingPeriod() ||
     (e.block.timestamp > cooldown + getCooldownSeconds() &&
        e.block.timestamp - (cooldown + getCooldownSeconds()) <= UNSTAKE_WINDOW());   
}


/*
    @Rule integrityOfRedeem
    @Description: Succesful redeem function increases the stake token balance of the recipient by the redeemed amount
                  and decreases the stake token balance of the the contract by the same amount. 
                  In addition, the sender balance should decrease by the amount it wanted to redeem.
         
    @Formula: 
        {
            balanceStakeTokenToBefore := stake_token.balanceOf(recipient),
            balanceStakeTokenVaultBefore := stake_token.balanceOf(currentContract),
            balanceBefore := balanceOf(msg.sender)
        }
            redeem(recipient, amount)
        {
            if (amount > balanceBefore) {
                amountToRedeem := balanceBefore * EXCHANGE_RATE_FACTOR / getExchangeRate();
            } else {
                amountToRedeem := amount * EXCHANGE_RATE_FACTOR / getExchangeRate();
            }

            stake_token.balanceOf(recipient) = balanceStakeTokenToBefore + amountToRedeem,
            stake_token.balanceOf(currentContract) = balanceStakeTokenVaultBefore - amountToRedeem,
            amount > balanceBefore => balanceOf(msg.sender) = 0,
            amount <= balanceBefore => balanceOf(msg.sender) = balanceBefore - amount
        }

    @Notes:
    @Link:
*/
rule integrityOfRedeem(address to, uint256 amount){
    env e;
    require(amount < AAVE_MAX_SUPPLY());
    require(e.msg.sender != currentContract && to != currentContract);

    uint256 balanceStakeTokenToBefore = stake_token.balanceOf(to);
    uint256 balanceStakeTokenVaultBefore = stake_token.balanceOf(currentContract);
    uint256 balanceBefore = balanceOf(e.msg.sender);
    require(balanceStakeTokenToBefore < AAVE_MAX_SUPPLY());
    require(balanceStakeTokenVaultBefore < AAVE_MAX_SUPPLY());
    require (balanceBefore < AAVE_MAX_SUPPLY());
    redeem(e, to, amount);
    uint256 balanceAfter = balanceOf(e.msg.sender);
    uint256 balanceStakeTokenToAfter = stake_token.balanceOf(to);
    uint256 balanceStakeTokenVaultAfter = stake_token.balanceOf(currentContract);

    uint216 currentExchangeRate = getExchangeRate();
    uint256 amountToRedeem;
    if (amount > balanceBefore) {
        amountToRedeem = balanceBefore * EXCHANGE_RATE_FACTOR() / getExchangeRate();
    } else {
        amountToRedeem = amount * EXCHANGE_RATE_FACTOR() / getExchangeRate();
    }

    assert balanceStakeTokenToAfter == balanceStakeTokenToBefore + amountToRedeem;
    assert balanceStakeTokenVaultAfter == balanceStakeTokenVaultBefore - amountToRedeem;
    if (amount > balanceBefore) {
        assert balanceAfter == 0;
    } else {
        assert balanceAfter == balanceBefore - amount;
    }

}

/*
    @Rule noRedeemOutOfUnstakeWindow
    @Description: Rule to verify that users can redeem while in post-slashing period.
         
    @Formula: 
        {
        }
            redeem(to, amount)
        {
            (inPostSlashingPeriod = true) ||
            (block.timestamp > cooldown + getCooldownSeconds() &&
            block.timestamp - (cooldown + getCooldownSeconds()) <= UNSTAKE_WINDOW)
        }

    @Notes:
    @Link:
*/
// rule redeemDuringPostSlashing(address to, uint256 amount){
//     env e;

//     require(inPostSlashingPeriod());
//     require(e.msg.value == 0);
//     require(amount > 0);
//     require(amount <= balanceOf(e.msg.sender));
//     require(getExchangeRate() != 0);

//     uint256 underlyingToRedeem = amount * EXCHANGE_RATE_FACTOR() / getExchangeRate();
//     require(stake_token.balanceOf(currentContract) >= underlyingToRedeem);

//     redeem@withrevert(e, to, amount);

//     assert !lastReverted;

// }

/*
    @Rule cooldownCorrectness
    @Description: Rule to verify the correctness of stakersCooldowns.
         
    @Formula: 
        {
            windowBefore := stakersCooldowns(msg.sender) + getCooldownSeconds() + UNSTAKE_WINDOW() - block.timestamp
        }
            <invoke any method f>
        {
            windowAfter := stakersCooldowns(msg.sender) + getCooldownSeconds + UNSTAKE_WINDOW() - block.timestamp,

            (stakersCooldowns(msg.sender) + getCooldownSeconds()) <= block.timestamp => windowBefore >= windowAfter
            (stakersCooldowns(msg.sender) + getCooldownSeconds()) > block.timestamp => windowBefore >= 0
        }

    @Notes:
    @Link:
*/
/*
rule cooldownCorrectnessOld(method f)
filtered { 
    f-> f.selector != initialize(address,address,address,uint256,uint256).selector &&
        f.selector != setCooldownSeconds(uint256).selector 
}
{
    env e;
    calldataarg args;
    address user = e.msg.sender;
    require(user != 0 && user != currentContract);
    require(e.block.timestamp > getCooldownSeconds() + UNSTAKE_WINDOW());
    require(getCooldownSeconds() > 0);

    uint72 cooldownBefore;
    //TODO: Write a similar rule which will make sure we cannot unstake more than X during the UNSTAKE_PERIOD,
    //      where X is the balance of the user at the time, when the cooldown button was pressed.
    cooldownBefore, _ = stakersCooldowns(e.msg.sender); // timestamp when was the cooldown initiated

    //The following 2 requirements make sure we are in the unstake period
    require(e.block.timestamp > cooldownBefore + getCooldownSeconds());
    require(e.block.timestamp - (cooldownBefore + getCooldownSeconds()) <= UNSTAKE_WINDOW());

    // The exact time we have left until we get to EXPIRE.
    mathint windowBefore = cooldownBefore + getCooldownSeconds() + UNSTAKE_WINDOW() - e.block.timestamp;

    f(e, args);

    uint72 cooldownAfter;
    cooldownAfter, _ = stakersCooldowns(e.msg.sender);

    // The exact time we have left until we get to EXPIRE.
    mathint windowAfter = ((cooldownAfter + getCooldownSeconds()) > e.block.timestamp 
        ? 0
        : cooldownAfter + getCooldownSeconds() + UNSTAKE_WINDOW() - e.block.timestamp);

    assert windowAfter <= windowBefore;
}
*/

/*
    @Rule cooldownCorrectness
    @Description: Rule to verify the correctness of stakersCooldowns.

    @Notes: During unstake period, each user should be able to unstake at most
            the amount they had when the cooldown has been initiated.
    @Link:
*/
rule cooldownCorrectness(env e)
{
    calldataarg args;
    address user = e.msg.sender;
    require(user != 0 && user != currentContract);
    requireInvariant cooldownAmountNotGreaterThanBalance(user);

    uint72 cooldownStart;
    uint184 sharesCooldownStart;
    uint256 amountToUnstake;
    address to;
    cooldownStart, sharesCooldownStart = stakersCooldowns(user); // timestamp when was the cooldown initiated
    uint256 sharesBefore = balanceOf(user); // number of shares


    require(sharesBefore >= sharesCooldownStart);
    // The following 3 requirements make sure we are in the unstake period
    require(cooldownStart > 0);
    require(e.block.timestamp > cooldownStart + getCooldownSeconds());
    require(e.block.timestamp - (cooldownStart + getCooldownSeconds()) <= UNSTAKE_WINDOW());

    redeem(e, to, amountToUnstake);
    uint256 soldShares = sharesBefore - balanceOf(user);

    assert amountToUnstake <= sharesCooldownStart => soldShares == amountToUnstake;
    assert amountToUnstake > sharesCooldownStart => soldShares == sharesCooldownStart;
}

/*
    @Rule rewardsGetterEquivalentClaim
    @Description: Rewards getter returns the same amount of max rewards the user deserve (if the user was to withdraw max).
         
    @Formula: 
        {
            deservedRewards := getTotalRewardsBalance(from),
            receiverBalanceBefore := reward_token.balanceOf(receiver)
        }
            claimedAmount := claimRewardsOnBehalf(from, receiver, max_uint256)
        {
            deservedRewards = claimedAmount,
            reward_token.balanceOf(receiver) = receiverBalanceBefore + claimedAmount
        }

    @Notes:
    @Link:
*/
rule rewardsGetterEquivalentClaim(method f, env e, address to, address from) {
    require to != REWARDS_VAULT();
    uint256 deservedRewards = getTotalRewardsBalance(e, from);
    uint256 _receiverBalance = reward_token.balanceOf(to);

    uint256 claimedAmount = claimRewardsOnBehalf(e, from, to, max_uint256);
    
    uint256 receiverBalance_ = reward_token.balanceOf(to);
    
    assert(deservedRewards == claimedAmount);
    assert(receiverBalance_ == _receiverBalance + claimedAmount);
}

/*
    @Rule rewardsMonotonicallyIncrease
    @Description: Rewards monotonically increasing for non claim functions.
         
    @Formula: 
        {
            deservedRewardsBefore := getTotalRewardsBalance(user)
        }
            <invoke any method f>
        {
            deservedRewardsBefore < getTotalRewardsBalance(user) => 
                f = claimRewards(address, uint256) ||
                f = claimRewardsOnBehalf(address, address, uint256) ||
                f = claimRewardsAndStake(address, uint256) ||
                f = claimRewardsAndStakeOnBehalf(address, address, uint256) ||
                f = claimRewardsAndRedeem(address, uint256, uint256) ||
                f = claimRewardsAndRedeemOnBehalf(address, address, uint256, uint256)
        }

    @Notes:
    @Link:
*/
rule rewardsMonotonicallyIncrease(method f, address user) {
    env e;
    uint256 _deservedRewards = getTotalRewardsBalance(e, user);

    env e2; calldataarg args;
    require e2.block.timestamp >= e.block.timestamp;
    f(e2, args);
    
    uint256 deservedRewards_ = getTotalRewardsBalance(e2, user);
    
    assert(!claimRewards_funcs(f) => deservedRewards_ >= _deservedRewards);
}

/*
    @Rule collectedRewardsMonotonicallyIncrease
    @Description: Rewards monotonically increasing for non claim functions.
         
    @Formula: 
        {
        }
            claimedAmount := claimRewardsOnBehalf(from, receiver, max_uint256)
        {
        }

    @Notes:
    @Link:
*/
rule collectedRewardsMonotonicallyIncrease(method f, address from, address to) {
    env e;
    storage initialStorage = lastStorage;
    
    uint256 _collectedRewards = claimRewardsOnBehalf(e, from, to, max_uint256);
    
    env e2; calldataarg args;
    require e2.block.timestamp >= e.block.timestamp;
    configureAssets(e2, args) at initialStorage;
    
    uint256 collectedRewards_ = claimRewardsOnBehalf(e, from, to, max_uint256);
    
    assert(!claimRewards_funcs(f) => collectedRewards_ >= _collectedRewards);
}

/*
    @Rule indexesMonotonicallyIncrease
    @Description: Global index monotonically increasing.
         
    @Formula: 
        {
            globalIndexBefore := getAssetGlobalIndex(asset),
            personalIndexBefore := getUserPersonalIndex(asset, user)
        }
            <invoke any method f>
        {
            getAssetGlobalIndex(asset) >= globalIndexBefore,
            getUserPersonalIndex(asset, user) >= personalIndexBefore
        }

    @Notes:
    @Link:
*/
rule indexesMonotonicallyIncrease(method f, address asset, address user) {
    requireInvariant PersonalIndexLessOrEqualGlobalIndex(asset, user);
    uint256 _globalIndex = getAssetGlobalIndex(asset);
    uint256 _personalIndex = getUserPersonalIndex(asset, user);
    
    env e; calldataarg args;
    f(e, args);
    
    uint256 globalIndex_ = getAssetGlobalIndex(asset);
    uint256 personalIndex_ = getUserPersonalIndex(asset, user);
    
    assert(globalIndex_ >= _globalIndex);
    assert(personalIndex_ >= _personalIndex);
}

/*
    @Rule slashingIncreaseExchangeRate
    @Description: Slashing increases the exchange rate.
         
    @Formula: 
        {
            ExchangeRateBefore := getExchangeRate()
        }
            slash(args)
        {
            getExchangeRate() >= ExchangeRateBefore
        }

    @Notes:
    @Link:
*/
rule slashingIncreaseExchangeRate(address receiver, uint256 amount) {
    env e; calldataarg args;
    
    uint216 _ExchangeRate = getExchangeRate();
    
    slash(e, args);
    
    uint216 ExchangeRate_ = getExchangeRate();
    
    assert(ExchangeRate_ >= _ExchangeRate);
}

/*
    @Rule returnFundsDecreaseExchangeRate
    @Description: Returning funds decreases the exchange rate.
         
    @Formula: 
        {
            ExchangeRateBefore := getExchangeRate()
        }
            returnFunds(args)
        {
            getExchangeRate() <= ExchangeRateBefore
        }

    @Notes:
    @Link:
*/
rule returnFundsDecreaseExchangeRate(address receiver, uint256 amount) {
    env e;
    uint216 _ExchangeRate = getExchangeRate();

    returnFunds(e, amount);
    
    uint216 ExchangeRate_ = getExchangeRate();
    
    assert amount > 0 => ExchangeRate_ <= _ExchangeRate;
}

/*
    @Rule exchangeRateNeverZero
    @Description: ExchangeRate can never be zero.
         
    @Formula: 
        {
            ExchangeRateBefore := getExchangeRate()
        }
            <invoke any method f>
        {
            getExchangeRate() != 0
        }

    @Notes:
    @Link:
*/

rule exchangeRateNeverZero(method f) {
    env e; calldataarg args;
    uint216 _ER = getExchangeRate();
    require _ER != 0;

    // This require proves, that the exchange rate can be 0 only when totalSupply is 0.
    // require f.selector == returnFunds(uint256).selector => totalSupply() != 0;

    f(e, args);

    uint216 ER_ = getExchangeRate();

    assert ER_ != 0;
}

/*
    @Rule slashAndReturnFundsOfZeroDoesntChangeExchangeRate
    @Description: Slashing 0 and returningFunds of 0 do not affect the exchange rate.
         
    @Formula: 
        {
            ExchangeRateBefore := getExchangeRate()
        }
            slash(dest, 0) || returnFunds(0)
        {
            getExchangeRate() != ExchangeRateBefore
        }

    @Notes:
    @Link:
*/
rule slashAndReturnFundsOfZeroDoesntChangeExchangeRate(method f){
    env e;
    address dest; uint256 amt = 0;
    uint216 _ER = getExchangeRate();
    storage initialStorage = lastStorage;
    
    slash(e, dest, amt);
    uint216 ER_AfterSlash = getExchangeRate();
    
    returnFunds(e, amt) at initialStorage;
    uint216 ER_AfterReturnFunds = getExchangeRate();

    assert(ER_AfterSlash == ER_AfterReturnFunds);
    assert(ER_AfterReturnFunds == _ER);
}

/*
    @Rule previewRedeemEquivalentRedeem
    @Description: Preview redeem returns the same underlying amount to redeem as redeem (doing the same calculation).
         
    @Formula: 
        {
            totalUnderlying := previewRedeem(amount),
            receiverBalanceBefore := stake_token.balanceOf(receiver)
        }
            redeem(receiver, amount)
        {
            totalUnderlying = stake_token.balanceOf(receiver) - receiverBalanceBefore
        }

    @Notes:
    @Link:
*/
rule previewRedeemEquivalentRedeem(method f, env e, address to, uint256 amount){
    require balanceOf(e.msg.sender) == amount;
    require currentContract != to;
    uint256 totalUnderlying = previewRedeem(amount);
    uint256 _receiverBalance = stake_token.balanceOf(to);

    redeem(e, to, amount);

    uint256 receiverBalance_ = stake_token.balanceOf(to);

    assert(totalUnderlying == receiverBalance_ - _receiverBalance);
}

/*
    @Rule previewStakeEquivalentStake
    @Description: Preview stake function returns the same shares amount to stake (doing the same calculation).
         
    @Formula: 
        {
            amountOfShares := previewStake(amount),
            receiverBalanceBefore := balanceOf(receiver)
        }
            stake(receiver, amount)
        {
            amountOfShares = previewStake(amount) - receiverBalanceBefore
        }

    @Notes:
    @Link:
*/
rule previewStakeEquivalentStake(method f, env e, address to, uint256 amount){
    requireInvariant totalSupplyGreaterThanUserBalance(to);
    uint256 amountOfShares = previewStake(amount);
    uint256 _receiverBalance = balanceOf(to);

    stake(e, to, amount);

    uint256 receiverBalance_ = balanceOf(to);

    assert(amountOfShares == receiverBalance_ - _receiverBalance);
}