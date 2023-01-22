import "base.spec"
import "invariants.spec"

use invariant balanceOfZero
use invariant totalSupplyGreaterThanUserBalance
use invariant PersonalIndexLessOrEqualGlobalIndex
use invariant allSharesAreBacked


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
    uint256 cooldownBefore = stakersCooldowns(onBehalfOf);
    require(cooldownBefore == 0);
    stake(e, onBehalfOf, amount);
    uint256 balanceAfter = balanceOf(onBehalfOf);
    uint256 cooldownAfter = stakersCooldowns(onBehalfOf);
    uint256 balanceStakeTokenDepositorAfter = stake_token.balanceOf(e.msg.sender);
    uint256 balanceStakeTokenVaultAfter = stake_token.balanceOf(currentContract);

    uint128 currentExchangeRate = getExchangeRate();

    assert balanceAfter == balanceBefore + 
        amount * currentExchangeRate / EXCHANGE_RATE_FACTOR();
    assert balanceStakeTokenDepositorAfter == balanceStakeTokenDepositorBefore - amount;
    assert balanceStakeTokenVaultAfter == balanceStakeTokenVaultBefore + amount;
}


rule noStakingPostSlashingPeriod(address onBehalfOf, uint256 amount) {
    env e;
    require(inPostSlashingPeriod());
    stake@withrevert(e, onBehalfOf, amount);
    assert lastReverted, "should not be able to stake in post slashing period";
}

// should be updated for exchange rate
rule stakeTokenBalanceAtLeastTotalSupply(method f) {
    env e;
    calldataarg args;
    require(e.msg.sender != currentContract);
    require(REWARDS_VAULT() != currentContract);
    uint256 totalBefore = totalSupply();
    uint256 stakeTokenBalanceBefore = stake_token.balanceOf(currentContract);
    require(stakeTokenBalanceBefore >= totalBefore);
    f(e, args);
    uint256 totalAfter = totalSupply();
    uint256 stakeTokenBalanceAfter = stake_token.balanceOf(currentContract);
    assert stakeTokenBalanceAfter * EXCHANGE_RATE_FACTOR() / getExchangeRate() >= totalAfter;
}

rule exchangeRateStateTransition(method f){
    env e;
    calldataarg args;
    uint128 exchangeRateBefore = getExchangeRate();
    require(exchangeRateBefore < MAX_EXCHANGE_RATE());
    // at least one AAVE in staking
    require(stake_token.balanceOf(currentContract) >= 10^18);
    f(e, args);
    uint128 exchangeRateAfter = getExchangeRate();
    assert exchangeRateBefore != exchangeRateAfter =>
        f.selector == slash(address,uint256).selector ||
        f.selector == returnFunds(uint256).selector ||
        f.selector == initialize(address,address,address,uint256,uint256).selector;

    require(f.selector != initialize(address,address,address,uint256,uint256).selector);
    
    // these properties require finetuning, because of overflow and 
    // rounding by 1 that the contract does

    assert f.selector == slash(address,uint256).selector =>
        exchangeRateAfter >= exchangeRateBefore;
    assert f.selector == returnFunds(uint256).selector =>
        exchangeRateAfter <= exchangeRateBefore;
}


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

rule noEntryUntilSlashingSettled(uint256 amount){
    env e;
    require(stake_token.balanceOf(e.msg.sender) >= amount 
        && stake_token.balanceOf(currentContract) < AAVE_MAX_SUPPLY());
    require(amount > 0 && amount < AAVE_MAX_SUPPLY());
    require(e.msg.value == 0);
    require(e.msg.sender != currentContract && e.msg.sender != 0);
    require(stakersCooldowns(e.msg.sender) <= MAX_COOLDOWN());
    require(e.block.timestamp > (getCooldownSeconds() + UNSTAKE_WINDOW()));
    require(getExchangeRate() < 2 * EXCHANGE_RATE_FACTOR());
    require(balanceOf(e.msg.sender) < AAVE_MAX_SUPPLY());
    requireInvariant balanceOfZero();
    
    // reverse in updateUserAssetsInternal, need to require correct index
    // (no underflow)


    stake@withrevert(e, e.msg.sender, amount);

    assert lastReverted <=> inPostSlashingPeriod();
}

// transfer tokens to the contract and assert the exchange rate doesn't change
rule airdropNotMutualized(uint256 amount){
    env e;
    uint256 exchangeRateBefore = getExchangeRate();
    stake_token.transfer(e, currentContract, amount);
    uint256 exchangeRateAfter = getExchangeRate();
    assert exchangeRateBefore == exchangeRateAfter;
}

// if redeem succeeds, the cooldown is inside the unstake window
rule noRedeemOutOfUnstakeWindow(address to, uint256 amount){
    env e;

    uint256 cooldown = stakersCooldowns(e.msg.sender);
    redeem(e, to, amount);

    // assert cooldown is inside the unstake window or it's a post slashing period
    assert inPostSlashingPeriod() ||
     (e.block.timestamp > cooldown + getCooldownSeconds() &&
        e.block.timestamp - (cooldown + getCooldownSeconds()) <= UNSTAKE_WINDOW());   
}

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

    uint256 currentExchangeRate = getExchangeRate();
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

rule redeemDuringPostSlashing(address to, uint256 amount){
    env e;

    require(inPostSlashingPeriod());
    require(e.msg.value == 0);
    require(amount > 0);
    require(amount <= balanceOf(e.msg.sender));
    require(getExchangeRate() != 0);

    uint256 underlyingToRedeem = amount * EXCHANGE_RATE_FACTOR() / getExchangeRate();
    require(stake_token.balanceOf(currentContract) >= underlyingToRedeem);

    redeem@withrevert(e, to, amount);

    assert !lastReverted;

}

rule cooldownCorrectness(method f)
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

    uint256 cooldownBefore = stakersCooldowns(e.msg.sender);

    require(e.block.timestamp > cooldownBefore + getCooldownSeconds());
    require(e.block.timestamp - (cooldownBefore + getCooldownSeconds()) <= UNSTAKE_WINDOW());

    mathint windowBefore = cooldownBefore + getCooldownSeconds() + UNSTAKE_WINDOW() - e.block.timestamp;

    f(e, args);

    uint256 cooldownAfter = stakersCooldowns(e.msg.sender);
    mathint windowAfter = ((cooldownAfter + getCooldownSeconds()) > e.block.timestamp 
        ? 0
        : cooldownAfter + getCooldownSeconds() + UNSTAKE_WINDOW() - e.block.timestamp);

    assert windowAfter <= windowBefore;
}

// rewards getter returns the same amount of max rewards the user deserve (if the user was to withdraw max)
rule rewardsGetterEquivalentClaim(method f, env e, address to, address from) {
    require to != REWARDS_VAULT();
    uint256 deservedRewards = getTotalRewardsBalance(e, from);
    uint256 _receiverBalance = reward_token.balanceOf(to);

    uint256 claimedAmount = claimRewardsOnBehalf(e, from, to, max_uint256);
    
    uint256 receiverBalance_ = reward_token.balanceOf(to);
    
    assert(deservedRewards == claimedAmount);
    assert(receiverBalance_ == _receiverBalance + claimedAmount);
}

// Rewards monotonically increasing for non claim functions
rule rewardsMonotonicallyIncrease(method f, address user) {
    env e;
    uint256 _deservedRewards = getTotalRewardsBalance(e, user);
    
    calldataarg args;
    f(e, args);
    
    uint256 deservedRewards_ = getTotalRewardsBalance(e, user);
    
    assert(!claimRewards_funcs(f) => deservedRewards_ >= _deservedRewards);
}

// Rewards monotonically increasing for non claim functions
rule collectedRewardsMonotonicallyIncrease(method f, address from, address to) {
    env e;
    storage initialStorage = lastStorage;
    
    uint256 _collectedRewards = claimRewardsOnBehalf(e, from, to, max_uint256);
    
    env e2; calldataarg args;
    configureAssets(e2, args) at initialStorage;
    
    uint256 collectedRewards_ = claimRewardsOnBehalf(e, from, to, max_uint256);
    
    assert(!claimRewards_funcs(f) => collectedRewards_ >= _collectedRewards);
}

/* Remove Before Publishing

// Rewards monotonically increasing for non claim functions
rule rewardsMonotonicallyIncrease2(method f, address user) {
    env e;
    uint256 _deservedRewards = stakerRewardsToClaim(user);
    
    calldataarg args;
    f(e, args);
    
    uint256 deservedRewards_ = stakerRewardsToClaim(user);
    
    assert(!claimRewards_funcs(f) => deservedRewards_ >= _deservedRewards);
}*/

// Rewards monotonically increasing for non claim functions
rule whoDecreasedDeservedRewards(method f, address user) {
    env e;
    uint256 _deservedRewards = getTotalRewardsBalance(e, user);
    
    calldataarg args;
    f(e, args);
    
    uint256 deservedRewards_ = getTotalRewardsBalance(e, user);
    
    assert(deservedRewards_ < _deservedRewards => claimRewards_funcs(f));
}

// Global index monotonically increasing
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

// Slashing increases the exchange rate
rule slashingIncreaseExchangeRate(address receiver, uint256 amount) {
    env e; calldataarg args;
    
    uint128 _ExchangeRate = getExchangeRate();
    
    slash(e, args);
    
    uint128 ExchangeRate_ = getExchangeRate();
    
    assert(ExchangeRate_ >= _ExchangeRate);
}

// Returning funds decreases the exchange rate
rule returnFundsDecreaseExchangeRate(address receiver, uint256 amount) {
    env e; calldataarg args;
    uint128 _ExchangeRate = getExchangeRate();

    returnFunds(e, args);
    
    uint128 ExchangeRate_ = getExchangeRate();
    
    assert(ExchangeRate_ <= _ExchangeRate);
}

// Exchange rate shouldn't get to the value 0
rule exchangeRateNeverZero(method f) {
    env e; calldataarg args;
    uint128 _ER = getExchangeRate();
    require _ER != 0;
    
    f(e, args);

    uint128 ER_ = getExchangeRate();

    assert ER_ != 0;
}


//  Remove before publishing 

// rule exchangeRateNeverZero3(method f, uint256 amt) {
//     env e; calldataarg args;
//     require (totalSupply() + 1) * EXCHANGE_RATE_FACTOR() < max_uint128;
//     require (totalSupply() + 1) * EXCHANGE_RATE_FACTOR() - previewRedeem(totalSupply()) >= amt;
//     uint128 _ER = getExchangeRate();
//     require _ER != 0;
    
//     returnFunds(e, amt);

//     uint128 ER_ = getExchangeRate();

//     assert ER_ != 0;
// }

rule slashAndReturnFundsOfZeroDoesntChangeExchangeRate(method f){
    env e;
    address dest; uint256 amt = 0;
    uint128 _ER = getExchangeRate();
    storage initialStorage = lastStorage;
    
    slash(e, dest, amt);
    uint128 ER_AfterSlash = getExchangeRate();
    
    returnFunds(e, amt) at initialStorage;
    uint128 ER_AfterReturnFunds = getExchangeRate();

    assert(ER_AfterSlash == ER_AfterReturnFunds);
    assert(ER_AfterReturnFunds == _ER);
}

// Preview redeem returns the same underlying amount to redeem as redeem (doing the same calculation)
rule previewRedeemEquivalentRedeem(method f, env e, address to, uint256 amount){
    require balanceOf(e.msg.sender) == amount;
    require currentContract != to;
    uint256 totalUnderlying = previewRedeem(amount);
    uint256 _receiverBalance = stake_token.balanceOf(to);

    redeem(e, to, amount);

    uint256 receiverBalance_ = stake_token.balanceOf(to);

    assert(totalUnderlying == receiverBalance_ - _receiverBalance);
}

// Preview stake returns the same shares amount to stake (doing the same calculation)
rule previewStakeEquivalentStake(method f, env e, address to, uint256 amount){
    requireInvariant totalSupplyGreaterThanUserBalance(to);
    uint256 amountOfShares = previewStake(amount);
    uint256 _receiverBalance = balanceOf(to);

    stake(e, to, amount);

    uint256 receiverBalance_ = balanceOf(to);

    assert(amountOfShares == receiverBalance_ - _receiverBalance);
}