import "base.spec"

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
    require(amount > 0);
    require(amount <= balanceOf(e.msg.sender));

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