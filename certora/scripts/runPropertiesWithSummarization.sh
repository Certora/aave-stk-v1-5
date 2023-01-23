if [[ "$1" ]]
then
    RULE="--rule $1"
fi

certoraRun certora/harness/StakedAaveV3Harness.sol \
    certora/harness/DummyERC20Impl.sol \
    certora/harness/AaveGovernance.sol \
    certora/harness/GhoVariableDebt_Mock.sol \
    certora/harness/RewardVault.sol \
    --link StakedAaveV3Harness:STAKED_TOKEN=DummyERC20Impl \
    --link StakedAaveV3Harness:REWARD_TOKEN=DummyERC20Impl \
    --link StakedAaveV3Harness:GHO_DEBT_TOKEN=GhoVariableDebt_Mock \
    --link StakedAaveV3Harness:_aaveGovernance=AaveGovernance \
    --link StakedAaveV3Harness:REWARDS_VAULT=RewardVault \
    --verify StakedAaveV3Harness:certora/specs/propertiesWithSummarizations.spec \
    $RULE \
    --solc solc8.17 \
    --staging \
    --optimistic_loop \
    --loop_iter 3 \
    --send_only \
    --settings -t=600 \
    --method "returnFunds(uint256)" \
    --msg "all props $1" 