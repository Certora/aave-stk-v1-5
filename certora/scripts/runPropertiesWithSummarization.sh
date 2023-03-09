if [[ "$1" ]]
then
    RULE="--rule $1"
fi

certoraRun certora/harness/StakedAaveV3Harness.sol \
    certora/harness/DummyERC20Impl.sol \
    certora/harness/AaveGovernance.sol \
    certora/harness/RewardVault.sol \
    --link StakedAaveV3Harness:STAKED_TOKEN=DummyERC20Impl \
    --link StakedAaveV3Harness:REWARD_TOKEN=DummyERC20Impl \
    --link StakedAaveV3Harness:_aaveGovernance=AaveGovernance \
    --link StakedAaveV3Harness:REWARDS_VAULT=RewardVault \
    --verify StakedAaveV3Harness:certora/specs/summarizationsCollector.spec \
    --solc solc8.17 \
    --cloud \
    --optimistic_loop \
    --loop_iter 3 \
    --rules $1 $2 $3 $4 $5 $6 $7 $8 $9 ${10} ${11} ${12} ${13} ${14} ${15} ${16} \
    --settings -t=600 \
    --msg "all props $1"