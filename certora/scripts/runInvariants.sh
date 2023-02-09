if [[ "$1" ]]
then
    RULE="--rule $1"
fi

certoraRun certora/munged/contracts/StakedAaveV3.sol \
    certora/harness/DummyERC20Impl.sol \
    certora/harness/AaveGovernance.sol \
    certora/harness/GhoVariableDebt_Mock.sol \
    --link StakedAaveV3:STAKED_TOKEN=DummyERC20Impl \
    --link StakedAaveV3:REWARD_TOKEN=DummyERC20Impl \
    --link StakedAaveV3:GHO_DEBT_TOKEN=GhoVariableDebt_Mock \
    --link StakedAaveV3:_aaveGovernance=AaveGovernance \
    --verify StakedAaveV3:certora/specs/invariants.spec \
    $RULE \
    --solc solc8.17 \
    --cloud \
    --send_only \
    --optimistic_loop \
    --loop_iter 3 \
    --msg "invariants" 