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
    --solc solc8.17 \
    --cloud \
    --optimistic_loop \
    --loop_iter 3 \
    --rules $1 $2 $3 $4 $5 $6 $7 $8 $9 ${10} ${11} ${12} ${13} ${14} ${15} ${16} \
    --msg "invariants" 