/bin/bash ./certora/scripts/runAllProps.sh \
integrityOfStaking \
noStakingPostSlashingPeriod \
noSlashingMoreThanMax \
integrityOfSlashing \
integrityOfReturnFunds \
noEntryUntilSlashingSettled \
airdropNotMutualized \
noRedeemOutOfUnstakeWindow \
totalSupplyDoesNotDropToZero \
cooldownCorrectness \
rewardsGetterEquivalentClaim \
rewardsMonotonicallyIncrease \
rewardsIncreaseForNonClaimFunctions \
indexesMonotonicallyIncrease \
slashingIncreaseExchangeRate \
returnFundsDecreaseExchangeRate \
exchangeRateNeverZero \
slashAndReturnFundsOfZeroDoesntChangeExchangeRate \
integrityOfRedeem \
previewStakeEquivalentStake