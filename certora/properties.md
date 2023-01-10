## BGD properties

### slashing

Implemented

- transfer amount of staked underlying to _destination_ 
    - check balances
    - determine that amount doesn't violate _maxSlashingPercentage_
- after slashing:
    exchangeRate_t1 = (totalStaked_t0 - amount) / totalSupply_t0
- after slashing inPostSlashingPeriod = true:
    - accounts can exit immediately without cooldown
    - no account can enter
    - no other slashing can occur

### staking

Implemented

- stkAmount_t1 = amount * exchangeRate_t0 / 1e18

### redeeming

Implemented

- amount_t1 = amount * 1e18 / exchangeRate_t0

### returnFunds

Implemented

- returned funds injected into the exchangeRate
- entering not possible until slashing is settled by slashingAdmin

### Governance

Not implemented

- sum of power of all accounts is eqlt to sum of all balances

- power_t0 = stkAmount_t0 * 1e18 / exchangeRate_t0

### Airdrops

Implemented

- airdropped tokens (not through _stake_ or _returnFunds_) are not considered
  for the exchange rate, i.e. not mutualized

### Governance

Not implemented

- Sum of voting/proposition power is less or equal than sum of all balances
- delegatee of 0 is 0 (with preserve maybe)
- if count of snapshots is 0 then for all addresses their delegatee is not you
(with ghost delegatees)
- prove t using the previous 2

### Exchange rate

Not implemented

- exchange rate is totalStaked / totalSupply

## Other properties

#### cooldown
- [v] `cooldown()` correctness: updated with block timestamp

