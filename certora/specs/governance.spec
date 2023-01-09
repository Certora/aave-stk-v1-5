import "base.spec"

definition MASK128() returns uint256 = 340282366920938463463374607431768211455;
definition getValue(uint256 blockAndValue) returns uint256 = MASK128() & blockAndValue;

sort ADDRESS;
sort COUNTER;

ghost toAddress(address) returns ADDRESS;
ghost toCounter(uint256) returns COUNTER;

ghost currentCounter(ADDRESS) returns uint256;
ghost votePowerSum() returns mathint;
ghost shadowSnapshots(ADDRESS,COUNTER) returns uint256;

// ghost mapping(address => bool) isDelegatingProposition {
//     init_state axiom forall address a. isDelegatingProposition[a] == false;
// }
definition IS_UINT256(uint256 x) returns bool = (x >= 0) && (x <= max_uint256);
definition IS_ADDRESS(address a) returns bool = (a >= 0) && (a <= max_uint160);
ghost mapping(address => address) votingDelegates {
    init_state axiom forall address a. IS_ADDRESS(a) => (votingDelegates[a] == 0);
}

ghost mapping(address=>uint256) votingSnapshotCount {
    init_state axiom forall address a. IS_ADDRESS(a) => votingSnapshotCount[a] == 0;
    axiom forall address a. IS_ADDRESS(a) => IS_UINT256(votingSnapshotCount[a]);
}

hook Sstore  _votingSnapshotsCounts[KEY address user] uint256 new_count 
    (uint256 old_count) STORAGE {
        require(votingSnapshotCount[user] == old_count);
        votingSnapshotCount[user] = new_count;
}

hook Sload uint256 new_count _votingSnapshotsCounts[KEY address user] STORAGE {
    require(votingSnapshotCount[user] == new_count);
}

hook Sstore _votingDelegates[KEY address user] address new_delegate 
    (address old_delegate) STORAGE {
        require(old_delegate == votingDelegates[user]);
        votingDelegates[user] = new_delegate;
}

hook Sload address new_delegate _votingDelegates[KEY address user]  STORAGE {
        require(new_delegate == votingDelegates[user]);
}

 
// hook Sstore _votingSnapshots[KEY address user][KEY uint256 count].(offset 0/*16 for value*/) uint128 blockAndValue (uint128 oldBandV) STORAGE {
// 	havoc shadowSnapshots assuming shadowSnapshots@new(toAddress(user),toCounter(count)) == blockAndValue && (forall ADDRESS a. forall COUNTER c. (a != toAddress(user) || c != toCounter(count)) => shadowSnapshots@new(a,c) == shadowSnapshots@old(a,c));
	
// //	if (count == currentCounter(toAddress(user))) {
// 		havoc votePowerSum assuming votePowerSum@new() == votePowerSum@old() - getValue(oldBandV) + getValue(blockAndValue);
// 	//} else {
// 		//havoc votePowerSum assuming votePowerSum@new() == votePowerSum@old();
// 	//}
// }

// hook Sstore _votingSnapshotsCounts[KEY address user] uint256 counter (uint256 oldCounter) STORAGE {
// 	havoc currentCounter assuming currentCounter@new(toAddress(user)) == counter && (forall ADDRESS a. a != toAddress(user) => currentCounter@new(a)==currentCounter@old(a));
// 	havoc votePowerSum assuming votePowerSum@new() == votePowerSum@old() - getValue(shadowSnapshots(toAddress(user),toCounter(oldCounter))) + getValue(shadowSnapshots(toAddress(user),toCounter(counter)));
// }

// account for exchange rate
// invariant votePowerIsTotalSupply() votePowerSum() == totalSupply()

rule getPowerAtBlockCorrectness(uint256 amount) {
    env e;

    require(amount < AAVE_MAX_SUPPLY());
    // requireInvariant snapshotCountZero2;
    requireInvariant delegateeOfZero;
    //requireInvariant balanceZeroWhenNoSnapshots;
    uint256 powerBefore = getPowerAtBlock(e, e.msg.sender, e.block.number - 1, VOTING_POWER());
    stake(e, e.msg.sender, amount);
    uint256 powerAfter = getPowerAtBlock(e, e.msg.sender, e.block.number - 1, VOTING_POWER());
    assert powerAfter == powerBefore;
}

invariant balanceZeroWhenNoSnapshots(address a) 
    //forall address a. IS_ADDRESS(a) => 
        (_votingSnapshotsCounts(a) == 0 => balanceOf(a) == 0) {
        preserved {
            requireInvariant delegateeOfZero();
            requireInvariant snapshotCountZero2(a);
        }
    }

invariant delegateeOfZero()
    // filtered { f-> f.selector !=  }
    votingDelegates[0] == 0 {
        preserved with (env e) {
            require(e.msg.sender != 0);
        }
}

invariant snapshotCountZero()
    forall address user. IS_ADDRESS(user) => (
        votingSnapshotCount[user] == 0 => (
            (forall address a. IS_ADDRESS(a) => (
                votingDelegates[a] != user || a == user
            )) && 
            ( votingDelegates[user] == 0 || votingDelegates[user] == user
            )
        )
    )

invariant snapshotCountZero2(address user)
    votingSnapshotCount[user] == 0 => ( votingDelegates[user] == 0 || votingDelegates[user] == user) {
        preserved with (env e) {
            require(e.msg.sender != 0);
        }
    }
