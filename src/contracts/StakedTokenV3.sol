// SPDX-License-Identifier: agpl-3.0
pragma solidity ^0.8.0;

import {IERC20} from '../interfaces/IERC20.sol';
import {IERC20WithPermit} from '../interfaces/IERC20WithPermit.sol';
import {IStakedToken} from '../interfaces/IStakedToken.sol';
import {IStakedTokenV3} from '../interfaces/IStakedTokenV3.sol';
import {ITransferHook} from '../interfaces/ITransferHook.sol';

import {ERC20} from '../lib/ERC20.sol';
import {DistributionTypes} from '../lib/DistributionTypes.sol';
import {SafeERC20} from '../lib/SafeERC20.sol';
import {PercentageMath} from '../lib/PercentageMath.sol';
import {StakedTokenV2} from './StakedTokenV2.sol';

import {VersionedInitializable} from '../utils/VersionedInitializable.sol';
import {AaveDistributionManager} from './AaveDistributionManager.sol';
import {GovernancePowerWithSnapshot} from '../lib/GovernancePowerWithSnapshot.sol';
import {RoleManager} from '../utils/RoleManager.sol';

/**
 * @title StakedToken
 * @notice Contract to stake Aave token, tokenize the position and get rewards, inheriting from a distribution manager contract
 * @author Aave
 **/
contract StakedTokenV3 is StakedTokenV2, IStakedTokenV3, RoleManager {
  using SafeERC20 for IERC20;
  using PercentageMath for uint256;

  CooldownTimes internal cooldownTimes;

  /// @notice Seconds available to redeem once the cooldown period is fullfilled
  uint256 public constant SLASH_ADMIN_ROLE = 0;
  uint256 public constant COOLDOWN_ADMIN_ROLE = 1;
  uint256 public constant CLAIM_HELPER_ROLE = 2;
  uint128 public constant INITIAL_EXCHANGE_RATE = 1e18;
  uint256 public constant TOKEN_UNIT = 1e18;

  //maximum percentage of the underlying that can be slashed in a single realization event
  uint256 internal _maxSlashablePercentage;
  bool public isPendingSlashing;

  mapping(uint256 => Snapshot) public _exchangeRateSnapshots;
  uint256 _exchangeRateSnapshotsCount;

  modifier onlySlashingAdmin() {
    require(
      msg.sender == getAdmin(SLASH_ADMIN_ROLE),
      'CALLER_NOT_SLASHING_ADMIN'
    );
    _;
  }

  modifier onlyCooldownAdmin() {
    require(
      msg.sender == getAdmin(COOLDOWN_ADMIN_ROLE),
      'CALLER_NOT_COOLDOWN_ADMIN'
    );
    _;
  }

  modifier onlyClaimHelper() {
    require(
      msg.sender == getAdmin(CLAIM_HELPER_ROLE),
      'CALLER_NOT_CLAIM_HELPER'
    );
    _;
  }

  constructor(
    IERC20 stakedToken,
    IERC20 rewardToken,
    uint256 cooldownSeconds,
    uint256 unstakeWindow,
    address rewardsVault,
    address emissionManager,
    uint128 distributionDuration,
    string memory name,
    string memory symbol,
    address governance
  )
    public
    StakedTokenV2(
      stakedToken,
      rewardToken,
      cooldownSeconds,
      unstakeWindow,
      rewardsVault,
      emissionManager,
      distributionDuration,
      name,
      symbol,
      governance
    )
  {}

  function REVISION() public pure virtual override returns (uint256) {
    return 4;
  }

  /**
   * @dev returns the revision of the implementation contract
   * @return The revision
   */
  function getRevision() internal pure virtual override returns (uint256) {
    return REVISION();
  }

  /**
   * @dev Inherited from StakedTokenV2, deprecated
   * Overwrite `initialize` from `StakedTokenV2` so it can no longer be used to initialize
   **/
  function initialize() external override {
    revert('DEPRECATED');
  }

  /**
   * @dev Called by the proxy contract
   **/
  function initialize(
    address slashingAdmin,
    address cooldownPauseAdmin,
    address claimHelper,
    uint256 maxSlashablePercentage,
    uint40 cooldownSeconds
  ) external initializer {
    require(
      maxSlashablePercentage <= PercentageMath.PERCENTAGE_FACTOR,
      'INVALID_SLASHING_PERCENTAGE'
    );
    uint256 chainId;

    //solium-disable-next-line
    assembly {
      chainId := chainid()
    }

    DOMAIN_SEPARATOR = keccak256(
      abi.encode(
        EIP712_DOMAIN,
        keccak256(bytes(super.name())),
        keccak256(EIP712_REVISION),
        chainId,
        address(this)
      )
    );

    InitAdmin[] memory initAdmins = new InitAdmin[](3);
    initAdmins[0] = InitAdmin(SLASH_ADMIN_ROLE, slashingAdmin);
    initAdmins[1] = InitAdmin(COOLDOWN_ADMIN_ROLE, cooldownPauseAdmin);
    initAdmins[2] = InitAdmin(CLAIM_HELPER_ROLE, claimHelper);

    _initAdmins(initAdmins);

    _setMaxSlashablePercentage(maxSlashablePercentage);
    _setCooldownSeconds(cooldownSeconds);
  }

  /**
   * @dev Allows a from to stake STAKED_TOKEN
   * @param to Address of the from that will receive stake token shares
   * @param amount The amount to be staked
   **/
  function stake(address to, uint256 amount)
    external
    override(IStakedToken, StakedTokenV2)
  {
    _stake(msg.sender, to, amount);
  }

  /**
   * @dev Allows a from to stake STAKED_TOKEN with gasless approvals (permit)
   * @param to Address of the from that will receive stake token shares
   * @param amount The amount to be staked
   * @param deadline The permit execution deadline
   * @param v The v component of the signed message
   * @param r The r component of the signed message
   * @param s The s component of the signed message
   **/
  function stakeWithPermit(
    address from,
    address to,
    uint256 amount,
    uint256 deadline,
    uint8 v,
    bytes32 r,
    bytes32 s
  ) external override {
    IERC20WithPermit(address(STAKED_TOKEN)).permit(
      from,
      address(this),
      amount,
      deadline,
      v,
      r,
      s
    );
    _stake(from, to, amount);
  }

  /**
   * @dev Redeems staked tokens, and stop earning rewards
   * @param to Address to redeem to
   * @param amount Amount to redeem
   **/
  function redeem(address to, uint256 amount)
    external
    override(IStakedToken, StakedTokenV2)
  {
    _redeem(msg.sender, to, amount);
  }

  /**
   * @dev Redeems staked tokens for a user. Only the claim helper contract is allowed to call this function
   * @param from Address to redeem from
   * @param to Address to redeem to
   * @param amount Amount to redeem
   **/
  function redeemOnBehalf(
    address from,
    address to,
    uint256 amount
  ) external override onlyClaimHelper {
    _redeem(from, to, amount);
  }

  /**
   * @dev Claims an `amount` of `REWARD_TOKEN` to the address `to`
   * @param to Address to send the claimed rewards
   * @param amount Amount to stake
   **/
  function claimRewards(address to, uint256 amount)
    external
    override(IStakedToken, StakedTokenV2)
  {
    _claimRewards(msg.sender, to, amount);
  }

  /**
   * @dev Claims an `amount` of `REWARD_TOKEN` to the address `to` on behalf of the user. Only the claim helper contract is allowed to call this function
   * @param from The address of the user from to claim
   * @param to Address to send the claimed rewards
   * @param amount Amount to claim
   **/
  function claimRewardsOnBehalf(
    address from,
    address to,
    uint256 amount
  ) external override onlyClaimHelper returns (uint256) {
    return _claimRewards(from, to, amount);
  }

  /**
   * @dev Claims an `amount` of `REWARD_TOKEN` and restakes
   * @param to Address to stake to
   * @param amount Amount to claim
   **/
  function claimRewardsAndStake(address to, uint256 amount)
    external
    override
    returns (uint256)
  {
    return _claimRewardsAndStakeOnBehalf(msg.sender, to, amount);
  }

  /**
   * @dev Claims an `amount` of `REWARD_TOKEN` and restakes. Only the claim helper contract is allowed to call this function
   * @param from The address of the from from which to claim
   * @param to Address to stake to
   * @param amount Amount to claim
   **/
  function claimRewardsAndStakeOnBehalf(
    address from,
    address to,
    uint256 amount
  ) external override onlyClaimHelper returns (uint256) {
    return _claimRewardsAndStakeOnBehalf(from, to, amount);
  }

  /**
   * @dev Claims an `amount` of `REWARD_TOKEN` and redeem
   * @param claimAmount Amount to claim
   * @param redeemAmount Amount to redeem
   * @param to Address to claim and unstake to
   **/
  function claimRewardsAndRedeem(
    address to,
    uint256 claimAmount,
    uint256 redeemAmount
  ) external override {
    _claimRewards(msg.sender, to, claimAmount);
    _redeem(msg.sender, to, redeemAmount);
  }

  /**
   * @dev Claims an `amount` of `REWARD_TOKEN` and redeem. Only the claim helper contract is allowed to call this function
   * @param from The address of the from
   * @param to Address to claim and unstake to
   * @param claimAmount Amount to claim
   * @param redeemAmount Amount to redeem
   **/
  function claimRewardsAndRedeemOnBehalf(
    address from,
    address to,
    uint256 claimAmount,
    uint256 redeemAmount
  ) external override onlyClaimHelper {
    _claimRewards(from, to, claimAmount);
    _redeem(from, to, redeemAmount);
  }

  /**
   * @dev Calculates the exchange rate between the amount of STAKED_TOKEN and the the StakeToken total supply.
   * Slashing will reduce the exchange rate. Supplying STAKED_TOKEN to the stake contract
   * can replenish the slashed STAKED_TOKEN and bring the exchange rate back to 1
   **/
  function exchangeRate() public view override returns (uint128) {
    if (_exchangeRateSnapshotsCount == 0) return INITIAL_EXCHANGE_RATE;
    return _exchangeRateSnapshots[_exchangeRateSnapshotsCount - 1].value;
  }

  function _getExchangeRate(uint256 totalAssets, uint256 totalShares)
    public
    pure
    returns (uint128)
  {
    return uint128((totalAssets * TOKEN_UNIT) / totalShares);
  }

  /**
   * @dev Executes a slashing of the underlying of a certain amount, transferring the seized funds
   * to destination. Decreasing the amount of underlying will automatically adjust the exchange rate
   * @param destination the address where seized funds will be transferred
   * @param amount the amount
   **/
  function slash(address destination, uint256 amount)
    external
    override
    onlySlashingAdmin
  {
    require(isPendingSlashing != true, 'PREVIOUS_SLASHING_NOT_SETTLED');
    uint256 currentExchangeRate = exchangeRate();
    uint256 currentShares = totalSupply();
    uint256 balance = (currentExchangeRate * currentShares) / TOKEN_UNIT;

    uint256 maxSlashable = balance.percentMul(_maxSlashablePercentage);

    require(amount <= maxSlashable, 'INVALID_SLASHING_AMOUNT');

    STAKED_TOKEN.safeTransfer(destination, amount);

    isPendingSlashing = true;

    _updateExchangeRate(_getExchangeRate(balance - amount, currentShares));

    emit Slashed(destination, amount);
  }

  function returnFunds(uint256 amount) external override {
    STAKED_TOKEN.safeTransfer(address(this), amount);
    uint256 currentExchangeRate = exchangeRate();
    uint256 currentShares = totalSupply();
    uint256 balance = (currentExchangeRate * currentShares) / TOKEN_UNIT;
    _updateExchangeRate(_getExchangeRate(balance + amount, currentShares));

    // TODO: emit funds returned event
  }

  function settleSlashing() external override {
    isPendingSlashing = false;
  }

  /**
   * @dev sets the admin of the slashing pausing function
   * @param percentage the new maximum slashable percentage
   */
  function setMaxSlashablePercentage(uint256 percentage)
    external
    override
    onlySlashingAdmin
  {
    _setMaxSlashablePercentage(percentage);
  }

  function _setMaxSlashablePercentage(uint256 percentage) internal {
    require(
      percentage <= PercentageMath.PERCENTAGE_FACTOR,
      'INVALID_SLASHING_PERCENTAGE'
    );

    _maxSlashablePercentage = percentage;
    emit MaxSlashablePercentageChanged(percentage);
  }

  /**
   * @dev returns the current maximum slashable percentage of the stake
   */
  function getMaxSlashablePercentage()
    external
    view
    override
    returns (uint256)
  {
    return _maxSlashablePercentage;
  }

  /**
   * @dev sets the cooldown duration whch needs to pass before the user can unstake
   * @param cooldownSeconds the new cooldown duration
   */
  function setCooldownSeconds(uint40 cooldownSeconds)
    external
    onlyCooldownAdmin
  {
    _setCooldownSeconds(cooldownSeconds);
  }

  function _setCooldownSeconds(uint40 cooldownSeconds) internal {
    cooldownTimes.cooldownSeconds = cooldownSeconds;
    emit CooldownSecondsChanged(cooldownSeconds);
  }

  function getCooldownSeconds() external view returns (uint40) {
    return cooldownTimes.cooldownSeconds;
  }

  function _claimRewards(
    address from,
    address to,
    uint256 amount
  ) internal returns (uint256) {
    require(amount != 0, 'INVALID_ZERO_AMOUNT');
    uint256 newTotalRewards = _updateCurrentUnclaimedRewards(
      from,
      balanceOf(from),
      false
    );

    uint256 amountToClaim = (amount > newTotalRewards)
      ? newTotalRewards
      : amount;

    stakerRewardsToClaim[from] = newTotalRewards - amountToClaim;
    REWARD_TOKEN.safeTransferFrom(REWARDS_VAULT, to, amountToClaim);
    emit RewardsClaimed(from, to, amountToClaim);
    return amountToClaim;
  }

  function _claimRewardsAndStakeOnBehalf(
    address from,
    address to,
    uint256 amount
  ) internal returns (uint256) {
    require(REWARD_TOKEN == STAKED_TOKEN, 'REWARD_TOKEN_IS_NOT_STAKED_TOKEN');

    uint256 userUpdatedRewards = _updateCurrentUnclaimedRewards(
      from,
      balanceOf(from),
      true
    );
    uint256 amountToClaim = (amount > userUpdatedRewards)
      ? userUpdatedRewards
      : amount;

    if (amountToClaim != 0) {
      _claimRewards(from, address(this), amountToClaim);
      STAKED_TOKEN.approve(address(this), amountToClaim);
      _stake(address(this), to, amountToClaim);
    }

    return amountToClaim;
  }

  function _stake(
    address from,
    address to,
    uint256 amount
  ) internal {
    require(isPendingSlashing != true, 'SLASHING_ONGOING');
    require(amount != 0, 'INVALID_ZERO_AMOUNT');

    uint256 balanceOfUser = balanceOf(to);

    uint256 accruedRewards = _updateUserAssetInternal(
      to,
      address(this),
      balanceOfUser,
      totalSupply()
    );

    if (accruedRewards != 0) {
      emit RewardsAccrued(to, accruedRewards);
      stakerRewardsToClaim[to] = stakerRewardsToClaim[to] + accruedRewards;
    }

    stakersCooldowns[to] = getNextCooldownTimestamp(
      0,
      amount,
      to,
      balanceOfUser
    );

    uint256 sharesToMint = (amount * TOKEN_UNIT) / exchangeRate();
    _mint(to, sharesToMint);

    STAKED_TOKEN.safeTransferFrom(from, address(this), amount);

    emit Staked(from, to, amount, sharesToMint);
  }

  /**
   * @dev Calculates the how is gonna be a new cooldown timestamp depending on the sender/receiver situation
   *  - If the timestamp of the sender is "better" or the timestamp of the recipient is 0, we take the one of the recipient
   *  - Weighted average of from/to cooldown timestamps if:
   *    # The sender doesn't have the cooldown activated (timestamp 0).
   *    # The sender timestamp is expired
   *    # The sender has a "worse" timestamp
   *  - If the receiver's cooldown timestamp expired (too old), the next is 0
   * @param fromCooldownTimestamp Cooldown timestamp of the sender
   * @param amountToReceive Amount
   * @param toAddress Address of the recipient
   * @param toBalance Current balance of the receiver
   * @return The new cooldown timestamp
   **/
  function getNextCooldownTimestamp(
    uint256 fromCooldownTimestamp,
    uint256 amountToReceive,
    address toAddress,
    uint256 toBalance
  ) public view override returns (uint256) {
    uint256 toCooldownTimestamp = stakersCooldowns[toAddress];
    if (toCooldownTimestamp == 0) {
      return 0;
    }

    uint256 minimalValidCooldownTimestamp = block.timestamp -
      cooldownTimes.cooldownSeconds -
      UNSTAKE_WINDOW;

    if (minimalValidCooldownTimestamp > toCooldownTimestamp) {
      toCooldownTimestamp = 0;
    } else {
      uint256 _fromCooldownTimestamp = (minimalValidCooldownTimestamp >
        fromCooldownTimestamp)
        ? block.timestamp
        : fromCooldownTimestamp;

      if (_fromCooldownTimestamp < toCooldownTimestamp) {
        return toCooldownTimestamp;
      } else {
        toCooldownTimestamp =
          ((amountToReceive * _fromCooldownTimestamp) +
            (toBalance * toCooldownTimestamp)) /
          (amountToReceive + toBalance);
      }
    }
    return toCooldownTimestamp;
  }

  /**
   * @dev Redeems staked tokens, and stop earning rewards
   * @param to Address to redeem to
   * @param amount Amount to redeem
   **/
  function _redeem(
    address from,
    address to,
    uint256 amount
  ) internal {
    require(amount != 0, 'INVALID_ZERO_AMOUNT');
    //solium-disable-next-line
    uint256 cooldownStartTimestamp = stakersCooldowns[from];

    if (!isPendingSlashing) {
      require(
        (block.timestamp >
          cooldownStartTimestamp + cooldownTimes.cooldownSeconds),
        'INSUFFICIENT_COOLDOWN'
      );
      require(
        (block.timestamp -
          (cooldownStartTimestamp + cooldownTimes.cooldownSeconds) <=
          UNSTAKE_WINDOW),
        'UNSTAKE_WINDOW_FINISHED'
      );
    }
    uint256 balanceOfFrom = balanceOf(from);

    uint256 amountToRedeem = (amount > balanceOfFrom) ? balanceOfFrom : amount;

    _updateCurrentUnclaimedRewards(from, balanceOfFrom, true);

    uint256 underlyingToRedeem = (amountToRedeem * exchangeRate()) / TOKEN_UNIT;

    _burn(from, amountToRedeem);

    if (balanceOfFrom - amountToRedeem == 0) {
      stakersCooldowns[from] = 0;
    }

    IERC20(STAKED_TOKEN).safeTransfer(to, underlyingToRedeem);

    emit Redeem(from, to, underlyingToRedeem, amountToRedeem);
  }

  function _updateExchangeRate(uint128 newExchangeRate) internal {
    _exchangeRateSnapshots[_exchangeRateSnapshotsCount] = Snapshot(
      uint128(block.number),
      newExchangeRate
    );
    _exchangeRateSnapshotsCount += 1;
    // TODO: emit event
  }

  /**
   * @dev binary search to return closest exchangeRate
   */
  function _searchExchangeRateByBlockNumber(uint256 blockNumber)
    internal
    view
    returns (uint256)
  {
    require(blockNumber <= block.number, 'INVALID_BLOCK_NUMBER');
    uint256 snapshotsCount = _exchangeRateSnapshotsCount;

    if (snapshotsCount == 0) {
      return INITIAL_EXCHANGE_RATE;
    }

    // First check most recent balance
    if (_exchangeRateSnapshots[snapshotsCount - 1].blockNumber <= blockNumber) {
      return _exchangeRateSnapshots[snapshotsCount - 1].value;
    }

    uint256 lower = 0;
    uint256 upper = snapshotsCount - 1;
    while (upper > lower) {
      uint256 center = upper - (upper - lower) / 2; // ceil, avoiding overflow
      Snapshot memory snapshot = _exchangeRateSnapshots[center];
      if (snapshot.blockNumber == blockNumber) {
        return snapshot.value;
      } else if (snapshot.blockNumber < blockNumber) {
        lower = center;
      } else {
        upper = center - 1;
      }
    }
    return _exchangeRateSnapshots[lower].value;
  }

  /**
   * @dev accounts for voting power adjustment based on exchangeRate
   */
  function _searchByBlockNumber(
    mapping(address => mapping(uint256 => Snapshot)) storage snapshots,
    mapping(address => uint256) storage snapshotsCounts,
    address user,
    uint256 blockNumber
  ) internal view override returns (uint256) {
    return
      (super._searchByBlockNumber(
        snapshots,
        snapshotsCounts,
        user,
        blockNumber
      ) * _searchExchangeRateByBlockNumber(blockNumber)) / TOKEN_UNIT;
  }
}
