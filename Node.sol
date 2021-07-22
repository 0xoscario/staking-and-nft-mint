// SPDX-License-Identifier: MIT
// File: @openzeppelin/contracts/token/ERC20/IERC20.sol


pragma solidity ^0.6.0;

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}

// File: @openzeppelin/contracts/math/SafeMath.sol


pragma solidity ^0.6.0;

/**
 * @dev Wrappers over Solidity's arithmetic operations with added overflow
 * checks.
 *
 * Arithmetic operations in Solidity wrap on overflow. This can easily result
 * in bugs, because programmers usually assume that an overflow raises an
 * error, which is the standard behavior in high level programming languages.
 * `SafeMath` restores this intuition by reverting the transaction when an
 * operation overflows.
 *
 * Using this library instead of the unchecked operations eliminates an entire
 * class of bugs, so it's recommended to use it always.
 */
library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");

        return c;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return sub(a, b, "SafeMath: subtraction overflow");
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        uint256 c = a - b;

        return c;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
        if (a == 0) {
            return 0;
        }

        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");

        return c;
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return div(a, b, "SafeMath: division by zero");
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold

        return c;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return mod(a, b, "SafeMath: modulo by zero");
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts with custom message when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b != 0, errorMessage);
        return a % b;
    }
}

// File: @openzeppelin/contracts/utils/Address.sol


pragma solidity ^0.6.2;

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies in extcodesize, which returns 0 for contracts in
        // construction, since the code is only stored at the end of the
        // constructor execution.

        uint256 size;
        // solhint-disable-next-line no-inline-assembly
        assembly { size := extcodesize(account) }
        return size > 0;
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        // solhint-disable-next-line avoid-low-level-calls, avoid-call-value
        (bool success, ) = recipient.call{ value: amount }("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain`call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
      return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data, string memory errorMessage) internal returns (bytes memory) {
        return _functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value, string memory errorMessage) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        return _functionCallWithValue(target, data, value, errorMessage);
    }

    function _functionCallWithValue(address target, bytes memory data, uint256 weiValue, string memory errorMessage) private returns (bytes memory) {
        require(isContract(target), "Address: call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.call{ value: weiValue }(data);
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                // solhint-disable-next-line no-inline-assembly
                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}

// File: @openzeppelin/contracts/token/ERC20/SafeERC20.sol


pragma solidity ^0.6.0;




/**
 * @title SafeERC20
 * @dev Wrappers around ERC20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    using SafeMath for uint256;
    using Address for address;

    function safeTransfer(IERC20 token, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(IERC20 token, address from, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(IERC20 token, address spender, uint256 value) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        // solhint-disable-next-line max-line-length
        require((value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    function safeIncreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).add(value);
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function safeDecreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).sub(value, "SafeERC20: decreased allowance below zero");
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address.functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.

        bytes memory returndata = address(token).functionCall(data, "SafeERC20: low-level call failed");
        if (returndata.length > 0) { // Return data is optional
            // solhint-disable-next-line max-line-length
            require(abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
        }
    }
}

// File: @openzeppelin/contracts/GSN/Context.sol


pragma solidity ^0.6.0;

/*
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with GSN meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address payable) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes memory) {
        this; // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
        return msg.data;
    }
}

// File: @openzeppelin/contracts/access/Ownable.sol


pragma solidity ^0.6.0;

/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
contract Ownable is Context {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the deployer as the initial owner.
     */
    constructor () internal {
        address msgSender = _msgSender();
        _owner = msgSender;
        emit OwnershipTransferred(address(0), msgSender);
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(_owner == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions anymore. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }
}

// File: contracts/owner/Auth.sol

pragma solidity ^0.6.0;



contract Auth is Context, Ownable {

    mapping(address => bool) public authMap;
    event AddAuth(address addr);
    event RemoveAuth(address addr);

    constructor() internal {
        authMap[_msgSender()] = true;
    }

    modifier onlyOperator() {
        require(
            authMap[_msgSender()],
            'Auth: caller is not the operator'
        );
        _;
    }

    function isOperator(address addr) public view returns (bool) {
        return authMap[addr];
    }

    function addAuth(address addr) public onlyOwner {
        require(addr != address(0), "Auth: addr can not be 0x0");
        authMap[addr] = true;
        emit AddAuth(addr);
    }

    function removeAuth(address addr) public onlyOwner {
        require(addr != address(0), "Auth: addr can not be 0x0");
        authMap[addr] = false;
        emit RemoveAuth(addr);
    }
}

// File: contracts/interface/INodeData.sol

pragma solidity ^0.6.12;

interface INodeData {
    function NODE_STATUS_WAIT() external view returns(uint256);
    function NODE_STATUS_OFFICIAL() external view returns(uint256);
    function NODE_STATUS_FAIL() external view returns(uint256);
    function getOfficialNodeList() external view returns(address[] memory);
    function getNodeList() external view returns(address[] memory);
    function getVoteNodeInfo(address _addr, address _nodeAddr) external view returns (uint256 amount, uint256 time);
    function getVoterInfo(address _addr) external view returns(address[] memory nodeAddr, uint256 totalAmount);
    function getNodeInfo(address _addr) external view returns (
        address nodeAddr,
        string memory name,
        string memory slogan,
        uint256 rate,
        uint256 depositAmount,
        uint256 voteAmount,
        uint256 totalAmount,
        uint256 status,
        address[] memory voteAddr
    );
    function checkClaimDeposit(address _nodeAddr) external view returns(bool);
    function addNode(
        address _addr,
        string memory _name,
        string memory _slogan,
        uint256 _rate,
        uint256 _depositAmount
    ) external;

    function vote(address _addr, address _nodeAddr, uint256 _amount) external;
    function claimVote(address _addr, address _nodeAddr, uint256 _amount) external;
    function claimDeposit(address _addr, address _nodeAddr) external;
    function addOfficialNode(address _nodeAddr) external;
    function addFailNode(address _nodeAddr) external;
    function updateNode(address _addr, string memory _name, string memory _slogan, uint256 _rate) external;
}

// File: contracts/interface/IRToken.sol

pragma solidity ^0.6.12;

interface IRToken {
    function mint(address _addr, uint256 _amount) external;
    function burnFrom(address _addr, uint256 _amount) external;
}

// File: contracts/Node.sol

pragma solidity ^0.6.12;
pragma experimental ABIEncoderV2;







contract Node is Auth {
    using SafeERC20 for IERC20;
    using SafeMath for uint256;

    struct NodeObj {
        address nodeAddr;
        string name;
        string slogan;
        uint256 rate;
        uint256 voterCount;
        // total vote amount
        uint256 totalAmount;
        // 0 pending 1 official 2 fail
        uint256 status;
        bool valid;
    }

    struct Vote {
        address addr;
        uint256 amount;
    }

    struct VoteNode {
        string name;
        address nodeAddr;
        uint256 amount;
    }

    address public nodeDataAddr;
    address public token;
    address public rToken;
    address public teamAddr;
    uint256 public nodeStartTime;
    uint256 public nodeEndTime;
    uint256 public limitRate = 50;
    uint256 public limitAmount = 2100e18;
    uint256 public limitTime = 7 days;
    uint256 public limitVoteAmount = 5000e18;
    uint256 public limitVoteAddr = 5;
    uint256 public feeRate = 20;
    uint256 public onlyOnce = 0;
    address[]  public matchAddr;
    address[]  public disMatchAddr;

    constructor(address _nodeData, address _token, address _rToken, address _teamAddr, uint256 _start, uint256 _end) public {
        nodeDataAddr = _nodeData;
        token = _token;
        rToken = _rToken;
        teamAddr = _teamAddr;
        nodeStartTime = _start;
        nodeEndTime = _end;
    }

    function setStartEnd(uint256 _nodeStartTime, uint256 _nodeEndTime) public onlyOperator {
        nodeStartTime = _nodeStartTime;
        nodeEndTime = _nodeEndTime;
    }

    function setTeamAddr(address _addr) public onlyOperator {
        teamAddr = _addr;
    }

    function setNodeDataAddr(address _addr) public onlyOperator {
        nodeDataAddr = _addr;
    }

    function setLimitTime(uint256 _interval) public onlyOperator {
        limitTime = _interval;
    }

    function setFeeRate(uint256 _feeRate) public onlyOperator {
        require(_feeRate < 100, "Node: invalid rate");
        feeRate = _feeRate;
    }

    /* ========== VIEW FUNCTION ========== */
    function getNodeGeneralInfo() public view returns (uint256 valid, uint256 invalid, uint256 total) {
        valid = 0;
        invalid = 0;
        total = 0;
        address[] memory list = INodeData(nodeDataAddr).getNodeList();
        for (uint256 i = 0; i < list.length; i++) {
            (,,,,,,uint256 totalAmount,,address[] memory voteAddr) = INodeData(nodeDataAddr).getNodeInfo(list[i]);
            if (totalAmount >= limitVoteAmount && voteAddr.length >= limitVoteAddr) {
                valid = valid.add(1);
            } else {
                invalid = invalid.add(1);
            }
            total = total.add(totalAmount);
        }
    }

    function getNodeList() public view returns (NodeObj[] memory nodeList) {
        address[] memory list = INodeData(nodeDataAddr).getNodeList();
        address[] memory officialList = INodeData(nodeDataAddr).getOfficialNodeList();
        uint256 length;
        length = list.length;
        if (officialList.length > 0) {
            length = officialList.length;
            list = officialList;
        }
        nodeList = new NodeObj[](length);
        for (uint256 i = 0; i < length; i++) {
            (address nodeAddr,
            string memory name,
            string memory slogan,
            uint256 rate,,,
            uint256 totalAmount,
            uint256 status,
            address[] memory voteAddr) = INodeData(nodeDataAddr).getNodeInfo(list[i]);
            nodeList[i].nodeAddr = nodeAddr;
            nodeList[i].name = name;
            nodeList[i].slogan = slogan;
            nodeList[i].rate = rate;
            nodeList[i].totalAmount = totalAmount;
            nodeList[i].status = status;
            nodeList[i].voterCount = voteAddr.length;
            if (totalAmount >= limitVoteAmount && voteAddr.length >= limitVoteAddr) {
                nodeList[i].valid = true;
            }
        }
        for (uint256 j = 0; j < length; j++) {
            for (uint256 k = 0; k < length - j - 1; k ++) {
                if (nodeList[k].totalAmount < nodeList[k + 1].totalAmount) {
                    NodeObj memory scoreTemp = nodeList[k];
                    nodeList[k] = nodeList[k + 1];
                    nodeList[k + 1] = scoreTemp;
                }
            }
        }
        return nodeList;
    }

    function getPersonalNodeInfo(address _nodeAddr) public view returns (string memory name, string memory slogan, uint256 rate, uint256 totalAmount, uint256 voteAmount, uint256 depositAmount, uint256 status) {
        (, name, slogan, rate, depositAmount, voteAmount, totalAmount, status,) = INodeData(nodeDataAddr).getNodeInfo(_nodeAddr);
    }

    function getPersonalNodeList(address _nodeAddr) public view returns (Vote[] memory voteList) {
        (,,,,,,,,address[] memory _voteAddr) = INodeData(nodeDataAddr).getNodeInfo(_nodeAddr);
        uint256 length = _voteAddr.length;
        voteList = new Vote[](length);

        for (uint256 i = 0; i < length; i++) {
            (uint256 amount,) = INodeData(nodeDataAddr).getVoteNodeInfo(_voteAddr[i], _nodeAddr);
            voteList[i].amount = amount;
            voteList[i].addr = _voteAddr[i];
        }

        for (uint256 j = 0; j < length; j++) {
            for (uint256 k = 0; k < length - j - 1; k ++) {
                if (voteList[k].amount < voteList[k + 1].amount) {
                    Vote memory scoreTemp = voteList[k];
                    voteList[k] = voteList[k + 1];
                    voteList[k + 1] = scoreTemp;
                }
            }
        }
    }

    function getPersonalVoteInfo(address _addr) public view returns (uint256 nodeNum, uint256 totalAmount) {
        (address[] memory _nodeAddr, uint256 _totalAmount) = INodeData(nodeDataAddr).getVoterInfo(_addr);
        totalAmount = _totalAmount;
        nodeNum = _nodeAddr.length;
    }

    function getPersonalVoteNodeInfo(address _addr) public view returns (VoteNode[] memory voteNodeList) {
        (address[] memory _nodeAddr,) = INodeData(nodeDataAddr).getVoterInfo(_addr);
        voteNodeList = new VoteNode[](_nodeAddr.length);
        for (uint256 i = 0; i < _nodeAddr.length; i++) {
            (uint256 amount,) = INodeData(nodeDataAddr).getVoteNodeInfo(_addr, _nodeAddr[i]);
            (,string memory name,,,,,,,) = INodeData(nodeDataAddr).getNodeInfo(_nodeAddr[i]);
            voteNodeList[i].name = name;
            voteNodeList[i].amount = amount;
            voteNodeList[i].nodeAddr = _nodeAddr[i];
        }
    }

    function checkClaimDeposit(address _nodeAddr) public view returns(bool) {
        return INodeData(nodeDataAddr).checkClaimDeposit(_nodeAddr);
    }

    /* ========== CORE FUNCTION ========== */
    function updateNode(string memory _name, string memory _slogan, uint256 _rate) public {
        (address nodeAddr,,,,,,,,) = INodeData(nodeDataAddr).getNodeInfo(msg.sender);
        require(nodeAddr != address(0), "Node: node is not exist");
        require(_rate >= limitRate && _rate <=100, "Node: invalid rate");
        INodeData(nodeDataAddr).updateNode(msg.sender, _name, _slogan, _rate);
    }

    function deposit(string memory _name, string memory _slogan, uint256 _rate, uint256 _amount) public {
        require(nodeStartTime <= block.timestamp, "Node: not start");
        require(nodeEndTime >= block.timestamp, "Node: already end");
        require(_rate >= limitRate && _rate < 100, "Node: rate is limit");
        require(_amount >= limitAmount, "Node: amount limit");
        (address nodeAddr,,,,,,,,) = INodeData(nodeDataAddr).getNodeInfo(msg.sender);
        require(nodeAddr == address(0), "Node: node is exist");
        IERC20(token).safeTransferFrom(msg.sender, address(this), _amount);
        IRToken(rToken).mint(msg.sender, _amount);
        INodeData(nodeDataAddr).addNode(msg.sender, _name, _slogan, _rate, _amount);

    }

    function vote(address _nodeAddr, uint256 _amount) public {
        (address nodeAddr,,,,,,,uint256 status,) = INodeData(nodeDataAddr).getNodeInfo(_nodeAddr);
        require(status != INodeData(nodeDataAddr).NODE_STATUS_FAIL(), "Node: node is fail status");
        require(nodeAddr != address(0), "Node: node is not exist");
        IERC20(token).safeTransferFrom(msg.sender, address(this), _amount);
        IRToken(rToken).mint(msg.sender, _amount);
        INodeData(nodeDataAddr).vote(msg.sender, _nodeAddr, _amount);
    }

    function claimVote(address _nodeAddr, uint256 _amount) public {
        (address nodeAddr,,,,,,,,) = INodeData(nodeDataAddr).getNodeInfo(_nodeAddr);
        require(nodeAddr != address(0), "Node: node is not exist");
        (uint256 amount, uint256 time) = INodeData(nodeDataAddr).getVoteNodeInfo(msg.sender, _nodeAddr);
        require(amount >= _amount, "Node: amount is not enough");

        IRToken(rToken).burnFrom(msg.sender, _amount);
        uint256 fee;
        if (time.add(limitTime) > block.timestamp) {
            fee = _amount.mul(feeRate).div(100);
            IERC20(token).safeTransfer(teamAddr, fee);
        }
        IERC20(token).safeTransfer(msg.sender, _amount.sub(fee));
        INodeData(nodeDataAddr).claimVote(msg.sender, _nodeAddr, _amount);
    }

    function claimDeposit() public {
        (address nodeAddr,,,,uint256 depositAmount,,,,) = INodeData(nodeDataAddr).getNodeInfo(msg.sender);
        require(nodeAddr != address(0), "Node: node is not exist");
        require(depositAmount > 0, "Node: node depositAmount is not enough");
        INodeData(nodeDataAddr).claimDeposit(msg.sender, msg.sender);
        IERC20(token).safeTransfer(msg.sender, depositAmount);
        IRToken(rToken).burnFrom(msg.sender, depositAmount);
    }

    function finish() public onlyOperator {
        require(block.timestamp > nodeEndTime, "Node: not end");
        require(onlyOnce == 0, "Node: only init once");
        onlyOnce = 1;
        NodeObj[] memory nodeList = getNodeList();

        for (uint256 i = 0; i < nodeList.length; i++) {
            if (nodeList[i].valid) {
                matchAddr.push(nodeList[i].nodeAddr);
                continue;
            }
            disMatchAddr.push(nodeList[i].nodeAddr);
        }

        uint256 limit = matchAddr.length.mul(2).div(3);
        for (uint256 j = 0; j < matchAddr.length; j++) {
            if (j < limit) {
                INodeData(nodeDataAddr).addOfficialNode(matchAddr[j]);
                continue;
            }
            INodeData(nodeDataAddr).addFailNode(matchAddr[j]);
        }

        for (uint256 k = 0; k < disMatchAddr.length; k++) {
            INodeData(nodeDataAddr).addFailNode(disMatchAddr[k]);
        }
    }
}
