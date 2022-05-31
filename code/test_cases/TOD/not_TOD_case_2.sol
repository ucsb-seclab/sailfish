pragma solidity ^0.5.0;

contract IOU {
	mapping (address => mapping(address => uint256)) allowed;
	mapping (address => uint256) balances;
	uint256 target;

	// Approves the transfer of tokens
	function approve(address _spender, uint256 _val) public {
		allowed[msg.sender][_spender] = _val;
	}
	// Transfers tokens
	function transferFrom(address _from, address _to, uint256 _val) public {
		require(allowed[_from][msg.sender] >= _val && balances[_from] >= _val && _val > 0);
	 	balances[_from] -= _val;
	 	balances[_to] += _val;
	 	allowed [_from][msg.sender] -= _val;
	 	delete target;
	}
}