pragma solidity ^0.4.24;

contract Reentrancy {
    mapping (address => uint) userBalance;
   
    function getBalance(address u) view public returns(uint){
        return userBalance[u];
    }

    function addToBalance() payable public{
        userBalance[msg.sender] += msg.value;
    }   

    function withdrawBalance(uint amount) public{
    	if (userBalance[msg.sender] >= amount){
		amount = userBalance[msg.sender];
		userBalance[msg.sender] = 0;
		if( ! (msg.sender.call.value(amount)() ) ){
		    revert();
		}
	}	
    }   
}
