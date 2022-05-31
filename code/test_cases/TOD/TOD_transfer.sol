pragma solidity ^0.5.0;

/*
  Let's say splitFunds(amount_1) is scheduled and then reserve(sender, amount_2) is scheduled with amount_2 lesser than 
  `amount_1`, and with sender = msg.sender of splitFunds(). Depending on whether reserve(sender, amount_2) is executed first 
  or splitFunds() is executed first the final state will change.
  
  
  Sailfish will raise alert here.
  
*/

// This is TOD Transfer
contract BabyTODTransfer {
  mapping(address => uint256) splits;

  function reserve(address sender, uint256 amount) public {
      splits[sender] = amount;
  }

  function splitFunds(uint256 amount) public {

  	if (splits[msg.sender] >= amount){
  		splits[msg.sender] = splits[msg.sender] - amount;
    		msg.sender.transfer(amount);
  	}
  }
}
