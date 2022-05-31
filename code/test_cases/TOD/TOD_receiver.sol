pragma solidity ^0.5.0;

/*
  Let's say splitFunds(amount) is scheduled and then changeSender(sender_1) is scheduled with sender_1 != new_addr. 
  Depending on whether changeSender(sender_1) is executed first or splitFunds(amount) is executed first, the Ether will be 
  transferred to different users.
  
  Sailfish will raise alert here.
*/

// This is TOD Receiver
contract BabyTODReceiver {
  mapping(address => uint256) splits;
  address payable sender;

  constructor(address payable new_addr) public {
     sender = new_addr;
  }
  
  function changeSender(address payable receiver) public {
    sender = receiver;
  }
  
  function splitFunds(uint256 amount) public {
      if (sender != address(0)){
    	 sender.transfer(amount);
      }
  }
}
