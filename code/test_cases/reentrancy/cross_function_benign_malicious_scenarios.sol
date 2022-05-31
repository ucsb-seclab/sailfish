pragma solidity ^0.4.24;


/*
 This is an example of cross-function reentrancy. Where Sailfish will raise alerts for the following dependent function pairs:
 (withdrawAllBalance, withdrawAllBalance), (withdrawAllBalance, transferBalance), and (withdrawAllBalance, transferAll). However,
 after Refiner phase runs, it will consider these two pairs: (withdrawAllBalance, withdrawAllBalance), (withdrawAllBalance, transferAll)
 as infeasble due to infeasible path conditions. It will only raise alerts for (withdrawAllBalance, transferBalance) as it is a valid
 true positive.
*/

contract CrossFunction {
  mapping(address => uint) creditAmount;
  mapping(address => bool) creditReward;
    
  function depositEther() public payable {
    if (msg.value > 0) { 
      creditAmount[msg.sender] = creditAmount[msg.sender] + msg.value;
    }
  }

  function withdrawAllBalance() public {
    uint creditBalance = creditAmount[msg.sender];
    
    if (creditBalance > 0 && !creditReward[msg.sender])
    {
      creditReward[msg.sender] = true;
      msg.sender.call.value(creditBalance)("");
      creditAmount[msg.sender] = 0;
    }
  }

  function transferBalance(address to) public {
    if (creditAmount[msg.sender] > 0 ) {
      creditAmount[to] = creditAmount[msg.sender];
      creditAmount[msg.sender] = 0;
    }
  }

  function transferAll() public {
    if (!creditReward[msg.sender]) {
      creditReward[msg.sender] = true;
      uint amount = creditAmount[msg.sender];
      creditAmount[msg.sender] = 0;
      msg.sender.transfer(amount);

    }
  }
}
