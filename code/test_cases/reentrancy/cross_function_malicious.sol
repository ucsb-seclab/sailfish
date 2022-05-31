pragma solidity ^0.4.24;
/*

Sailfish will raise alerts since etherBalance can be updated using depositEther

*/
contract CrossFunction {
  mapping (address => uint) tokenBalance;
  mapping (address => uint) etherBalance;
  mapping (address => bool) usedTokenOnce;
  uint256 rID_;
  uint currentRate;
  
  // Function not vulnerable to re-entrancy attack
  function trasferTokens(uint amount) public payable {
      if (tokenBalance[msg.sender] >= amount && !usedTokenOnce[msg.sender] && amount >= 2) {
          uint tokenAmount = amount / currentRate;
          tokenBalance[msg.sender] -= tokenAmount;
          usedTokenOnce[msg.sender] = true;
          msg.sender.transfer(tokenAmount);
      }
  }

  // Function not vulnerable to re-entrancy attack
  function withdrawAll() public {
      uint etherAmount = etherBalance[msg.sender];
      uint tokenAmount = tokenBalance[msg.sender];

      if (etherAmount > 0 && tokenAmount > 0) {
          uint e = etherAmount + (tokenAmount * currentRate);
          usedTokenOnce[msg.sender] = true;
          etherBalance[msg.sender] = 0;
          msg.sender.call.value(e)("");
          tokenBalance[msg.sender] = 0;
      }
  }

  function depositEther(uint amount) public payable {
  	etherBalance[msg.sender] += amount;
  }
}


