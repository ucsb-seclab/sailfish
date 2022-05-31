pragma solidity ^0.4.24;
/*
Sereum marks this contract as vulnerable to re-entrancy
But this is not vulnerable. Because, entering withdrawAll is guarded by two variables
etherBalance[msg.sender] and tokenBalance[msg.sender]. So, even if tokenBalance[msg.sender] is updated 
after the external call, etherBalance is updated before the call, so an attacker can not enter this function.

Similarly, an attacker cannot enter trasferTokens() either, since this is guarded by both tokenBalance and usedTokenOnce[msg.sender]
It prohibits the attacker to enter this function as well.
But, Sereum records both tokenBalance and usedTokenOnce[msg.sender] as control flow influencing variable. Hence, after the control returns in
function withdrawAll updates the set of locked variable to be tokenBalance and usedTokenOnce[msg.sender]. And, any write after to tokenBalance, it
detect as an attack. Aborts that transaction. But, this is completely benign.


Sailfish will not raise alerts after the Refiner phase due to infeasible path conditions. Though, explorer will raise alerts.

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
}


