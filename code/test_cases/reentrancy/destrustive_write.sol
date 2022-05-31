pragma solidity ^0.5.0;
/*
  This is a demonstration of an attack example which should be undetected by
  both Securify and Sereum. 

  * Why Securify can not detect this *
  ====================================
  Securify only marks a contract as malicious if there is a state variable write
  after the external call. In splitFunds there is no state update after the external call

  * Why Sereum can not detect this *
  ====================================
  Sereum detects re-entrancy by the following way
  1. Taint source is : SLOAD and taint sink is JUMPI
  2. Set of control flow influencing variables are stored in the node when a called contract complete its execution 
  3. “AFTER” every external call, Sereum updates the set of locked variables, locked variables are those which are 
      tainted and decide the control flow in some previous invocation of the same contract. 
      Whenever Sereum encounters a SSTORE, it intercepts the write to see whether 
      that write involves any locked variables. If yes, it aborts the entire transaction
  In this example, there is no state varible written after the external call, hence Sereum won't be able to detect it as
  re-entrancy
  
  * Output *
  ===========
  Sailfish will raise alarm in splitFunds and splitFunds combo for dependencies `splits[id] = split;` and `b.transfer(depo * (100 - splits[id]) / 100);`
  
*/

contract PaymentSharer {
  mapping(uint => uint) splits;
  mapping(uint => uint) deposits;
  mapping(uint => address payable) first;
  mapping(uint => address payable) second;

  function init(uint id, address payable _first, address payable _second) public {
    require(first[id] == address(0) && second[id] == address(0));
    require(first[id] == address(0) && second[id] == address(0));
    first[id] = _first;
    second[id] = _second;
  }

  function deposit(uint id) public payable {
    deposits[id] += msg.value;
  }

  function updateSplit(uint id, uint split) public {
    require(split <= 100);
    splits[id] = split;
  }

  function splitFunds(uint id) public {
    // Here would be: 
    // Signatures that both parties agree with this split

    // Split
    address payable a = first[id];
    address payable b = second[id];
    uint depo = deposits[id];
    deposits[id] = 0;

    // Before this call, the attacker will call the splitFunds once and make the split[id] to be 1. So, that
    // all the deposits will be transfered to his preferred address
    a.call.value(depo * splits[id] / 100)(""); 
    // Before the next call gets executed the attacker fallback function calls back to this contract
    // again into the function updateSplit with split = 0 and for the next call it can 
    // again transfer the whole amount to its preferred address
    b.transfer(depo * (100 - splits[id]) / 100);
  }
}
