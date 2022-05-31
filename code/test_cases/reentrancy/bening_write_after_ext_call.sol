pragma solidity ^0.4.24;

/*
    Both Securify and Mythril detects this as Re-entrancy. Because there is a state change of success[msg.sender]
    after the external call. But, this state change can not be used to get an re-entry in different functions.

    Output
    ======
    This is a benign write after external call. Sailfish will not raise any alarm
*/

contract Reentrancy {
    mapping (address => uint) userBalance;
    mapping (address => uint) success;
   
    function getBalance(address u) view public returns(uint){
        return userBalance[u];
    }

    function lastWithDrawSuccess(address u) view public returns(uint){
        return success[u];
    }

    function addToBalance() payable public{
        userBalance[msg.sender] += msg.value;
    }   

    function withdrawBalance(uint amount) public{
        // To protect against re-entrancy, the state variable
        // has to be change before the call
        success[msg.sender] = 0;
        
        if (userBalance[msg.sender] > amount){
            userBalance[msg.sender] = userBalance[msg.sender] - amount;
            if( ! (msg.sender.call.value(amount)() ) ){
                revert();
            }
            else
                success[msg.sender] = 1; // Both Mythrill and Sereum mark this as re-entrancy since
                                         // since there is a state change of variable success[msg.sender] 
                                         // after the external call 
        }
    }   
}
