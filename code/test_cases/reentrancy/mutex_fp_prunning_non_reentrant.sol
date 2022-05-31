pragma solidity ^0.4.24;

/*
    This example demonstrates how the state-of the art re-entrancy detection tools emits a
    lot of false positives even if re-entrancy can not happen. 
    Securify, Mythrill and Sereum will say withdrawBalance is vulnerable to re-entrancy.
    But, this is not true. All of them detects the state change as signature for re-entrancy.
    But, the attacker can not enter withdrawBalance again since mutex is set to true in the previous execution
    Hence, the if check fails.

    *Why Sereum detects this as re-entrancy*
    ========================================
    After the external call during the first execution, the attacket gets control and tries to
    enter the function again, but detects a control flow influenced by an storage variable mutex and records it. It
    can not enter the function since if check fails
    Once the control-flow comes back to this contract i.e after the external call returns it updates the set
    of locked variables and add mutex to it. Now, at the end the function tries to set the mutex to false, which is 
    completely valid. But, according to Sereum this is an attack. Hence, it even aborts an valid transaction.
    
    *Why Securify and Mythril detects this as re-entrancy*
    ======================================================
    Both the tools just detects state variable update after an external call and mark this vulnerable.
    
    *Output*
    ========
    In this example, Sailfish's explorer should raise alarm, however the refiner phase will consider as false positive. Hence,
    no alarm should be raised at the end.
    
*/
contract Reentrancy {
    mapping (address => uint) userBalance;
    mapping (address => uint) success;
    bool mutex;
    
    constructor() public {
        mutex = false;
    }

    function getBalance(address u) view public returns(uint){
        return userBalance[u];
    }

    function addToBalance() payable public{
        userBalance[msg.sender] += msg.value;
    }  

    /*
     This function is guarded by mutex and hence even if there is a state change after the 
     external call the attacket can not weaponize that to re-enter the function
    */
    function withdrawBalance(uint amount) public{
        
        if (mutex == false)
        {
            mutex = true;
            if (userBalance[msg.sender] > amount)
            {
                msg.sender.call.value(amount)();
                userBalance[msg.sender] = userBalance[msg.sender] - amount;
            }
            mutex = false;
        }
    }    
}

