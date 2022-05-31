pragma solidity ^0.5.8;

/* 
* ===== Mythril: False negative =====
*
* Mythril fails to find the re-entrancy in its
* default configuration as its default loop
* bound is 3. `--loop-bound` (`-b`) determines
* the maximum number of times a loop will be iterated
* by laser, the symbolic execution engine of Mythril.
* 
* [CMD]: myth analyze example06.sol     // No issues detected
*
* However, it loop bound is increased to at least 4, laser
* can synthesize transaction sequences with 4 loop iterations
* required to trigger the bug. However, increasing the loop bound
* even for such a small contract increases the analysis
* time by almost a factor of 7; thus making it expensive and
* hard to scale.
*
* [CMD]: myth analyze example06.sol --loop-bound 4   // State change after external call
*
* Sailfish will raise alerts here
*/

contract LoopBound {
    uint balance;

    // Constructor, initializes state variables
    constructor () public {
        balance = 100;
    }

    // Sends ether only in the fourth iteration
    function SendInFourthIteration() public {        
        uint amount = 0;

        while (true) {
            // Increases the pay-out in each iteration
            amount += 1;

            /*
            * Checks if the amount to be transferred is
            * more than the current balance. Ether is
            * transferred only in the fourth iteration
            * (amount > 3). First three iterations
            * of this loop only increases the `amount`,
            * while the fourth one actually succeeds.
            */
            if (balance > amount && amount > 3) {
                // External call
                msg.sender.call.value(amount)("");

                // [BUG]: State change after external call
                balance -= amount;
                break;
            }
        }
    }
}
