pragma solidity ^0.5.0;

contract BabyTOD {
  mapping(uint256 => address) slots;

  function reserve(uint256 id) public {
    if (slots[id] == address(0)){
      slots[id] = msg.sender;
    }
  }
}