UNINTERPRETABLE_FUNCTIONS = {
    "addmod(uint256,uint256,uint256)": ["CALL3 addmod", 1],
    "mulmod(uint256,uint256,uint256)": ["CALL3 mulmod", 1],
    "keccak256()": ["CALL1 keccak", 1],
    "keccak256(bytes)": ["CALL1 keccak",1], # Solidity 0.5
    "sha256()": ["CALL1 sha256", 1],
    "sha256(bytes)": ["CALL1 sha256", 1],  # Solidity 0.5
    "sha3()": ["CALL1 sha3", 1],
    "ripemd160()": ["CALL1 ripemd160", 1],
    "ripemd160(bytes)": ["CALL1 ripemd160", 1],  # Solidity 0.5
    "ecrecover(bytes32,uint8,bytes32,bytes32)": ["CALL4 ecrecover", 1],
    "blockhash(uint256)": ["CALL1 blockhash", 1],
    "this.balance()": ["this.balance", 1]
}

NOP_FUNCTIONS = {
    "gasleft()": "NEW_VAL integer",
    "revert()": "NOP",
    "revert(string)": "NOP",
    "selfdestruct(address)": "NOP",
    "suicide(address)": "NOP",
    "log0(bytes32)": "NOP",
    "log1(bytes32,bytes32)": "NOP",
    "log2(bytes32,bytes32,bytes32)": "NOP",
    "log3(bytes32,bytes32,bytes32,bytes32)": "NOP",
    "abi.encode()": "NEW_VAL integer",
    "abi.encodePacked()": "NEW_VAL integer",
    "abi.encodeWithSelector()": "NEW_VAL integer",
    "abi.encodeWithSignature()": "NEW_VAL integer",

    # abi.decode returns an a list arbitrary types
    "abi.decode()": "NEW_VAL integer",
    "type(address)": "integer",
}

global_solidity_functions = [
    {
        "name": "addmod",
        "type": ["function3"],
        "init": []
    },

    {
        "name": "mulmod",
        "type": ["function3"],
        "init": []
    },
    {
        "name": "keccak",
        "type": ["function1"],
        "init": []
    },
    {
        "name": "sha256",
        "type": ["function1"],
        "init": []
    },
    {
        "name": "sha3",
        "type": ["address"],
        "init": []
    },
    {
        "name": "ripemd160",
        "type": ["function1"],
        "init": []
    },
    {
        "name": "ecrecover",
        "type": ["function4"],
        "init": []
    },

    {
        "name": "blockhash",
        "type": ["function1"],
        "init": []
    },
]

