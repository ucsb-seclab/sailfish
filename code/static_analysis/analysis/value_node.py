class ValueNode:
    block_id = 0
    
    def __init__(self, variable, instr_block, value, operation):
        self._instr_block = instr_block
        self._variable = variable
        ValueNode.block_id += 1
        self._block_id = ValueNode.block_id
        self._value = value
        self._op = operation
    
    def __str__(self):
        expression = str(self._variable) + str(self._op) + str(self._value)
        label = '"BlockID: %d\n' % self._block_id + '\n'.join(expression) + '"'
        return label

    # Ref: https://stackoverflow.com/a/15774013
    def __deepcopy__(self, memo):
        cls = self.__class__
        result = cls.__new__(cls)
        memo[id(self)] = result
        for k, v in self.__dict__.items():
            if k != '_instr_block' and k!= '_variable' and k != 'block_id' and k != '_block_id':
                setattr(result, k, deepcopy(v, memo))
        
        ValueNode.block_id += 1
        setattr(result, '_block_id', ValueNode.block_id)        
        setattr(result, '_instr_block', self._instr_block)
        setattr(result, '_variable', self._variable)
        return result