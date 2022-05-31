class OpNode:
    block_id = 0
    
    def __init__(self, left_value, op_str, right_value):
        self.left_value = left_value
        self.right_value = right_value
        self.op_str = op_str
        OpNode.block_id += 1
        self._block_id = OpNode.block_id
    
    def __str__(self):
        expression = str(self.left_value) + str(self.op_str) + str(self.right_value)
        return expression

    # Ref: https://stackoverflow.com/a/15774013
    def __deepcopy__(self, memo):
        cls = self.__class__
        result = cls.__new__(cls)
        memo[id(self)] = result
        for k, v in self.__dict__.items():
            if k != 'right_value' and k!= 'left_value' and k != 'block_id' and k != '_block_id' and k!= 'op_str':
                setattr(result, k, deepcopy(v, memo))
        
        OpNode.block_id += 1
        setattr(result, '_block_id', OpNode.block_id)        
        setattr(result, 'left_value', self.left_value)
        setattr(result, 'right_value', self.right_value)
        setattr(result, 'op_str', self.op_str)
        return result