class CallGraphNode:
    block_id = 0
    
    def __init__(self, contract, function):
        self._contract = contract
        self._function = function
        CallGraphNode.block_id += 1
        self._block_id = CallGraphNode.block_id

    def __str__(self):
        label = '"BlockID: %d\n' % self._block_id + '\n' + self._contract.name + '.' + self._function.name + '"'
        return label

    # Ref: https://stackoverflow.com/a/15774013
    def __deepcopy__(self, memo):
        cls = self.__class__
        result = cls.__new__(cls)
        memo[id(self)] = result
        for k, v in self.__dict__.items():
            if k != '_contract' and k!= '_function' and k != 'block_id' and k != '_block_id':
                setattr(result, k, deepcopy(v, memo))
        
        CallGraphNode.block_id += 1
        setattr(result, '_block_id', CallGraphNode.block_id)        
        setattr(result, '_contract', self._contract)
        setattr(result, '_function', self._function)
        return result