'''
    This class serves as a wrapper for state_variable which are struct. Since, slither 
    all the inbuilt analyses (read/write/taint/..) collapse all the fields of the variable to the variable itself. 
    This means that structures, mapping, and nested types are seen as one large chunk. 
    (https://github.com/crytic/slither/pull/346) that will give a better representation at the IR level, and remove this limitation
    But, this one is in very nascent stage and do not handle a lot of things
    Hence we try to emulate field sensitivity in slither
    Each varnode contains information about the structure variables
'''
class VarNode:
    def __init__(self, state_var, expression, field):
        self._field = field
        self._origin_var = state_var
        self._expression = expression
        self._index_node = None
   
    @property
    def name(self):
        return str(self._expression)
    
    def __str__(self):
        expr = str(self._origin_var) + "." + str(self._field)
        return expr
    
    def __deepcopy__(self, memo):
        '''
        cls = self.__class__
        result = cls.__new__(cls)
        memo[id(self)] = result
        for k, v in self.__dict__.items():
            if k != '_instructions' and k!= '_ir_to_node_map' and k != 'block_id' and k != '_block_id':
                setattr(result, k, deepcopy(v, memo))
        
        BasicBlock.block_id += 1
        setattr(result, '_block_id', BasicBlock.block_id)        
        setattr(result, '_instructions', self._instructions)
        setattr(result, '_ir_to_node_map', self._ir_to_node_map)
        '''
        return self