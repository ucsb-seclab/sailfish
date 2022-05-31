'''
    This class serves as a wrapper for state_variable which are struct. Since, slither 
    all the inbuilt analyses (read/write/taint/..) collapse all the fields of the variable to the variable itself. 
    This means that structures, mapping, and nested types are seen as one large chunk. 
    (https://github.com/crytic/slither/pull/346) that will give a better representation at the IR level, and remove this limitation
    But, this one is in very nascent stage and do not handle a lot of things
    Hence we try to emulate field sensitivity in slither
    Each varnode contains information about the structure variables
'''
class IndexNode:
    def __init__(self, origin, index=None, member=None):
        self.origin = origin
        self.index = index
        self.member = member
    
    def __str__(self):
        if self.index == None and self.member == None:
            expr = self.get_str(self.origin)

        elif self.index is None:
            expr = self.get_str(self.origin) + "." + str(self.member)
        
        else:
            expr = self.get_str(self.origin) + "[" + str(self.index) + "]"
        
        return expr

    def get_str(self, variable):
        if isinstance(variable, list):
            return self.get_str(variable[0])

        elif isinstance(variable, IndexNode):
            if variable.index == None and variable.member == None:
                expr = self.get_str(variable.origin)

            elif variable.index is None:
                expr = self.get_str(variable.origin) + "." + str(variable.member)

            else:
                expr = self.get_str(variable.origin) + "[" + str(variable.index) + "]"

            return expr
        else:
            return str(variable)

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