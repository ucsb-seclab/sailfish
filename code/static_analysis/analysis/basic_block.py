import copy

class BasicBlock:
    block_id = 0
    
    def __init__(self, instructions):
        self._instructions = instructions
        self._label = None
        self._prev_bb = None
        self._state_vars_used = {}
        self._is_critical = None
        self._is_ext_call = False
        self._pred_state_var_used = {}
        self._ir_to_node_map = {}
        self._is_recursive_call = None
        self._call_context = []
        self._is_True = None
        self._is_root = None
        BasicBlock.block_id += 1
        self._block_id = BasicBlock.block_id

    def __str__(self):
        call_context = ','.join([str(c) for c in self._call_context])
        label = '"BlockID: %d\n' % self._block_id + 'Call context: %s\n' % call_context + str(self._is_True) + '\n' + '\n'.join([str(ir) for ir in self._instructions]) + '"'
        #label = str(self._block_id)
        return label

    # Ref: https://stackoverflow.com/a/15774013
    def __deepcopy__(self, memo):
        cls = self.__class__
        result = cls.__new__(cls)
        memo[id(self)] = result
        for k, v in self.__dict__.items():
            if k!= '_is_root' and k != '_is_ext_call' and k != '_instructions' and k != '_is_critical' and \
                k!= '_ir_to_node_map' and k != 'block_id' and k != '_block_id' and k!= '_is_True' and k!= '_call_context' and \
                     k!= '_state_vars_used' and k != '_pred_state_var_used' and k != '_prev_bb' and k != '_is_recursive_call' and k != '_label':
                setattr(result, k, deepcopy(v, memo))
        
        BasicBlock.block_id += 1
        setattr(result, '_prev_bb', self._prev_bb)
        self._prev_bb = result
        setattr(result, '_block_id', BasicBlock.block_id)
        setattr(result, '_label', self._label)   
        setattr(result, '_instructions', copy.copy(self._instructions))
        setattr(result, '_ir_to_node_map', copy.copy(self._ir_to_node_map))
        setattr(result, '_call_context', copy.copy(self._call_context))
        setattr(result, '_is_True', self._is_True)
        setattr(result, '_state_vars_used', copy.copy(self._state_vars_used))
        setattr(result, '_pred_state_var_used', copy.copy(self._pred_state_var_used))
        setattr(result, '_is_ext_call', self._is_ext_call)
        setattr(result, '_is_root', self._is_root)
        setattr(result, '_is_critical', self._is_critical)
        setattr(result, '_is_recursive_call', self._is_recursive_call)
        return result