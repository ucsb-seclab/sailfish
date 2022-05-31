import copy
class InstrBlock:
    block_id = 0
    
    def __init__(self, instruction):
        self._instruction = instruction
        self._origin_bb = None
        self._pred_vars_used = {}
        self._state_vars_used = {}
        InstrBlock.block_id += 1
        self._call_context = []
        self._block_id = InstrBlock.block_id
        self._instr_to_node = None
        self._new_to_old = None

    def __str__(self):
        if self._instruction != "Phi Node":
            label = '"BlockID: %d\n' % self._block_id + 'Function: %s\n' % self._instr_to_node.function.name + 'Node: \n' +'\n'.join([str(self._instr_to_node)]) + '\nIRS: \n' +'\n'.join([str(self._instruction)]) + '"'
        else:
            label = '"BlockID: %d\n' % self._block_id + 'Node type: %s\n' % self._instruction + '"'
        return label

    # Ref: https://stackoverflow.com/a/15774013
    def __deepcopy__(self, memo):
        cls = self.__class__
        result = cls.__new__(cls)
        memo[id(self)] = result
        for k, v in self.__dict__.items():
            if k != '_instruction' and k != 'block_id' and k != '_block_id' and k!= '_instr_to_node' and k != '_new_to_old' and k!= '_origin_bb' and k!= '_call_context' and k != '_state_vars_used' and k != '_pred_vars_used':
                setattr(result, k, deepcopy(v, memo))
        
        InstrBlock.block_id += 1
        setattr(result, '_block_id', InstrBlock.block_id)        
        setattr(result, '_new_to_old', self)
        setattr(result, '_instruction', self._instruction)
        setattr(result, '_instr_to_node', self._instr_to_node)
        setattr(result, '_origin_bb', self._origin_bb)
        setattr(result, '_call_context', copy.copy(self._call_context))
        setattr(result, '_state_vars_used', copy.copy(self._state_vars_used))
        setattr(result, '_pred_vars_used', copy.copy(self._pred_vars_used))
        return result