class JsonBlock:
    block_id = 0
    
    def __init__(self, instructions, scope_str):
        self._scope = None
        self._addr = None
        self._instructions = instructions
        JsonBlock.block_id += 1
        self._block_id = JsonBlock.block_id
        self.setup(scope_str)
    
    def setup(self, scope_str):
        self.set_addr()
        self.set_scope(scope_str)

    def get_block_dict(self):
        block_dict = {}
        block_dict['scope'] = self._scope
        block_dict['addr'] = self._addr
        block_dict['instructions'] = self._instructions

        return block_dict
    
    def set_addr(self):
        self._addr = hex(self._block_id)

    def set_scope(self, scope_str):
        if scope_str == '__GLOBAL__':
            self._scope = scope_str
        
        elif scope_str == '__RANGE__':
            self._scope = scope_str
        
        #elif scope_str.startswith('__RANGE'):
            #self._scope = scope_str + str(self._addr)
        
        else:
            self._scope = scope_str        

    def __str__(self):
        label = '"BlockID: %d\n' % self._block_id + '\n'.join([str(ir) for ir in self._instructions]) + '"'
        return label