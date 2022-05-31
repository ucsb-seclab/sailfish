from slither.slithir.operations.assignment import Assignment
from slither.slithir.operations.condition import Condition
from slither.slithir.operations.binary import Binary
from slither.slithir.operations.binary import BinaryType
from slither.slithir.variables.constant import Constant
from slither.slithir.variables.temporary import TemporaryVariable
from slither.slithir.operations.member import Member
from slither.slithir.variables.reference import ReferenceVariable
from index_node import *
from state_var import *
from varnode import *
import traceback

solidity_special_vars = ['block.coinbase', 'block.difficulty', 'block.gaslimit', 'block.number', 'block.timestamp', 'msg.data', 'msg.sender', 
                        'msg.sig', 'msg.value', 'now', 'tx.gasprice', 'tx.origin']

class RangeNode:
    block_id = 0
    
    def __init__(self, variable, basic_block, value, operation):
        self._basic_block = basic_block
        self._variable = variable
        self._instructions = []
        RangeNode.block_id += 1
        self._block_id = RangeNode.block_id
        self._value = value
        self._op = operation
        self._predecessors = {}
        self._true_or_false = {}

        self.setup()
        # This is a temporary fix to remove "-" from the instructions
        # but we should tackle this elegantly later
        self._instructions = list(filter(("-").__ne__, self._instructions))

        #print("=============")
        #print(self._instructions)
        #print("=============")
    
    def setup(self):
        self.patch_constant_str_bool()
        
        #: Handle 'OR' operator
        if self._op == '=':
            if not isinstance(self._value, list):
                left_var = str(self._variable)

                if type(self._value).__name__ == 'Constant':
                    if type(self._value.type).__name__ == 'ElementaryType' and self._value.type.type == 'string':
                        right_var = "NEW_VAL unknown"

                    else:
                        right_var = str(self._value)
                else:
                    right_var = str(self._value)
                    right_var = self.process_value_expressions(right_var)
                left_var = self.process_value_expressions(left_var)
                ir = str(left_var) + " := " + str(right_var)
                self._instructions.append(ir)
            
            else:
                left_var = self._variable
                right_expression = self.process_value_expressions(self._value)
                
                if isinstance(right_expression, list):
                    for expr in right_expression:
                        ir = str(left_var) + " := " + str(expr)
                        
                        # This is a separator to let know that there exist
                        # multiple assignment instructions and they should be in different
                        # blocks
                        #if len(self._instructions) != 0:
                            #self._instructions.append("-")
                        self._instructions.append(ir)
                else:
                    ir = str(left_var) + " := " + str(right_expression)
                    self._instructions.append(ir)
                
        else:
            left_expression = self.process_value_expressions(self._variable)
            right_expression = self.process_value_expressions(self._value)
            
            if not isinstance(right_expression, list):
                if not isinstance(left_expression, list):
                    temp_var = "R" + str(TemporaryVariable(" "))
                    cond_ir = str(temp_var) + " = " + str(left_expression) + " " + self._op + " " + str(right_expression)
                    self._instructions.append(cond_ir)
                    ir = "CONDITION" + " " + str(temp_var)
                    self._instructions.append(ir)
                
                else:
                    temp_var_irs = []
                    temp_vars = []
                    for element in left_expression:
                        temp_var = "R" + str(TemporaryVariable(" "))
                        cond_ir = str(temp_var) + " = " + str(element) + " " + self._op + " " + str(right_expression)
                        temp_vars.append(temp_var)
                        temp_var_irs.append(cond_ir)
                    
                    temp_var = temp_vars[0]
                    for i in range(1, len(temp_vars)):
                        temp_var_1 = "R" + str(TemporaryVariable(" "))
                        ir = temp_var_1 + " = " + temp_var + " || " + str(temp_vars[i])
                        temp_var_irs.append(ir)
                        temp_var = temp_var_1
                    
                    ir = "CONDITION" + " " + str(temp_var)
                    temp_var_irs.append(ir)
                    self._instructions.extend(temp_var_irs)                                          

            else:
                if not isinstance(left_expression, list):
                    temp_var_irs = []
                    temp_vars = []
                    
                    for element in right_expression:
                        temp_var = "R" + str(TemporaryVariable(" "))
                        
                        if left_expression != '':
                            ir = str(temp_var) + " = " + str(left_expression) + " " + self._op + " " + str(element)
                        else:
                            ir = str(temp_var) + " = " + self._op + " " + str(element)
                        
                        temp_var_irs.append(ir)
                        temp_vars.append(temp_var)
                    
                    temp_var = temp_vars[0]
                    for i in range(1, len(temp_vars)):
                        temp_var_1 = "R" + str(TemporaryVariable(" "))
                        ir = temp_var_1 + " = " + str(temp_var) + " || " + str(temp_vars[i])
                        temp_var_irs.append(ir)
                        temp_var = temp_var_1
                    
                    ir = "CONDITION" + " " + str(temp_var)
                    temp_var_irs.append(ir)
                    self._instructions.extend(temp_var_irs)
                
                
                else:
                    temp_var_irs = []
                    temp_vars = []
                    for element in right_expression:
                        for left_element in left_expression:
                            temp_var = "R" + str(TemporaryVariable(" "))
                            ir = str(temp_var) + " = " + str(left_element) + " " + self._op + " " + str(element)
                            temp_var_irs.append(ir)
                            temp_vars.append(temp_var)
                    temp_var = temp_vars[0]
                    
                    for i in range(1, len(temp_vars)):
                        temp_var_1 = "R" + str(TemporaryVariable(" "))
                        ir = temp_var_1 + " = " + str(temp_var) + " || " + str(temp_vars[i])
                        temp_var_irs.append(ir)
                        temp_var = temp_var_1
                    
                    ir = "CONDITION" + " " + str(temp_var)
                    temp_var_irs.append(ir)
                    self._instructions.extend(temp_var_irs)

    def patch_constant_str_bool(self):
    # this patch update the str value of a bool constant in Slither IR
    # where originally it displays "True" but now "true" ("False" but now "false")
    # which corresponds with the Solidity language
        def new_str(self):
            if isinstance(self.value,bool):
                return str(self.value).lower()
            else:
                return str(self.value)
        Constant.__str__ = new_str
    
    def process_value_expressions(self, value):
        if isinstance(value, list):
            if len(value) == 1:
                result = self.process_value_expressions(value[0])
                return result
            
            elif len(value) == 3:
                lvalue = self.process_value_expressions(value[0])
                op_str = str(value[1])
                
                if op_str == 'OR':
                    self._instructions.append("-")
                    expressions = []
                    rvalue = self.process_value_expressions(value[2])
                    
                    if isinstance(lvalue, list):
                        expressions.extend(lvalue)
                    else:
                        expressions.append(str(lvalue))
                    
                    if isinstance(rvalue, list):
                        expressions.extend(rvalue)
                    
                    else:
                        expressions.append(str(rvalue))
                    
                    return expressions

                else:
                    rvalue = self.process_value_expressions(value[2])
                    
                    # Here we assume lvalue can not be a list
                    if not isinstance(rvalue, list):
                        if not isinstance(lvalue, list):
                            temp_var = str(TemporaryVariable(" "))
                            expression = temp_var + " = " + lvalue + " " + op_str + " " + rvalue
                            self._instructions.append(expression)
                            return temp_var
                        
                        else:
                            expressions = []
                            temp_vars = []
                            for element in lvalue:
                                temp_var = str(TemporaryVariable(" "))
                                ir = temp_var + " = " + str(element) + " " + str(op_str) + " " + rvalue
                                temp_vars.append(temp_var)
                                expressions.append(ir)
                            
                            self._instructions.extend(expressions)
                            return temp_vars
                    
                    else:
                        if not isinstance(lvalue, list):
                            expressions = []
                            temp_vars = []
                            for element in rvalue:
                                temp_var = str(TemporaryVariable(" "))
                                value = temp_var + " = " + str(lvalue) + " " + str(op_str) + " " + element
                                temp_vars.append(temp_var)
                                expressions.append(value)
                            self._instructions.extend(expressions)
                            return temp_vars
                        
                        else:
                            try:
                                assert not isinstance(lvalue, list), "both lvalue and rvalue can not be list"
                            except:
                                expressions = []
                                temp_vars = []
                                for element in rvalue:
                                    temp_var = str(TemporaryVariable(" "))
                                    value = temp_var + " = " + str(lvalue[0]) + " " + str(op_str) + " " + element
                                    temp_vars.append(temp_var)
                                    expressions.append(value)
                                self._instructions.extend(expressions)
                                return temp_vars

                    
            else:
                # This for array initialization, we know that
                # if it is 'initarray' it is array initialization so 
                # treat it differently
                if value[0] == 'initarray':
                    init_values = value[1:]
                    return init_values
                
                # Handle unary expressions
                elif value[0] == "~" or value[0] == '!':
                    if len(value) == 2:
                        rvalue = self.process_value_expressions(value[1])
                        
                        # If the rvalue is a list, that means the lvalue 
                        # may have multiple assignments, so we should do each individual assignments
                        # separately
                        if isinstance(rvalue, list):
                            expressions = []
                            temp_vars = []
                            
                            for element in rvalue:
                                temp_var = str(TemporaryVariable(" "))
                                value = temp_var + " = " + str(value[0]) + " " + element
                                temp_vars.append(temp_var)
                                expressions.append(value)
                            
                            self._instructions.extend(expressions)
                            return temp_vars                            
                        
                        # If the rvalue is not a list, it's simple just
                        # generate the IR instruction by simply appending the rvalue
                        # and op str
                        else:
                            
                            temp_var = str(TemporaryVariable(" "))
                            expression = temp_var + " = " + str(value[0]) + " " + str(value[1])
                            self._instructions.append(expression)
                            return temp_var                            
                    
                    else:
                        assert len(value) == 2, "value list has wrong number of elements for unary expressions!"
                    
                
                else:
                    real_count_or = value.count('OR')
                    right_count_or = (len(value) - 1) / 2
                    assert real_count_or == right_count_or, "ORed count does not match, debug!"
                    expressions = []
                    for i in range(0, len(value), 2):

                        result = self.process_value_expressions(value[i])
                        
                        if isinstance(result, list):
                            expressions.extend(result)
                        else:
                            expressions.append(str(result))
                    return expressions

        else:
            if "[" in str(value) or '.' in str(value):
                bracket_indices = self.get_array_brackets_indices(str(value))
                refvar = self.parse_value(0, str(value), len(str(value)), bracket_indices)
                return refvar

            elif type(value).__name__ == 'Constant' or isinstance(value, str):
                return str(value)
            
            else:
                return str(value)    


    def parse_value(self, start, value, end, bracket_indices):
        i = start

        if "[" in str(value[start:end]):
            refvar = ''
            
            while i < end:
                if value[i] == "[":
                    if refvar == '':
                        array_base = value[start:i]
                    
                    else:
                        array_base = refvar
                        #refvar = ''
                    
                    #array_index = value[i+1 : bracket_indices[i]]

                    if "." in str(array_base):
                        array_base = self.generate_ir_on_sep(str(array_base), ".")
                    
                    array_index = self.parse_value(i + 1, value, bracket_indices[i], bracket_indices)
                    refvar = self.generate_referncevariable_ir(array_base, array_index, '')
                    i = bracket_indices[i] + 1
                
                elif value[i] == "." and "[" not in value[i:end]:
                    if refvar == '':
                        refvar = self.generate_ir_on_sep(str(value[start:end]), ".")
                    
                    else:
                        refvar = refvar + value[i:end]
                        refvar = self.generate_ir_on_sep(str(refvar), ".")
                        
                    i = end

                else:
                    refvar = refvar + value[i]
                    i = i + 1        
            
            return refvar

        elif "." in str(value[start:end]):
            if str(value[start:end]) in solidity_special_vars:
                return str(value[start:end])
            
            else:
                refvar = self.generate_ir_on_sep(str(value[start:end]), ".")
                return refvar                         
        
        else:
            return str(value[start:end])            
                
                
    def get_array_brackets_indices(self, value):
        index_array = {}
        stack = []
        
        for i in range(0, len(value)):
            if value[i] == "[":
                stack.append(i)
            
            if value[i] == "]":
                j = stack.pop()
                index_array[j] = i

        
        return index_array
                
    def generate_referncevariable_ir(self, lvar, rvar_1, rvar_2):
        refvar = str(ReferenceVariable(""))
        if "." in rvar_1 and rvar_1 not in solidity_special_vars:
            rvar_1 = self.generate_ir_on_sep(rvar_1, ".")
        ir = refvar + " -> " + str(lvar) + "[" + str(rvar_1) + "]"
        self._instructions.append(ir)

        if rvar_2 != '':
            if "." in str(rvar_2) and rvar_2 not in solidity_special_vars:
                splits = str(rvar_2).split(".")
                for elem in splits:
                    if elem != '':
                        refvar_1 = str(ReferenceVariable(""))
                        ir = refvar_1 + " -> " + refvar + "." + elem
                        self._instructions.append(ir)
                        refvar = refvar_1
        
        return refvar      

    def generate_ir_on_sep(self, value, sep):
        splits = str(value).split(sep)
        refvar = str(ReferenceVariable(""))
        ir = refvar + " -> " + str(splits[0]) + sep + str(splits[1])
        self._instructions.append(ir)
        
        for elm in splits[2:]:
            if elm != '':
                refvar_1 = str(ReferenceVariable(""))
                ir = refvar_1 + " -> " + str(refvar) + sep + str(elm)
                self._instructions.append(ir)
                refvar = refvar_1
        
        return refvar
    
    def get_origin_state_variable(self, state_var):
        if isinstance(state_var, StateVar):
            origin_svar = state_var._state_var
            return origin_svar
        
        else:
            if isinstance(state_var, VarNode):
                field = state_var._field
                origin_svar = self.get_origin_state_variable(state_var._origin_var)

    def print_instructions(self):
        instr_list = []
        for instr in self._instructions:
            instr_list.append(str(instr))

        return instr_list
    
    def __str__(self):
        if isinstance(self._value, list):
            if isinstance(self._variable, list):
                expression = self.str_list(self._variable) + " " + str(self._op) + " " + self.str_list(self._value)
            else:
                expression = str(self._variable) + " " + str(self._op) + " " + self.str_list(self._value)
        
        else:
            if isinstance(self._variable, list):
                expression = self.str_list(self._variable) + " " + str(self._op) + " " + str(self._value)
            else:            
                expression = str(self._variable) + " " + str(self._op) + " " + str(self._value)
        
        label = expression
        return label

    def str_list(self, var_list):
        expression = ''
        for element in var_list:
            if isinstance(element, list):
                expression = expression + self.str_list(element)
            else:
                expression = expression + str(element)
        return expression

    def get_value(self, value):
        result = ''
        if isinstance(value, list):
            for element in value:
                result = result + self.get_value(element)
        else:
            result = result + str(value)
        return result

    def print_conditional_value_range(self, graph):
        preconditions = []
        predecessors = list(graph.predecessors(self))

        for predecessor in predecessors:
            preconditions.append(str(predecessor))
        
        if len(preconditions) == 0:
            preconditions.append(True)
        
        return preconditions
    
    # Ref: https://stackoverflow.com/a/15774013
    def __deepcopy__(self, memo):
        cls = self.__class__
        result = cls.__new__(cls)
        memo[id(self)] = result
        for k, v in self.__dict__.items():
            if k != '_basic_block' and k!= '_variable' and k != 'block_id' and k != '_block_id' and k!= '_value' and k != '_instructions'\
                and k != '_predecessors' and k != '_true_or_false':
                setattr(result, k, deepcopy(v, memo))
        
        RangeNode.block_id += 1
        setattr(result, '_block_id', RangeNode.block_id)
        setattr(result, '_value', self._value)
        setattr(result, '_basic_block', self._basic_block)
        setattr(result, '_variable', self._variable)
        setattr(result, '_instructions', self._instructions)
        setattr(result, '_true_or_false', self._true_or_false)
        setattr(result, '_predecessors', self._predecessors)
        return result
