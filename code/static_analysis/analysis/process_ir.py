import slither
import shutil
import os
import sys
import pydot
import glob
import traceback
import json
import networkx as nx
from collections import defaultdict
import matplotlib.pyplot as plt
from varnode import *
from collections import defaultdict
from slither.slithir.variables.constant import Constant
from slither.core.declarations.solidity_variables import SolidityFunction
from slither.slithir.operations.binary import BinaryType
from slither.slithir.operations.unary import UnaryType
from slither.core.declarations.function import Function
from slither.core.variables.variable import Variable
from slither.printers.call.call_graph import *
from slither.core.solidity_types.elementary_type import *
from slither.core.solidity_types.elementary_type import ElementaryType, ElementaryTypeName
from slither.core.cfg.node import NodeType
from cfg import *
from basic_block import *
from instr_block import *
from icfg import *
from varnode import *
import copy
from sdg import *
from util import *
from value_node import *
from range_node import *
from state_var import *
from index_node import *
import global_imports
import traceback

# Improvements: Probably we may need to field sensitive
bool_type = ElementaryType('bool')
BALANCE = Constant('balance')
LENGTH = Constant('length')
int_type = ElementaryType('int')

TUPLE_TYPES = []

CONSTANT_TYPES = ['int', 'str', 'Constant']
VARIBLE_TYPES = ['StateVariableSolc', 'LocalVariableSolc']
SOLIDITY_VARS = ['SolidityVariableComposed', 'SolidityVariable']
JOINOP = [BinaryType.OROR, BinaryType.ANDAND]
ARITHMETICOP = [BinaryType.POWER, BinaryType.MULTIPLICATION, BinaryType.DIVISION, BinaryType.MODULO, BinaryType.ADDITION, BinaryType.SUBTRACTION, 
                BinaryType.LEFT_SHIFT, BinaryType.RIGHT_SHIFT, BinaryType.AND, BinaryType.CARET, BinaryType.OR]
UNARYOP = [UnaryType.BANG, UnaryType.TILD]
CONDITIONOP = [BinaryType.LESS, BinaryType.GREATER, BinaryType.LESS_EQUAL, BinaryType.GREATER_EQUAL, BinaryType.EQUAL, BinaryType.NOT_EQUAL]
DEBUG = 0
# Need to add support for all these operations
slithir_operations = ["assignment", "balance", "binary ", "call.py", "condition", "delete.py ", "event_call	", "high_level_call", "index", "init_array", 
"internal_call", "internal_dynamic", "length", "library_call", "low_level_call", "lvalue", "member", "new_array", "new_contract", 
"new_elementary_type", "new_structure", "nop", "operation", "phi", "phi_callback", "push.py", "return_operation", "send.py", 
"solidity_call.py", "transfer", "type_conversion.", "unary ", "unpack"]



# This function returns the corresponding state var object given StateVariableSolc
def get_state_var_obj(log, var):
    if var in SDG.map_svars_to_sobj.keys():
        return SDG.map_svars_to_sobj[var]
    
    else:
        if DEBUG:
            log.info("This should be implemented, this is for structures!")
            sys.exit(1)
        else:
            pass

# SlithIR is very inconsistant. It has two different API's for getting return values
# function.returns and function.return_values. They both can be different sometimes (which is weird)
# In addition, return_ir's can contain values whoch is absent in both function.returns and function.return_values
# So, we need combine all of them, so that we don't miss any return values        
def get_return_values(log, vrg, cfg_obj):
    returns_values = {}
    processsed_values = []
    i = 0
    
    # This is for multiple return IRs and each return IR 
    # can return multiple values, store them in a disctionary of lists
    for return_ir in cfg_obj._returns_irs:
        returns_values[str(i)] = return_ir.used
        processsed_values.extend(return_ir.used)
        i = i + 1
    
    for return_value in cfg_obj._function.returns:
        if return_value not in processsed_values:
            if return_value in CFG.lvalue_vars.keys():
                if str(i) not in returns_values.keys():
                    returns_values[str(i)] = []
                
                returns_values[str(i)].append(return_value)
    
    cfg_obj._return_values = returns_values
    return returns_values

def is_tainted(log, value, cfg_obj, taint_granularity):
    taint_flag = slither.analyses.data_dependency.data_dependency.is_tainted(value, taint_granularity)    
    
    if taint_flag:
        return True
    
    else:
        if type(value).__name__ in CONSTANT_TYPES or type(value).__name__ in SOLIDITY_VARS:
            return False
        
        else:
            all_state_variables = set(cfg_obj._function.contract.state_variables)
            state_variables_written = set(cfg_obj._function.contract.all_state_variables_written)
            state_variables_not_writtten = all_state_variables - state_variables_written
            dependent_vars = list(slither.analyses.data_dependency.data_dependency.get_dependencies(value, taint_granularity))
            dependent_vars_copy = list(set(dependent_vars) - state_variables_not_writtten)

            if len(dependent_vars_copy) != len(dependent_vars):
                return True
            else:
                if DEBUG:
                    log.warning("Check before returning False!")
                return False

def is_var_node_present(log, svar, field):
    vnode = None
    
    for var_node in SDG.var_node_list:
        if var_node._origin_var == svar and var_node._field == field:
            vnode = var_node
            break
    
    return vnode

def perform_arithmetic_op(arg1, arg2, op):
    if op == '+':
        return arg1 + arg2
    if op == '-':
        return arg1 - arg2
    if op == '*':
        return arg1 * arg2
    if op == '**':
        return arg1 ** arg2
    if op == '/':
        return arg1 / arg2
    if op == '<<':
        return arg1 << arg2
    if op == '>>':
        return arg1 >> arg2
    if op == '%':
        return arg1 % arg2
    if op == '^':
        return arg1 ^ arg2
    if op == "|":
        return arg1 | arg2
    if op == '&':
        return arg1 & arg2

def process_left_or_right_variable(log, vrg, variable, cfg_obj, call_type, instr, parameters=[], parent=None, node=None, graph=None):
    res_var = None

    if type(variable).__name__ == 'TemporaryVariable':
        lvar, rvar, type_str = process_temporary_variable(log, vrg, variable, cfg_obj, call_type, parameters, parent, node, graph)
        if lvar is not None:
            res_var = lvar
        if rvar is not None:
            res_var = rvar
    
    else:
        if type(variable).__name__ == 'StateVariableSolc':
            res_var = get_state_var_obj(log, variable)
            
            if res_var in vrg._constant_state_vars.keys():
                res_var = vrg._constant_state_vars[res_var]                    
        
        elif type(variable).__name__ in SOLIDITY_VARS:
            res_var = variable
        
        elif type(variable).__name__ == 'Constant':
            res_var = variable

        elif type(variable).__name__ == 'LocalVariableSolc':
            
            if variable in parameters:
                if is_tainted(log, variable, cfg_obj, cfg_obj._function._contract):
                    res_var = 'U'
                
                else:
                    if call_type == 'R':
                        res_var = variable                    
                    
                    else:
                        res_var = track_predecessor_assignments(log, vrg, variable, cfg_obj, call_type, parameters, parent)
            
            else:
                value_list = []
                
                if call_type == 'R':
                    parent =  cfg_obj._ir_to_block[instr]
                
                for lvar, rvar, type_str in process_local_variable(log, vrg, cfg_obj, instr, call_type, variable, parameters, parent, node, graph):
                    if len(value_list) >= 1:
                        value_list.append('OR')

                    if isinstance(lvar, list):
                        if len(lvar) != 0:
                            if len(lvar) <= 1:
                                value_list.extend(lvar)
                            
                            else:                          
                                value_list.append(lvar)
                    else:
                        value_list.append(lvar)

                res_var = value_list

        elif type(variable).__name__ == 'ReferenceVariable':
            res_var = get_origin_variable_from_refvariable(log, vrg, instr, variable, cfg_obj, call_type, parent)
            res_var = replace_state_var_with_index_node(res_var, variable, vrg)
        
        elif type(variable).__name__ == 'LocalVariableInitFromTupleSolc':
            res_var = process_localVariableInitFromTupleSolc(log, vrg, cfg_obj, instr, call_type, variable, parameters, parent)
        
        elif type(variable).__name__ == 'TupleVariable':
            s_lvar, s_rvar, type_str = process_tuple_variable(log, vrg, cfg_obj, instr, call_type, variable, parameters, parent)
            if 'U' in s_lvar:
                s_lvar = 'U'
            res_var = s_lvar

        else:
            log.warning("What can be there in the else part")
            sys.exit(1)

    return res_var

# This function tracks the origin of callee function parameters in the callers
def track_predecessor_assignments(log, vrg, variable, cfg_obj, call_type, parameters, parent=None):
    value_list = []
    res_var = None
    #try:
    all_predecessors = vrg._predecessors[cfg_obj._function]
    
    if len(all_predecessors) == 0:
        value_list.append('U')
    
    for pred in all_predecessors:
        pred_cfg_obj = CFG.function_cfg[pred]
        ir_calls = list(pred_cfg_obj._ircall_to_bb.keys())
        ir_calls = ir_calls + copy.copy(pred_cfg_obj._modifier_ir_calls)

        call_args = None
        
        for ir_call in ir_calls:
            if ir_call.function == cfg_obj._function:
                call_args = ir_call.arguments
                break
        
        ## Call args can be None because of base constructor 
        ## within a constructor, slither do not align the base constructor calls
        ## within the rest of function in node-son manner. So, we can not have that information
        ## in the cfg, so, we just return 'U'
        if call_args == None:
            value_list = ['U']
        
        else:
            v_index = parameters.index(variable)
            source_arg = call_args[v_index]


            res_var = process_left_or_right_variable(log, vrg, source_arg, pred_cfg_obj, call_type, ir_call, pred.parameters, parent)
            if isinstance(res_var, list) and len(res_var) == 1:
                value_list.extend(res_var)
            else:
                if len(value_list) >= 1:
                    value_list.append('OR')
                value_list.append(res_var)

    return value_list

# This function processes any instruction involving temp var as lvalue
def process_temporary_variable(log, vrg, variable, cfg_obj, call_type=None, parameters=[], parent=None, node=None, graph=None):
    instrs = CFG.lvalue_vars[variable]

    s_lvar = None
    s_rvar = None
    type_str = None

    # This should not happen, since we can't trust SlithIR, so let's be conservative
    try:
        assert len(instrs) == 1, "Uexpected, need to handle this!"
    except AssertionError as error:
        log.error("instrs length more than 1")
        sys.exit(1)

    instr = instrs[0]
    s_lvar, s_rvar, type_str = instruction_handler(log, vrg, instr, cfg_obj, call_type, parameters, parent, node, graph)
        
    return s_lvar, s_rvar, type_str


def instruction_handler(log, vrg, instr, cfg_obj, call_type=None, parameters=[], parent=None, node=None, graph=None):
    s_lvar = None
    s_rvar = None
    type_str = None
    
    if type(instr).__name__ == 'Binary':
        s_lvar, s_rvar, type_str = handle_binary_statement(log, vrg, instr, cfg_obj, call_type, parameters, parent, node, graph)

    elif type(instr).__name__ == 'Unary':
        s_lvar, s_rvar, type_str = handle_unary_statement(log, vrg, instr, cfg_obj, call_type, parameters, parent, node, graph)

    #: Need to implement
    elif type(instr).__name__ == 'NewStructure':
        s_lvar = process_new_structure_statement(log, vrg, instr, parameters, cfg_obj, parent)
        s_rvar = None
        type_str = 'new_s'
    
    elif type(instr).__name__ == 'Unpack':
        if hasattr(instr, 'tuple'):
            tuple_var = instr.tuple
            lvar, rvar, t_str = process_tuple_variable(log, vrg, cfg_obj, instr, call_type, tuple_var, parameters, parent)
            index = instr.index
            try:
                s_lvar = lvar[index]
            
            except:
                log.warning("This can only happen due to slither insanity, where slither does not capture the returned tuple properly, we ignore it for now!")
                sys.exit(1)

        else:
            log.warning("For Unpack can there anything else than tuple!")
            sys.exit(1)
    elif type(instr).__name__ == 'TypeConversion':
        var_right = instr.read[0]
        s_lvar = process_left_or_right_variable(log, vrg, var_right, cfg_obj, call_type, instr, parameters, parent, node, graph)

    elif type(instr).__name__ == 'Assignment':
        s_lvar = process_left_or_right_variable(log, vrg, instr.rvalue, cfg_obj, call_type, instr, parameters, parent, node, graph)

    elif type(instr).__name__ == 'HighLevelCall':
        s_lvar, s_rvar, type_str = process_high_level_call(log, vrg, instr, cfg_obj, call_type, parameters, parent)                       
    
    elif type(instr).__name__ == 'LibraryCall' or type(instr).__name__ == 'InternalCall':
        s_lvar, s_rvar, type_str = process_internal_call(log, vrg, instr, cfg_obj, call_type, parameters, parent)
    
    elif type(instr).__name__ == 'Send' or type(instr).__name__ == 'LowLevelCall' or type(instr).__name__ == 'Transfer':
        s_lvar = 'U'
    
    elif type(instr).__name__ == 'SolidityCall':
        s_lvar = 'U'
    
    elif type(instr).__name__ == 'NewElementaryType' or type(instr).__name__ == 'NewArray' or type(instr).__name__ == 'NewContract':
        s_lvar = 'U'
    
    elif type(instr).__name__ == 'Push':
        s_lvar = process_left_or_right_variable(log, vrg, instr.value, cfg_obj, call_type, instr, parameters, parent, node, graph)

    elif type(instr).__name__ == 'Length':
        s_lvar = process_length_ir(log, vrg, instr, instr.value, cfg_obj, call_type, parent)
    
    elif type(instr).__name__ == 'InitArray':
        s_lvar = instr.init_values

    else:
        log.warning("Temp variable instruction not handled!")
        sys.exit(1)
    return s_lvar, s_rvar, type_str


def process_push_operation(log, vrg, var_right, cfg_obj, call_type, instr, parameters, parent, node, graph):
    s_lvar = None
    s_rvar = None
    type_str = None
    push_lvalue = process_left_or_right_variable(log, vrg, instr.lvalue, cfg_obj, call_type, instr, parameters, parent)
    push_value = process_left_or_right_variable(log, vrg, instr.value, cfg_obj, call_type, instr, parameters, parent)

    if push_value == 'U':
        s_lvar = 'U'
    
    else:
        s_lvar = push_value

    return s_lvar, s_rvar, type_str

def process_new_structure_statement(log, vrg, svar_assign_ir, parameters, cfg_obj, parent=None):
    arguments = svar_assign_ir.arguments
    results = []
    
    for i in range(0, len(arguments)):
        result = process_left_or_right_variable(log, vrg, arguments[i], cfg_obj, '', svar_assign_ir, parameters, parent)
        results.append(result)
    
    return results

def handle_unary_statement(log, vrg, instr, cfg_obj, call_type, parameters=[], parent=None, node=None, graph=None):
    s_lvar = None
    s_rvar = None
    type_str = None
    rvalue = instr.rvalue
    type_str = instr.type_str

    s_lvar = process_left_or_right_variable(log, vrg, rvalue, cfg_obj, call_type, instr, parameters, parent, node, graph)

    
    if isinstance(s_lvar, StateVar):
        if s_lvar in vrg._constant_state_vars.keys():
            s_lvar = vrg._constant_state_vars[s_lvar]
    
    if graph is not None:
        # This can happen because say the condition is TMP_1 = REF_0 == 0, CONDITION !TMP_1, In this case
        # during binary state ment we already create a range node and add an edge. But, this wrong,
        # Since the actual node should be created here, not in handle_binary_statement, hence we remove 
        # that first
        if isinstance(s_lvar, RangeNode):
            graph.remove_edge(s_lvar, node)

        range_node = RangeNode('', parent, s_lvar, type_str)

        graph.add_edge(range_node, node)
        s_lvar = range_node
        type_str = None
    else:
        res = []
        res.append(type_str)
        res.append(s_lvar)
        s_lvar = res
        s_rvar = None
        type_str = None

    return s_lvar, s_rvar, type_str

def handle_binary_statement(log, vrg, instr, cfg_obj, call_type, parameters=[], parent=None, node=None, graph=None):
    s_lvar = None
    s_rvar = None
    type_str = None

    var_left = instr.variable_left
    var_right = instr.variable_right
    type_str = instr.type_str

    s_lvar = process_left_or_right_variable(log, vrg, var_left, cfg_obj, call_type, instr, parameters, parent, node, graph)
    s_rvar = process_left_or_right_variable(log, vrg, var_right, cfg_obj, call_type, instr, parameters, parent, node, graph)

    if isinstance(s_lvar, StateVar):
        if s_lvar in vrg._constant_state_vars.keys():
            s_lvar = vrg._constant_state_vars[s_lvar]

    if isinstance(s_rvar, StateVar):
        if s_rvar in vrg._constant_state_vars.keys():
            s_rvar = vrg._constant_state_vars[s_rvar]

    if BinaryType.get_type(type_str) in JOINOP:

        if call_type == 'R':
            true_value = Constant('True', bool_type)
            false_value = Constant('False', bool_type)
            s_lvar = [true_value, 'OR', false_value]
            s_rvar = None
            type_str = None
        
        else:
            if s_rvar == 'U' or s_lvar == 'U':
                if s_lvar == 'U' and s_rvar == 'U':
                    s_lvar = 'U'
                    s_rvar = None
                    type_str = None
                
                else:
                    if s_lvar != 'U':
                        s_rvar = None
                        type_str = None
                    
                    else:
                        s_lvar = s_rvar
                        s_rvar = None
                        type_str = None 
            else:
                s_lvar = create_rangenode_if_not_exists(log, vrg, s_lvar, cfg_obj, call_type, parameters, parent, node, graph)
                s_rvar = create_rangenode_if_not_exists(log, vrg, s_rvar, cfg_obj, call_type, parameters, parent, node, graph)
                
                join_list = []
                join_list.append(s_lvar)
                join_list.append(type_str)
                join_list.append(s_rvar)
                node._predecessors[parent] = join_list
                s_lvar = join_list
                s_rvar = None
                type_str = None

    
    elif BinaryType.get_type(type_str) in CONDITIONOP:
        
        if call_type == 'R' or call_type == '':
            true_value = Constant('True', bool_type)
            false_value = Constant('False', bool_type)
            s_lvar = [true_value, 'OR', false_value]
            s_rvar = None
            type_str = None
        
        else:
            if isinstance(s_lvar, list):
                if 'U' in s_lvar:
                    s_lvar = 'U'
                    s_rvar = None
                    type_str = None

            if isinstance(s_rvar, list):
                if 'U' in s_rvar:       
                    s_lvar = 'U'
                    s_rvar = None
                    type_str = None
            #else:
            if s_lvar == 'U' or s_rvar == 'U':
                s_lvar = 'U'
                s_rvar = None
                type_str = None
        
            else:
                if isinstance(s_lvar, RangeNode):
                    graph.remove_edge(s_lvar, node)
                range_node = RangeNode(s_lvar, parent, s_rvar, type_str)
                graph.add_edge(range_node, node)

                s_lvar = range_node
                s_rvar = None
                type_str = None

    elif BinaryType.get_type(type_str) in ARITHMETICOP:
        if type(s_lvar).__name__ == 'Constant' and type(s_rvar).__name__ == 'Constant':
            s_lvar = str(s_lvar)
            s_rvar = str(s_rvar)

            if "." in s_lvar:
                s_lvar = float(s_lvar)
            else:
                s_lvar = int(s_lvar)

            if "." in s_rvar:
                s_rvar = float(s_rvar)
            else:
                s_rvar = int(s_rvar)

            s_lvar = perform_arithmetic_op(s_lvar, s_rvar, type_str)
            s_lvar = int(s_lvar)
            s_lvar = Constant(str(s_lvar), int_type)
            s_rvar = None
            type_str = None
        
        else:
            s_lvar, s_rvar, type_str = handle_non_constant_binary_op(log, vrg, s_lvar, s_rvar, type_str)
         
    else:
        log.warning("Are there any other types of operations exist!")
        sys.exit(1)

                    
    return s_lvar, s_rvar, type_str

def create_rangenode_if_not_exists(log, vrg, var_obj, cfg_obj, call_type, parameters, parent, node, graph):
    if isinstance(var_obj, RangeNode):
        return var_obj
    
    else:
        if isinstance(var_obj, VarNode) or isinstance(var_obj, IndexNode) or isinstance(var_obj, StateVar):
            range_node = RangeNode(var_obj, parent, "true", "==")
            graph.add_edge(range_node, node)
            return range_node
        
        else:
            if isinstance(var_obj, list):
                if '||' in var_obj or '&&' in var_obj:
                    return var_obj
                
                else:
                    range_node = RangeNode("true", parent, "", "")
                    graph.add_edge(range_node, node)
                    return range_node
            else:
                log.warning("What else can be a single argument!")
                sys.exit(1)           


def handle_non_constant_binary_op(log, vrg, s_lvar, s_rvar, type_str):
    if isinstance(s_lvar, list) or isinstance(s_rvar, list):
        val_list = analyze_vars(s_lvar, s_rvar)
        if 'U'in val_list:
            s_lvar = 'U'
            s_rvar = None
            type_str = None
        else:
            op_list = []
            if isinstance(s_lvar, list) and len(s_lvar) == 0:
                s_lvar = 'U'
            
            if isinstance(s_rvar, list) and len(s_rvar) == 0:
                s_rvar = 'U'
            
            op_list.append(s_lvar)
            op_list.append(type_str)
            op_list.append(s_rvar)
            if 'U' in op_list:
                op_list = 'U'
            s_rvar = None
            type_str = None                    

    else:
        if s_lvar is not None and s_rvar is not None:
            if s_lvar == 'U' or s_rvar == 'U':
                s_lvar = 'U'
                s_rvar = None
                type_str = None
            
            else:
                op_list = []
                op_list.append(s_lvar)
                op_list.append(type_str)
                op_list.append(s_rvar)
                s_lvar = op_list
                s_rvar = None
                type_str = None
        
        else:
            res_var = s_lvar if s_lvar is not None else s_rvar
            s_lvar = res_var
            s_rvar = None
            type_str = None  

    return s_lvar, s_rvar, type_str

def analyze_vars(lvar, rvar):
    val_list = []
    if lvar is not None:
        if isinstance(lvar, list):
            val_list.extend(lvar)
        else:
            val_list.append(lvar)
    if rvar is not None:
        if isinstance(rvar, list):
            val_list.extend(rvar)
        else:
            val_list.append(rvar)    
    
    return val_list

def process_internal_call(log, vrg, instr, cfg_obj, call_type, parameters, parent=None):
    s_lvar = None
    s_rvar = None
    type_str = None
    flag = False
    

    callee  = instr.function

    caller_arguments = instr.arguments
    ## Handle callee return summaries
    return_list = map_callee_returns_to_caller_args(log, vrg, callee, caller_arguments, call_type, parent)
    return_values = CFG.function_cfg[callee]._return_values

    # Arguments of the call can be temporary variables, constants, state vars or reference vars. 
    # We need to get the actual source of the var
    

    temp_arr = []
    res = []

    # This is for multiple return
    for num in return_values:
        values = return_values[num]
        
        v_list = []
        
        # This is for single return
        for rvalue in values:
            if type(rvalue).__name__ == 'Constant':
                v_list.append([rvalue])
            
            else:
                if return_list.get(rvalue) == None:
                    return_list[rvalue] = ['U']

                value = return_list[rvalue]
                result = get_call_arguments_origin(log, vrg, value, instr, parameters, cfg_obj, call_type, parent)
                
                if 'U' in result:
                    v_list.append('U')
                
                else:
                    v_list.append(result)
                
                if type(rvalue).__name__ == 'TupleVariable' and isinstance(rvalue.type, list):
                    length = len(rvalue.type)
                    cur_len = len(v_list)
                    
                    if cur_len < length:
                        v_list = v_list * length
        #if len(v_list) == 1:
            #v_list = v_list[0]
        
        if len(v_list) == 0:
            v_list = []
        
        if len(v_list) != 0:
            temp_arr.append(v_list)
    
    res = []
    
    if len(temp_arr) > 0:
        if len(temp_arr) == 1:
            res = temp_arr[0]
        
        else:
            #try:
            for col in range(0, len(temp_arr[0])):
                ored_val = []
                
                for row in range(0, len(temp_arr)):
                    if len(ored_val) > 0:
                        ored_val.append('OR')

                    ored_val.append(temp_arr[row][col])


                    
                if 'U' in ored_val:
                    ored_val = ['U']
                
                res.append(ored_val)


    s_lvar = res
    # This can can if the internal function returns a value
    # which is assigned through assemly operations, so in that that
    # case we assume this as U
    if len(s_lvar) == 0:
        length = 1
        
        if return_values.get('0') != None:
            returns = return_values['0']
            length = len(returns)
        else:
            r_length = len(callee._returns)
            if r_length != 0:
                length = r_length

        s_lvar = ['U'] * length
    return s_lvar, s_rvar, type_str 


def process_high_level_call(log, vrg, instr, cfg_obj, call_type, parameters, parent=None):
    s_lvar = None
    s_rvar = None
    type_str = None

    call_destination = instr.destination
    call_arguments = instr.arguments             
    
    if is_tainted(log, call_destination, cfg_obj, cfg_obj._function.contract):
        s_lvar = 'U'
    
    else:
        taint_flag = False
        
        if call_destination in CFG.function_cfg.keys() and len(CFG.function_cfg[call_destination]._cfg.nodes) > 1:
            s_lvar, s_rvar, type_str = process_internal_call(log, vrg, instr, call_type, parameters, parent)
        
        else:
            for argument in call_arguments:
                if is_tainted(log, argument, cfg_obj, cfg_obj._function.contract):
                    taint_flag = True
                    break
            
            if taint_flag == True:
                s_lvar = 'U'
            
            else:
            # : Need to modify this part whether call destination is part of the contract or not
                s_lvar = 'U'
    
    return s_lvar, s_rvar, type_str                

def process_tuple_variable(log, vrg, cfg_obj, instruction, call_type, variable, parameters, parent=None):
    instrs = CFG.lvalue_vars[variable]

    try:
        assert len(instrs) == 1, "need to handle this!"
    except AssertionError as error:
        log.warning("instrs length for tuple variable as a lvalue more than 1")
        sys.exit(1)
    
    s_lvar = None
    s_rvar = None
    type_str = None

    for instr in instrs:
        if type(instr).__name__ == 'HighLevelCall':
            s_lvar, s_rvar, type_str = process_high_level_call(log, vrg, instr, cfg_obj, call_type, parameters, parent)
            s_lvar = parse_tuple_vars(log, vrg, cfg_obj, instr, call_type, variable, s_lvar, parameters)
        
        elif type(instr).__name__ in ['InternalCall', 'LibraryCall']:
            s_lvar, s_rvar, type_str = process_internal_call(log, vrg, instr, cfg_obj, call_type, parameters, parent)
            s_lvar = parse_tuple_vars(log, vrg, cfg_obj, instr, call_type, variable, s_lvar, parameters)

        elif type(instr).__name__ == 'LowLevelCall' or type(instr).__name__ == 'SolidityCall':
            s_lvar = parse_tuple_vars(log, vrg, cfg_obj, instr, call_type, variable, s_lvar, parameters)
        
        else:
            log.warning("Any other types of operation involving tuples!")
            sys.exit(1)

        return s_lvar, s_rvar, type_str

def parse_tuple_vars(log, vrg, cfg_obj, instruction, call_type, variable, s_lvar, parameters, parent=None):
    new_s_lvar = []
    tuple_type = variable.type
    tuple_dict = {}

    # Findout whether tuple is a list and how many arguments it has and type of each one of them
    if isinstance(tuple_type, list):
        no_of_args = 0
        tuple_type = variable.type

        for i in range(0, len(tuple_type)):
            if type(tuple_type[i]).__name__ == 'ArrayType':
                try:
                    length = tuple_type[i].length.value
                except:
                    log.warning("Slither is just afraid of tuples!")
                    sys.exit(1)

                if isinstance(length, str):
                    length = int(length)
                    no_of_args += length
                    tuple_dict[i] = length

                else:
                    log.warning("Unexpected, probably needs debugging")
                    sys.exit(1)

            elif type(tuple_type[i]).__name__ == 'ElementaryType':
                tuple_dict[i] = 1
                no_of_args += 1

            # This is slither ducktaping
            elif tuple_type[i] in ElementaryTypeName:
                tuple_dict[i] = 1
                no_of_args += 1

            elif type(tuple_type[i]).__name__ == 'UserDefinedType':
                tuple_dict[i] = 1
                no_of_args += 1

            else:
                log.warning('Some thing else in tuple type')
                sys.exit(1)

    else:
        tuple_dict[0] = 1
        no_of_args = 1

    if not isinstance(s_lvar, list):
        v_list = []

        for i in range(0, len(tuple_dict.keys())):
            if tuple_dict[i] > 1:
                new_s_lvar = [s_lvar] * tuple_dict[i]

            else:
                new_s_lvar = s_lvar

            v_list.append(new_s_lvar)

        s_lvar = v_list

    else:
        if len(s_lvar) == 0:
            v_list = []
            for i in range(0, len(tuple_dict.keys())):
                if tuple_dict[i] > 1:
                    new_s_lvar = ['U'] * tuple_dict[i]
                else:
                    new_s_lvar = s_lvar

                v_list.append(new_s_lvar)
            s_lvar = v_list

        else:
            if no_of_args != len(s_lvar):
                res = ['U'] * (no_of_args - len(s_lvar))
                s_lvar.append(res)

            else:
                v_list = []

                for i in range(0, len(tuple_dict.keys())):
                    if tuple_dict[i] > 1:
                        new_s_lvar = []
                        for j in range(0, tuple_dict[i]):
                            new_s_lvar.append(s_lvar[i + j][0])
                    else:
                        new_s_lvar = s_lvar[i]

                    v_list.append(new_s_lvar)

                s_lvar = v_list
    return s_lvar

def check_eligible_instr(log, vrg, cfg_obj, base_instr, lvalue_instr):
    lvalue_bb = cfg_obj._ir_to_block[lvalue_instr]
    base_instr_bb = cfg_obj._ir_to_block[base_instr]
    all_predecessor_bbs = cfg_obj._all_predecessors[base_instr_bb]
    
    if lvalue_bb == base_instr_bb:
        bb_instructions = lvalue_bb._instructions

        if bb_instructions.index(lvalue_instr) < bb_instructions.index(base_instr):
            return True
    
    elif lvalue_bb in all_predecessor_bbs:
        return True
    
    return False

def do_flow_sensitive_analysis(log, vrg, cfg_obj, instruction, call_type, variable, parameters, parent, node=None, graph=None):
    containing_bb = cfg_obj._ir_to_block[instruction]
    all_predecessor_bbs = cfg_obj._all_predecessors[containing_bb]
    
    lvalue_bbs = {}
    eligible_instrs = []
    for instr in CFG.lvalue_vars[variable]:
        bb = cfg_obj._ir_to_block[instr]
        
        if check_eligible_instr(log, vrg, cfg_obj, instruction, instr) == True:
            if lvalue_bbs.get(bb) == None:
                lvalue_bbs[bb] = []
            lvalue_bbs[bb].append(instr)
            eligible_instrs.append(instr)
            eligible_instrs = list(set(eligible_instrs))
    
    pred_lvalue_bbs = list(set(list(lvalue_bbs.keys())).intersection(set(all_predecessor_bbs)))    
    result = []
    
    if len(eligible_instrs) == 1:
        target_instr = eligible_instrs[0]
        
        if vrg._lvalue_equals.get(target_instr) == None:
            s_lvar, s_rvar, type_str = instruction_handler(log, vrg, target_instr, cfg_obj, call_type, parameters, parent, node, graph)
            vrg._lvalue_equals[target_instr] = s_lvar
        result =  vrg._lvalue_equals[target_instr]
    
    elif len(eligible_instrs) > 1:
        if lvalue_bbs.get(containing_bb) != None:
            last_index = containing_bb._instructions.index(instruction) - 1
            
            for i in range(last_index, -1, -1):
                target_instr = containing_bb._instructions[i]
                
                if target_instr in lvalue_bbs[containing_bb]:
                    if vrg._lvalue_equals.get(target_instr) == None:
                        s_lvar, s_rvar, type_str = instruction_handler(log, vrg, target_instr, cfg_obj, call_type, parameters, parent, node, graph)
                        vrg._lvalue_equals[target_instr] = s_lvar
                    
                    result = vrg._lvalue_equals[target_instr]
                    break
        
        elif len(pred_lvalue_bbs) != 0:
            result = find_target_basic_block(log, vrg, cfg_obj, containing_bb, pred_lvalue_bbs, lvalue_bbs, call_type, parameters, parent, node, graph)
        
        else:
            log.warning("This should not happen, if happens then it's a bug!")
            sys.exit(1)
    
    else:
        log.warning("No lvalue eligible assignment, is this some bug!")
        result = 'U'
        #sys.exit(1)
    if is_unconstrained(result):
        result = 'U'
    
    return result

def is_unconstrained(result):
    if isinstance(result, list):
        if 'U' in result:
            return True
    else:
        if result == 'U':
            return True
    return False

def find_target_basic_block(log, vrg, cfg_obj, basic_block, pred_lvalue_bbs, lvalue_instr_to_bbs, call_type, parameters, parent, node=None, graph=None):
    result = []
    
    # This is for backedge detection
    if basic_block in vrg.local_visit_stack:
        common_cycle_preds = list(set(pred_lvalue_bbs).intersection(vrg.local_visit_stack))
        if len(common_cycle_preds) == 0:
            result = []
        
        else:
            result = 'U'
        return result
    
    else:
        vrg.local_visit_stack.append(basic_block)

    predecessors = list(cfg_obj._cfg.predecessors(basic_block))
    for predecessor in predecessors:
        if predecessor in pred_lvalue_bbs:
            instrs_list = lvalue_instr_to_bbs[predecessor]
            min_index = predecessor._instructions.index(instrs_list[0])
            
            for instr in instrs_list:
                cur_index = predecessor._instructions.index(instr)
                
                if cur_index <= min_index:
                    min_index = cur_index
            
            target_instr = predecessor._instructions[min_index]
            if vrg._lvalue_equals.get(target_instr) == None:
                s_lvar, s_rvar, type_str = instruction_handler(log, vrg, target_instr, cfg_obj, call_type, parameters, parent, node, graph)
                vrg._lvalue_equals[target_instr] = s_lvar
            

            if is_unconstrained(vrg._lvalue_equals[target_instr]):
                result = ['U']
            
            elif is_empty(vrg._lvalue_equals[target_instr]) == False:
                if len(result) > 0:
                    result.append('OR')
                
                result.append(vrg._lvalue_equals[target_instr])
        
        else:
            all_preds = cfg_obj._all_predecessors[predecessor]
            common_blocks = list(set(all_preds).intersection(set(pred_lvalue_bbs)))
            
            if len(common_blocks) != 0:
                value = find_target_basic_block(log, vrg, cfg_obj, predecessor, pred_lvalue_bbs, lvalue_instr_to_bbs, call_type, parameters, parent, node, graph)
                
                if is_unconstrained(value):
                    result = ['U']
                
                elif is_empty(value) == False:
                    if len(result) > 0:
                        result.append('OR')
                    
                    result.append(value)
    
    vrg.local_visit_stack.remove(basic_block)
    return result

def is_empty(value_list):
    if isinstance(value_list, list) and len(value_list) == 0:
        return True
    
    return False

def process_local_variable(log, vrg, cfg_obj, instruction, call_type, variable, parameters, parent=None, node=None, graph=None):
    s_lvar = None
    s_rvar = None
    type_str = None
    instructions = []
    
    #loop_itr = 0
    # This means that there is a back edge,
    # hence empty result should be returned
    if instruction in vrg.local_visit_stack:
        s_lvar = []
        yield s_lvar, s_rvar, type_str 

    else:            
        
        if CFG.lvalue_vars.get(variable) == None:
            modifiers = cfg_obj._function.modifiers
            parameter_m = []
            
            for modifier in modifiers:
                parameter_m.extend(modifier.parameters)
            
            if variable in parameter_m:
                s_lvar = 'U'
                instrs = []
            
            elif variable in parameters:
                s_lvar = process_left_or_right_variable(log, vrg, variable, cfg_obj, call_type, instruction, parameters, parent, node, graph)
            
            else:
                s_lvar = 'U'
                log.warning("Can there be this kind of variables")

        else:
            if instruction == None:
                leaf_basic_blocks = cfg_obj.leaf_nodes
                
                if len(leaf_basic_blocks) > 1:
                    for leaf_block in leaf_basic_blocks:
                        instructions.append(leaf_block._instructions[-1])
                        vrg.local_visit_stack.append(leaf_block._instructions[-1])
                
                else:
                    instruction = leaf_basic_blocks[0]._instructions[-1]
                    vrg.local_visit_stack.append(instruction)
            else:
                vrg.local_visit_stack.append(instruction)


            if len(instructions) != 0:
                result = []
                
                for instr in instructions:
                    lvar = do_flow_sensitive_analysis(log, vrg, cfg_obj, instr, call_type, variable, parameters, parent, node, graph)
                    
                    if isinstance(lvar, list) and len(lvar) != 0:
                        
                        if len(result) > 0:
                            result.append('OR')
                        result.append(lvar)
                    
                    else:
                        
                        if lvar is not None:
                            if len(result) > 0:
                                result.append('OR')
                            result.append(lvar)                            
                    vrg.local_visit_stack.remove(instr)
                
                s_lvar = result

            else:
                s_lvar = do_flow_sensitive_analysis(log, vrg, cfg_obj, instruction, call_type, variable, parameters, parent, node, graph)                
                vrg.local_visit_stack.remove(instruction)

        
        yield s_lvar, s_rvar, type_str
        
def replace_state_var_with_index_node(origin_var, ref_var, vrg):
    if isinstance(origin_var, StateVar):
        return vrg._reference_variables[ref_var]

    if isinstance(origin_var, VarNode):
        return vrg._reference_variables[ref_var]
    
    return origin_var

def process_indexir_rvalue(log, vrg, instr, variable, cfg_obj, call_type, parent=None):
    if type(variable).__name__ == 'StateVariableSolc':
        s_var_obj = get_state_var_obj(log, variable)
        return s_var_obj
    
    elif type(variable).__name__ == 'Constant':
        if str(variable.type) == 'string':
            if global_imports.constants.get(str(variable)) is None:
                global_imports.constants[str(variable)] = global_imports.str_count % 10
                global_imports.str_count += 1

            return global_imports.constants[str(variable)]

        else:
            return variable

    elif type(variable).__name__ in SOLIDITY_VARS:
        return variable

    #: need to tackele elegantly, for now for local variable
    # we are just returning U
    elif type(variable).__name__ == 'LocalVariableSolc':
        constant = Constant('U')
        return constant
    
    elif type(variable).__name__ == 'ReferenceVariable':
        get_origin_variable_from_refvariable(log, vrg, instr, variable, cfg_obj, call_type, parent)
        return vrg._reference_variables[variable]
    
    elif type(variable).__name__ == 'TemporaryVariable':
        constant = Constant('U')
        return constant        
    
    else:
        log.warning('Other types of right variable exists!')
        assert True, "Other types of right variable exists!"

def process_index_ir(log, vrg, instr, variable, cfg_obj, call_type, parent=None):
    variable_right = instr.variable_right
    variable_left = instr.variable_left
    lvalue = instr.lvalue
    
    # If variable left is a state variable, we stop here and store that,
    # Next, for right variable we need to know what is that and accordingly we store that 
    # in a index node 
    if lvalue not in vrg._ref_to_state.keys():
        if type(variable_left).__name__ == 'StateVariableSolc':
            left_value = get_state_var_obj(log, variable_left)
            right_value = process_indexir_rvalue(log, vrg, instr, variable_right, cfg_obj, call_type, parent)
            index_node = IndexNode(left_value, right_value, None)

            vrg._ref_to_state[lvalue] = left_value
            vrg._reference_variables[lvalue] = index_node
        
        elif type(variable_left).__name__ == 'LocalVariableSolc':
            # if location storage it means the local variable is actually storage pointer
            # Hence we should get the origin state variable
            if variable_left.location == 'storage':
                for lvar, rvar, type_str in process_local_variable(log, vrg, cfg_obj, instr, call_type, variable_left, cfg_obj._function.parameters, parent):
                    if lvar is not None:
                        vrg._ref_to_state[lvalue] = lvar
                    
                    else:
                        log.warning("How can lvar be None, debug!")
                        assert lvar != None, "How can lvar be None, debug!" 
                
                rvar = process_indexir_rvalue(log, vrg, instr, variable_right, cfg_obj, call_type, parent)
                index_node = IndexNode(vrg._ref_to_state[lvalue], rvar, None)
                vrg._reference_variables[lvalue] = index_node  
            
            else:
                vrg._ref_to_state[lvalue] = 'U'
                #rvar =  process_indexir_rvalue(log, vrg, instr, variable_right, cfg_obj, call_type, parent)
                #index_node = IndexNode(vrg._ref_to_state[lvalue], rvar, None)
                vrg._reference_variables[lvalue] = 'U'

        elif type(variable_left).__name__ == 'ReferenceVariable':
            vrg._ref_to_state[lvalue] = get_origin_variable_from_refvariable(log, vrg, instr, variable_left, cfg_obj, call_type, parent)
            right_value = process_indexir_rvalue(log, vrg, instr, variable_right, cfg_obj, call_type, parent)
            index_node = IndexNode(vrg._reference_variables[variable_left], right_value, None)
            vrg._reference_variables[lvalue] = index_node
        
        elif type(variable_left).__name__ == 'TemporaryVariable':
            lvar, rvar, type_str = process_temporary_variable(log, vrg, variable_left, cfg_obj, call_type, [])
            state_var = lvar
            
            if type(state_var).__name__ == 'StateVariableSolc':
                left_value = get_state_var_obj(log, state_var)
            
            elif isinstance(state_var, StateVar) or isinstance(state_var, VarNode):
                left_value = state_var
            
            elif state_var == 'U' or (isinstance(state_var, list) and 'U' in state_var):
                left_value = 'U'
            
            else:
                log.warning("This is not expected, am I missing something?")
                sys.exit(1)
            
            if left_value == 'U':
                vrg._ref_to_state[lvalue] = left_value
                vrg._reference_variables[lvalue] = 'U'
            
            else:
                right_value = process_indexir_rvalue(log, vrg, instr, variable_right, cfg_obj, call_type, parent)
                vrg._ref_to_state[lvalue] = left_value
                index_node = IndexNode(vrg._ref_to_state[lvalue], right_value, None)
                vrg._reference_variables[lvalue] = index_node 
        
        elif type(variable_left).__name__ == 'TupleVariable':
            log.warning("Tuple variable needs to be taken care!")
            sys.exit(1)

        elif type(variable_left).__name__ == 'SolidityVariableComposed':
            log.warning("Solidity composed variable needs to be taken care!")
            sys.exit(1)

def process_localVariableInitFromTupleSolc(log, vrg, cfg_obj, instruction, call_type, variable, parameters, parent=None):
    instrs = CFG.lvalue_vars[variable]
    s_lvar = None

    try:
        assert len(instrs) == 1, "need to handle this!"
    except AssertionError as error:
        log.warning("instrs length LocalVariableInitFromTupleSolc is more than 1")
        sys.exit(1)
    
    instr = instrs[0]

    if type(instr).__name__ == 'Unpack':
        tuple_var = instr.tuple
        lvar, rvar, type_str = process_tuple_variable(log, vrg, cfg_obj, instr, call_type, tuple_var, parameters, parent)
        index = instr.index
        try:
            s_lvar = lvar[index]
        except:
            log.warning("This can only happen due to slither insanity, where slither does not capture the returned tuple properly, we ignore it for now!")
            sys.exit(1)
    
    elif type(instr).__name__ == 'Assignment':
        lvar = process_left_or_right_variable(log, vrg, instr.rvalue, cfg_obj, call_type, instr, parameters, parent)
        s_lvar = lvar
    
    else:
        log.warning("Other types of instructions involving LocalVariableInitFromTupleSolc!")
        sys.exit(1)
    
    return s_lvar  

def create_var_node(log, instr, origin_var, struct_member):
    varnode = is_var_node_present(log, origin_var, struct_member)
    
    if varnode == None:
        if instr is None:
            expr = ''
        
        else:
            expr = instr.expression
        
        varnode = VarNode(origin_var, expr, struct_member)
        SDG.var_node_list.append(varnode)
    
    return varnode

def process_member_ir(log, vrg, instr, variable, cfg_obj, call_type, parent):
    var_left = instr.variable_left
    struct_member = instr.variable_right
    lvalue = instr.lvalue

    if lvalue not in vrg._ref_to_state.keys():
        if type(var_left).__name__ == 'StateVariableSolc':
            origin_var = get_state_var_obj(log, var_left)
            var_node = create_var_node(log, instr, origin_var, struct_member)
            vrg._ref_to_state[lvalue] = var_node

            index_node = IndexNode(origin_var, None, struct_member)
            vrg._reference_variables[lvalue] = index_node
        
        elif type(var_left).__name__ == 'LocalVariableSolc':
            if var_left.location == 'storage' or (call_type == 'C' and var_left.location == 'memory'):
                for lvar, rvar, type_str in process_local_variable(log, vrg, cfg_obj, instr, call_type, var_left, cfg_obj._function.parameters, parent):
                    if lvar is not None:
                        if lvar == 'U' or (isinstance(lvar, list) and 'U' in lvar):
                            vrg._ref_to_state[lvalue] = lvar
                            vrg._reference_variables[lvalue] = lvar
                        else:
                            var_node = create_var_node(log, instr, lvar, struct_member)
                            vrg._ref_to_state[lvalue] = var_node
                            index_node = IndexNode(lvar, None, struct_member)
                            vrg._reference_variables[lvalue] = index_node
                    
                    else:
                        log.warning("How can lvar be None, debug!")
                        sys.exit(1)


            else:
                #var_node = create_var_node(log, instr, var_left, struct_member)
                vrg._ref_to_state[lvalue] = 'U'
                #index_node = IndexNode(var_left, None, struct_member)
                vrg._reference_variables[lvalue] = "U"
                
        elif type(var_left).__name__ == 'ReferenceVariable':
            origin_var = get_origin_variable_from_refvariable(log, vrg, instr, var_left, cfg_obj, call_type, parent)
            var_node = create_var_node(log, instr, origin_var, struct_member)
            vrg._ref_to_state[lvalue] = var_node

            index_node = IndexNode(vrg._reference_variables[var_left], None, struct_member)
            vrg._reference_variables[lvalue] = index_node
        
        elif type(var_left).__name__ == 'TemporaryVariable':
            origin_var = process_temporary_variable(log, vrg, var_left, cfg_obj, call_type, cfg_obj._function.parameters, parent)
            assert not isinstance(origin_var, list), "origin var here is list!"
            
            var_node = create_var_node(log, instr, origin_var, struct_member)
            vrg._ref_to_state[lvalue] = var_node

            index_node = IndexNode(origin_var, None, struct_member)
            vrg._reference_variables[lvalue] = index_node
        
        elif type(var_left).__name__ == 'TupleVariable':
            log.warning("Tuple variable needs to be taken care!")
            sys.exit(1)

        elif type(var_left).__name__ == 'SolidityVariableComposed':
            log.warning("Solidity composed variable needs to be taken care!")
            sys.exit(1)

        elif type(var_left).__name__ == 'Enum':
            var_node = create_var_node(log, instr, var_left, struct_member)
            vrg._ref_to_state[lvalue] = var_node
            index_node = IndexNode(var_left, None, struct_member)
            vrg._reference_variables[lvalue] = index_node
        
        elif type(var_left).__name__ == 'ContractSolc04':
            var_node = create_var_node(log, instr, var_left, struct_member)
            vrg._ref_to_state[lvalue] = var_node
            index_node = IndexNode(var_left, None, struct_member)
            vrg._reference_variables[lvalue] = index_node

        elif type(var_left).__name__ == 'SolidityVariable':
            var_node = create_var_node(log, instr, var_left, struct_member)
            vrg._ref_to_state[lvalue] = var_node
            index_node = IndexNode(var_left, None, struct_member)
            vrg._reference_variables[lvalue] = index_node              

        else:
            log.warning("Other type of variable_left in Member IR")
            sys.exit(1)


def process_balance_ir(log, vrg, instr, variable, cfg_obj, call_type, parent=None):
    if type(instr.value).__name__ == 'TemporaryVariable':
        lvalue = instr.lvalue
        
        if lvalue not in vrg._ref_to_state.keys():
            lvar, rvar, type_str = process_temporary_variable(log, vrg, instr.value, cfg_obj, call_type, cfg_obj._function.parameters, parent)
            var_node = create_var_node(log, instr, lvar, BALANCE)
            vrg._ref_to_state[lvalue] = var_node
            
            index_node = IndexNode(lvar, None, BALANCE)
            vrg._reference_variables[lvalue] = index_node                                      
    
    elif type(instr.value).__name__ == 'StateVariableSolc':
        lvalue = instr.lvalue
        
        if lvalue not in vrg._ref_to_state.keys():
            origin_var = get_state_var_obj(log, lvalue)
            var_node = create_var_node(log, instr, origin_var, BALANCE)
            vrg._ref_to_state[lvalue] = var_node
            
            index_node = IndexNode(origin_var, None, BALANCE)
            vrg._reference_variables[lvalue] = index_node
    
    elif type(instr.value).__name__ == 'Constant':
        lvalue = instr.lvalue
        if lvalue not in vrg._ref_to_state.keys():
            vrg._ref_to_state[lvalue] = 'U'
            vrg._reference_variables[lvalue] = 'U'        

    elif type(instr.value).__name__ in SOLIDITY_VARS:
        lvalue = instr.lvalue
        
        if lvalue not in vrg._ref_to_state.keys():
            var_node = create_var_node(log, instr, instr.value, BALANCE)
            vrg._ref_to_state[lvalue] = var_node
            index_node = IndexNode(instr.value, None, BALANCE)
            vrg._reference_variables[lvalue] = index_node   

    elif type(instr.value).__name__ == 'ReferenceVariable':
        lvalue = instr.lvalue 
        
        if lvalue not in vrg._ref_to_state.keys():
            origin_var = get_origin_variable_from_refvariable(log, vrg, instr, instr.value, cfg_obj, call_type, parent)
            var_node = create_var_node(log, instr, origin_var, BALANCE)
            vrg._ref_to_state[lvalue] = var_node
            index_node = IndexNode(vrg._reference_variables[instr.value], None, BALANCE)
            vrg._reference_variables[lvalue] = index_node

    elif type(instr.value).__name__ == 'LocalVariableSolc':
        lvalue = instr.lvalue
        variable = process_left_or_right_variable(log, vrg, instr.value, cfg_obj, call_type, instr, cfg_obj._function.parameters, parent)
        
        if instr.value.is_storage == 'False' or variable == 'U':
            vrg._ref_to_state[lvalue] = variable
            vrg._reference_variables[lvalue] = variable
        
        else:
            var_node = create_var_node(log, instr, variable, BALANCE)
            vrg._ref_to_state[lvalue] = var_node
            index_node = IndexNode(variable, None, BALANCE)
            vrg._reference_variables[lvalue] = index_node            
    
    else:
        #if DEBUG:
        log.warning("Can other types of value exist for balance statements! Checkout")
        sys.exit(1)

def process_length_ir(log, vrg, instr, variable, cfg_obj, call_type, parent=None):
    lvalue = instr.lvalue

    if type(instr.value).__name__ == 'StateVariableSolc':
        origin_var = get_state_var_obj(log, instr.value)
        varnode = create_var_node(log, instr, origin_var, LENGTH)
        vrg._ref_to_state[lvalue] = varnode
        index_node = IndexNode(origin_var, None, LENGTH)
        vrg._reference_variables[lvalue] = index_node
    
    elif type(instr.value).__name__ == 'ReferenceVariable':
        origin_var = get_origin_variable_from_refvariable(log, vrg, instr, instr.value, cfg_obj, call_type, parent)
        varnode = create_var_node(log, instr, origin_var, LENGTH)
        vrg._ref_to_state[lvalue] = varnode
        index_node = IndexNode(origin_var, None, LENGTH)
        vrg._reference_variables[lvalue] = index_node
    
    elif type(instr.value).__name__ == 'LocalVariableSolc':
        
        if instr.value.location == 'storage':
            for lvar, rvar, type_str in process_local_variable(log, vrg, cfg_obj, instr, call_type, instr.value, cfg_obj._function.parameters, parent):
                if lvar is not None:
                    origin_var = lvar
                
                else:
                    log.warning("lvalue can not be none!")
                    sys.exit(1)

                varnode = create_var_node(log, instr, origin_var, LENGTH)
                vrg._ref_to_state[lvalue] = varnode
                index_node = IndexNode(origin_var, None, LENGTH)
                vrg._reference_variables[lvalue] = index_node

        else:
            if is_tainted(log, instr.value, cfg_obj, cfg_obj._function._contract) == True:
                vrg._ref_to_state[lvalue] = 'U'
            
            else:
                origin_var = process_left_or_right_variable(log, vrg, instr.value, cfg_obj, call_type, instr, cfg_obj._function.parameters, parent)
                varnode = create_var_node(log, instr, origin_var, LENGTH)
                vrg._ref_to_state[lvalue] = varnode
                index_node = IndexNode(origin_var, None, LENGTH)
                vrg._reference_variables[lvalue] = index_node            
    
    else:
        origin_var = process_left_or_right_variable(log, vrg, instr.value, cfg_obj, call_type, instr, cfg_obj._function.parameters, parent)
        if origin_var != 'U':
            varnode = create_var_node(log, instr, origin_var, LENGTH)
            vrg._ref_to_state[lvalue] = varnode
            index_node = IndexNode(origin_var, None, LENGTH)
            vrg._reference_variables[lvalue] = index_node
        else:
            vrg._ref_to_state[lvalue] = origin_var
            vrg._reference_variables[lvalue] = origin_var

def get_origin_variable_from_refvariable(log, vrg, instruction, variable, cfg_obj, call_type, parent=None):
    if variable in CFG.lvalue_vars.keys():
        instrs = CFG.lvalue_vars[variable]    
        instrs_length = len(instrs)
        lvalue = None
        
        for instr in instrs:
            # If the type of the instruction is index
            if type(instr).__name__ == 'Index':
                lvalue = instr.lvalue
                process_index_ir(log, vrg, instr, variable, cfg_obj, call_type, parent)
                                
            elif type(instr).__name__ == 'Member':
                lvalue = instr.lvalue
                process_member_ir(log, vrg, instr, variable, cfg_obj, call_type, parent)
                                
            elif type(instr).__name__ == 'Balance':
                lvalue = instr.lvalue
                process_balance_ir(log, vrg, instr, variable, cfg_obj, call_type, parent)
            
            elif type(instr).__name__ == 'Length':
                lvalue = instr.lvalue
                process_length_ir(log, vrg, instr, variable, cfg_obj, call_type, parent)
            
            elif type(instr).__name__ == 'Binary':
                continue
            
            elif type(instr).__name__ == 'Delete':
                continue
            
            elif type(instr).__name__ == 'Assignment':
                continue
            
            elif type(instr).__name__ == 'Push':
                continue
            
            elif type(instr).__name__ == 'InitArray':
                continue

            elif type(instr).__name__ == 'Unpack':
                continue

            else:
                #if DEBUG:
                log.warning("Other types of instructions involing reference var!")
                sys.exit(1)
                
        
        assert lvalue != None, "lvalue can not be none!"
        return vrg._ref_to_state[lvalue]

    else:
        if variable in cfg_obj._function.parameters:
            return variable
        
        else:
            if DEBUG:
                log.warning("Can there be anyother cases apart for local variables? Checkout")

def process_return_argument(log, vrg, callee_function, function_return, call_arguments, call_type, parent=None):
    function_parameters = callee_function.parameters
    binary_op_list = []

    if isinstance(function_return, list):
        for element in function_return:
            if element in function_parameters:
                index = function_parameters.index(element)
                caller_var = call_arguments[index]
                binary_op_list.append(caller_var)
            
            else:
                if type(element).__name__ in CONSTANT_TYPES:
                    binary_op_list.append(element)

                elif type(element).__name__ == 'StateVariableSolc':
                    s_var_obj = get_state_var_obj(element)
                    binary_op_list.append(s_var_obj)
                
                elif type(element).__name__ in SOLIDITY_VARS:
                    binary_op_list.append(element) 
                
                elif type(element).__name__ == 'LocalVariableSolc':
                    binary_op_list.append('U') 
                
                elif isinstance(element, StateVar):
                    binary_op_list.append(element)

                elif isinstance(element, VarNode):
                    binary_op_list.append(element)

                elif isinstance(element, IndexNode):
                    binary_op_list.append(element)                
                
                elif isinstance(element, list):
                    res = process_return_argument(log, vrg, callee_function, element, call_arguments, call_type, parent)
                    binary_op_list.append(res)
    
                else:
                    #if DEBUG:
                    log.warning("What else can a argument be!")
                    sys.exit(1)
    else:
        if function_return in function_parameters:
            index = function_parameters.index(function_return)
            caller_var = call_arguments[index]
            binary_op_list.append(function_return)
        
        elif type(function_return).__name__ == 'StateVariableSolc':
            s_var_obj = get_state_var_obj(function_return)
            binary_op_list.append(s_var_obj)
        
        elif isinstance(function_return, StateVar):
            binary_op_list.append(function_return)                
        
        elif isinstance(function_return, IndexNode):
            binary_op_list.append(function_return) 

        elif isinstance(function_return, VarNode):
            binary_op_list.append(function_return)        
        
        elif type(function_return).__name__ in SOLIDITY_VARS:
            binary_op_list.append(function_return) 
        
        elif type(function_return).__name__ in CONSTANT_TYPES:
            binary_op_list.append(function_return)        
        
        else:
            if DEBUG:
                log.warning("Watch out here! can be an outlier")
            binary_op_list.append(function_return)
    
    return binary_op_list

def map_callee_returns_to_caller_args(log, vrg, callee_function, call_arguments, call_type, parent=None):
    
    # Callee function's return values and parameters
    function_returns = CFG.function_cfg[callee_function]._return_summary
    return_values = CFG.function_cfg[callee_function]._return_values
    
    if len(function_returns) == 0:
        vrg.return_summary_handler(CFG.function_cfg[callee_function])
        function_returns = CFG.function_cfg[callee_function]._return_summary
        return_values = CFG.function_cfg[callee_function]._return_values
    
    function_parameters = callee_function.parameters
    return_list = {}
    
    # If a function has multiple returns then each return value
    # should be in a separate list. If the length of the list is
    # more than one, it means the return is a result of binary operation
    for return_key in function_returns.keys():
        function_return = function_returns[return_key]
        binary_op_list = process_return_argument(log, vrg, callee_function, function_return, call_arguments, call_type, parent)
        
        #if len(return_list) > 0:
            #return_list.append('OR')

        return_list[return_key] = binary_op_list
        
    
    return return_list

def get_call_arguments_origin(log, vrg, argument, call_instr, caller_parameters, caller_cfg_obj, call_type, parent=None):
    origin_res = []

    if isinstance(argument, list):
        for arg in argument:
            results = get_call_arguments_origin(log, vrg, arg, call_instr, caller_parameters, caller_cfg_obj, call_type, parent)
            
            if len(results) == 1:
                origin_res.extend(results)
            else:
                origin_res.append(results)

            if 'U' in origin_res:
                origin_res = ['U']

    else:
        if type(argument).__name__ == 'TemporaryVariable':
            s_lvar, s_rvar, type_str = process_temporary_variable(log, vrg, argument, caller_cfg_obj, call_type, caller_parameters, parent)
            if isinstance(s_lvar, list):
                origin_res = s_lvar
            else:
                origin_res = [s_lvar]

        elif type(argument).__name__ == 'ReferenceVariable':
            res = get_origin_variable_from_refvariable(log, vrg, call_instr, argument, caller_cfg_obj, call_type, parent)
            res = replace_state_var_with_index_node(res, argument, vrg)
            origin_res = get_call_arguments_origin(log, vrg, res, call_instr, caller_parameters, caller_cfg_obj, call_type, parent) 
        
        elif type(argument).__name__ == 'StateVariableSolc':
            origin_res = [argument]
            origin_var = get_state_var_obj(log, argument)
            
            if origin_var in vrg._constant_state_vars.keys():
                origin_var = vrg._constant_state_vars[origin_var]                
                origin_res = [origin_var]
            
            else:
                origin_res = [origin_var]
        
        elif isinstance(argument, StateVar):
            if argument in vrg._constant_state_vars.keys():
                origin_var = vrg._constant_state_vars[origin_var]                
                origin_res = [origin_var]
            else:
                origin_res = [argument]                    
        
        elif type(argument).__name__ == 'LocalVariableSolc':
            taint_flag = is_tainted(log, argument, caller_cfg_obj, caller_cfg_obj._function.contract)
            
            if taint_flag == True: #and argument in caller_parameters:
                origin_res = ['U']
                '''
                else:
                    if taint_flag == False:
                        s_lvar, s_rvar, type_str = process_local_variable(caller_cfg_obj, argument, caller_parameters)
                        
                        if s_lvar is not None:
                            origin_res = [s_lvar]
                        if s_rvar is not None:
                            origin_res = [s_rvar]
                '''

            else:
                # This case is interesting, this argument is actually derived using some constant variable operation. This case appears
                # In _adjustValue of LoanTokenLogicV4. The argument is interestRate. Which is passed as a argument from two different functions
                # TMP_531(uint256) = INTERNAL_CALL, LoanTokenLogicV4._nextBorrowInterestRate2(uint256,uint256,bool)(TMP_529,TMP_530,useFixedInterestModel)
                # interestRate(uint256) := TMP_531(uint256) (function _getBorrowAmountAndRate)
                # TMP_280(uint256) = 10 ** 20 ( in function getMaxEscrowAmount)
                # So far we just implement a simple things, get all the dependent vars, search for temporary vars in them and 
                # predict the possible values using process_temporary_variable()
                res_var = process_left_or_right_variable(log, vrg, argument, caller_cfg_obj, call_type, call_instr, caller_parameters, parent)
                if isinstance(res_var, list):
                    origin_res = res_var
                else:
                    origin_res = [res_var]

                '''
                dep_vars = list(slither.analyses.data_dependency.data_dependency.get_dependencies(argument, caller_cfg_obj._function.contract))
                for var in dep_vars:
                    if type(var).__name__ == 'TemporaryVariable':
                        lvar, rvar, type_str = process_temporary_variable(log, vrg, var, caller_cfg_obj, call_type)
                        if type(lvar).__name__ in CONSTANT_TYPES:
                            origin_res = [lvar]
                            break
                '''
        
        elif type(argument).__name__ == 'Constant':
            origin_res = [argument]
        
        elif type(argument).__name__ == 'int' or type(argument).__name__ == 'str':
            origin_res = [argument]
        
        elif isinstance(argument, VarNode):
            # : This is not perfect, probably needs to be looked at
            origin_res = [argument]
        
        elif isinstance(argument, IndexNode):
            origin_res = [argument]

        elif type(argument).__name__ in SOLIDITY_VARS:
            # : This is not perfect, probably needs to be looked at
            origin_res = [argument]        
        
        elif type(argument).__name__ == 'LocalVariableInitFromTupleSolc':

            lvar = process_localVariableInitFromTupleSolc(log, vrg, caller_cfg_obj, call_instr, call_type, argument, caller_parameters, parent)
            origin_res = lvar
        
        else:
            #if DEBUG:
            log.warning("Why I am here!")
            sys.exit(1)

    return origin_res