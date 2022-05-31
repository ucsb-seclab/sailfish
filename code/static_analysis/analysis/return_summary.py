import slither
import shutil
import sys
import os
import pydot
import glob
import traceback
import json
import networkx as nx
from collections import defaultdict
import matplotlib.pyplot as plt
from varnode import *
from collections import defaultdict
from slither.core.declarations.solidity_variables import SolidityFunction
from slither.core.declarations.function import Function
from slither.core.variables.variable import Variable
from slither.printers.call.call_graph import *
from slither.core.cfg.node import NodeType
from cfg import *
from basic_block import *
from instr_block import *
from icfg import *
from varnode import *
import copy
from sdg import *
from util import *
from index_node import *
from value_node import *
from range_node import *
from state_var import *
from process_ir import *
import traceback

# Improvements: Probably we may need to field sensitive
CONSTANT_TYPES = ['int', 'str', 'Constant']
VARIBLE_TYPES = ['StateVariableSolc', 'LocalVariableSolc']
SOLIDITY_VARS = ['SolidityVariableComposed', 'SolidityVariable']

def process_state_variable_return(log, vrg, return_value, cfg_obj):
    s_var_obj = get_state_var_obj(log, return_value)
    if s_var_obj in vrg._constant_state_vars.keys():
        cfg_obj._return_summary[return_value] = [vrg._constant_state_vars[s_var_obj]]

    else:
        cfg_obj._return_summary[return_value] = [s_var_obj]     

def process_solidity_variable_return(log, vrg, return_value, cfg_obj):
    cfg_obj._return_summary[return_value] = [return_value]

def process_temp_variable_return(log, vrg, parameters, return_instr, return_value, cfg_obj):
    return_summary = []
    lvar, rvar, type_str = process_temporary_variable(log, vrg, return_value, cfg_obj, 'R', parameters)
    
    if lvar is not None:
        if isinstance(lvar, list):
            return_summary.extend(lvar)
        else:
            return_summary.append(lvar)
    
    if rvar is not None:
        if isinstance(rvar, list):
            return_summary.extend(rvar)
        else:
            return_summary.append(rvar)
    
    cfg_obj._return_summary[return_value] = return_summary

def process_local_variable_return(log, vrg, parameters, return_instr, return_value, cfg_obj):
    return_summary = []
    
    if return_value in parameters:
        cfg_obj._return_summary[return_value] = [return_value]  
    
    else:
        if return_value not in CFG.lvalue_vars.keys():
            log.info("We should not consider this kind of return values!")
        
        else:
            for lvar, rvar, type_str in process_local_variable(log, vrg, cfg_obj, return_instr, 'R', return_value, parameters):
                if len(return_summary) >= 1:
                    return_summary.append('OR')
                if lvar is not None:
                    if isinstance(lvar, list):
                        return_summary.extend(lvar)
                    else:
                        return_summary.append(lvar)
                
                if rvar is not None:
                    if isinstance(rvar, list):
                        return_summary.extend(rvar)
                    else:
                        return_summary.append(rvar)
    
                cfg_obj._return_summary[return_value] = return_summary    

def process_ref_variable_return(log, vrg, parameters, instruction, return_value, cfg_obj):
    origin_var = get_origin_variable_from_refvariable(log, vrg, None, return_value, cfg_obj, 'R')
    origin_var = replace_state_var_with_index_node(origin_var, return_value, vrg)

    if type(origin_var).__name__ == 'LocalVariableSolc':
        taint_flag = is_tainted(log, origin_var, cfg_obj, cfg_obj._function.contract)
        
        if origin_var in parameters and taint_flag:
            cfg_obj._return_summary[return_value] = ['U']
        
        else:
            if DEBUG:
                log.warning("Other types of local variables to be considered!")
                sys.exit(1)

    elif isinstance(origin_var, StateVar):
        cfg_obj._return_summary[return_value] = [origin_var]
    
    elif isinstance(origin_var, VarNode):
        cfg_obj._return_summary[return_value] = [origin_var]
    
    elif isinstance(origin_var, IndexNode):
        cfg_obj._return_summary[return_value] = [origin_var]
    
    elif origin_var == 'U':
        cfg_obj._return_summary[return_value] = [origin_var]
    else:
        #if DEBUG:
        log.warning("Other types of variables to be considered!")
        sys.exit(1)

def process_tuple_variable_return(log, vrg, parameters, return_instr, return_value, cfg_obj):
    return_summary = []
    lvar, rvar, type_str = process_tuple_variable(log, vrg, cfg_obj, return_instr, "R", return_value, parameters)
    
    if lvar is not None:
        if isinstance(lvar, list):
            return_summary.extend(lvar)
        else:
            return_summary.append(lvar)
    
    if rvar is not None:
        if isinstance(rvar, list):
            return_summary.extend(rvar)
        else:
            return_summary.append(rvar)    

    cfg_obj._return_summary[return_value] = return_summary

def process_LocalVariableInitFromTupleSolc_return(log, vrg, parameters, return_instr, return_value, cfg_obj):
    return_summary = []
    lvar = process_localVariableInitFromTupleSolc(log, vrg, cfg_obj, return_instr, "R", return_value, parameters)
    
    if lvar is not None:
        if isinstance(lvar, list):
            return_summary.extend(lvar)
        else:
            return_summary.append(lvar)  

    cfg_obj._return_summary[return_value] = return_summary


def get_ir_instr(log, vrg, cfg_obj, return_value):
    instr = None
    for return_ir in cfg_obj._returns_irs:
        if return_value in return_ir.used:
            instr = return_ir
            break
    return instr

def generate_return_summary(log, vrg, cfg_obj, parameters, return_values):
    vrg._loop_count = {}
    completed_returns = []

    for num in return_values:
        for value in return_values[num]:
            # We only record varibles which influences the return values somehow
            if value in completed_returns:
                continue
            
            completed_returns.append(value)
            return_summary = []

            return_instr = get_ir_instr(log, vrg, cfg_obj, value)
            
            if type(value).__name__ == 'Constant':
                cfg_obj._return_summary[value.name] = [value]        
            
            elif type(value).__name__ == 'TemporaryVariable':
                if value not in CFG.lvalue_vars.keys():
                    continue
                
                process_temp_variable_return(log, vrg, parameters, return_instr, value, cfg_obj)
            
            elif type(value).__name__ == 'LocalVariableSolc':
                process_local_variable_return(log, vrg, parameters, return_instr, value, cfg_obj)
            
            elif type(value).__name__ == 'ReferenceVariable':
                process_ref_variable_return(log, vrg, parameters, return_instr, value, cfg_obj)
            
            elif type(value).__name__ == 'StateVariableSolc':
                process_state_variable_return(log, vrg, value, cfg_obj)
            
            elif type(value).__name__ == 'SolidityVariable' or type(value).__name__ == 'SolidityVariableComposed':
                process_solidity_variable_return(log, vrg, value, cfg_obj)

            elif type(value).__name__ == 'TupleVariable':
                process_tuple_variable_return(log, vrg, parameters, return_instr, value, cfg_obj)
            
            elif type(value).__name__ == 'LocalVariableInitFromTupleSolc':
                process_LocalVariableInitFromTupleSolc_return(log, vrg, parameters, return_instr, value, cfg_obj)

            # : This else part need to be fixed
            else:
                #if DEBUG:
                log.warning("Can a return value be something that needs special treatment!")
                sys.exit(1)
                #cfg_obj._return_summary[value] = [value]      