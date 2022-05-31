import sys
sys.path.append("..")
sys.path.append("../../symbolic_execution/")

from ir_translator import *
from collections import OrderedDict
import ujson
import argparse
import os
import logging
import sys
import glob
import time
import datetime
import logging
import traceback
import multiprocessing
import json
from slither.slither import Slither
from util import *
from detection import *
from callgraph import *
from sdg import *
from icfg import *
from cfg import *
from lib import *
from compose import *
from config import *
from shutil import rmtree
from state_var import *
import networkx as nx
from vdg import *
from basic_block import *
from range_graph import *
from json_block import *
from slither.slithir.variables.temporary import TemporaryVariable
from slither.slithir.operations.nop import Nop
from slither.slithir.operations.assignment import Assignment
from slither.slithir.operations.binary import Binary
from slither.slithir.operations.binary import BinaryType
from slither.slithir.variables.constant import Constant
from slither.slithir.variables.variable import Variable
from slither.core.solidity_types.type import Type
from slither.slithir.variables.temporary import TemporaryVariable
from imports import *
import global_imports
NOPED_OUT = ['Push', 'EventCall', 'Delete']
ROOT_DIR = '/home/sherlock/research/projects/smart-contract'
INIT_ASSIGNMENT_FUNCTIONS = ['constructor', 'slitherConstructorVariables']
solidity_special_vars = {'block.coinbase' : "address", 
                            'block.difficulty' : "uint", 
                            'block.gaslimit' : "uint", 
                            'block.number' :"uint", 
                            'block.timestamp' : "uint", 
                            'msg.data' : "bytes", 
                            'msg.sender' : "address", 
                            'msg.sig' : "bytes4", 
                            'msg.value' : "uint", 
                            'now' : "uint", 
                            'tx.gasprice' : "uint", 
                            'tx.origin' : "address",
                            'this.balance': "uint",
                            'this.address': "address",
                            'msg_sender': "integer"
                        }

external_calls = ['HighLevelCall', 'LowLevelCall']
initialize_special_vars = {'msg_sender' : ["msg_sender := 0x4"],
                           'this.address' : ["this.address := 0x5"],
                           'msg.sender' : ["msg.sender := 0x6"]}
initialize_vars = 0
json_blocks_mapping = {}
function_visibility = ['public', 'external']

string_to_integer = {}

def is_ir_call(ir):
    if type(ir).__name__ == 'InternalCall':
        return True
    elif type(ir).__name__ == 'LibraryCall':
        return True
    else:
        return False

def invoke_post_processing_translation(json_obj):
    gt = IRTranslator() # instantiate a new translator
    new_json_obj = gt.translate(json_obj)
    return new_json_obj

def get_successors_block_address(graph, node, error_node):
    successors = list(graph.successors(node))
    addr = {}
    addrs = []
    
    if len(successors) != 0:
        successors = get_paths_between_nodes(graph, node, successors, error_node)
    
    if len(successors) == 1:
        addr[hex(successors[0]._block_id)] = True
    
    else:
        if len(successors) > 1:
            for i in range(0, 2):
                if successors[i]._is_True == None:
                    addr[hex(successors[i]._block_id)] = not successors[1 - i]._is_True
                
                else:
                    addr[hex(successors[i]._block_id)] = successors[i]._is_True
    
    addrs = addr

    return successors, addrs

def get_paths_between_nodes(graph, src_node, dest_nodes, error_node):
    #dest_nodes[0]._is_True = True
    succsrs = []

    if type(src_node._instructions[-1]).__name__ == 'Condition':
       
        if len(dest_nodes) == 1:
            succsrs.extend(dest_nodes)
            graph.add_edge(src_node, error_node)
            succsrs.append(error_node)
        
        else:
            for dest_node in dest_nodes:
                graph.remove_edge(src_node, dest_node)
                
                if nx.algorithms.shortest_paths.has_path(graph, src_node, dest_node) == False:
                    graph.add_edge(src_node, dest_node)
                    succsrs.append(dest_node)
                
                else:
                    graph.add_edge(src_node, error_node)
                    succsrs.append(error_node)
    
    elif is_ir_call(src_node._instructions[-1]):
        pass
    
    else:
        succsrs.extend(dest_nodes)
    
    return succsrs

def get_predecessors_block_address(graph, node):
    predecessors = list(graph.predecessors(node))
    addrs = [hex(predecessor._block_id) for predecessor in predecessors]
    return addrs

def process_instructions(graph, basic_block, successors):
    ir_instrs = [str(x) for x in basic_block._instructions[0:-1]]
    instr = str(basic_block._instructions[-1])
    # Needs to be fixed
    
    if type(basic_block._instructions[-1]).__name__ == 'Condition':
        instr = instr + ',' + successors[0]
    
    ir_instrs.append(instr)

    return ir_instrs

def get_str_instructions(range_node):
    instructions = range_node._instructions
    instr_list = []
    refvars = {}
    for instr in instructions:
        str_instr = str(instr)
        instr_tokens = str_instr.split(" ")

        if str_instr.find(".length") != -1:
            str_instr = str(instr_tokens[0]) + " = " + "NEW_VAL integer"

        if instr_tokens[0].startswith('REF_') and instr_tokens[1] == '->':
            refvars[instr_tokens[0]] = instr_tokens[2]

        elif instr_tokens[0].startswith('REF_') and (instr_tokens[1] == ':=' or instr_tokens[1] == '='):
            instr_tokens[0] = refvars[instr_tokens[0]]
            str_instr = instr_tokens[0]

            for token in instr_tokens[1:]:
                str_instr = str_instr + " " + token

        instr_list.append(str(str_instr))

    return instr_list

def get_variable_rangevalue(scope_str, range_node, graph):
    instructions = get_str_instructions(range_node)#range_node.print_instructions()
    json_block = JsonBlock(instructions, scope_str)
    range_dict = json_block.get_block_dict()
    
    return range_dict

def flatten_the_conditions(scope_str, element, graph, json_blocks, visited_nodes, map_rnode_to_jblock):
    if isinstance(element, RangeNode):
        json_block = get_variable_rangevalue(scope_str, element, graph)
        map_rnode_to_jblock[json_block['addr']] = element
        json_blocks.append(json_block)
        visited_nodes.append(element)
    
    elif isinstance(element, list):
        for elem in element:
            flatten_the_conditions(scope_str, elem, graph, json_blocks, visited_nodes, map_rnode_to_jblock)

    else:
        if element == '||':
            json_blocks.append('||')

def generate_conditional_irs(scope_str, target_addr, nop_block_addr, range_node, graph):
    predecesors = list(graph.predecessors(range_node))
    map_rnode_to_jblock = {}
    json_blocks = []
    visited_nodes = []
    
    for b_block in range_node._predecessors.keys():
        elements = range_node._predecessors[b_block]

        for element in elements:
            flatten_the_conditions(scope_str, element, graph, json_blocks, visited_nodes, map_rnode_to_jblock)

    for pred in predecesors:
        if pred not in visited_nodes:
            json_block = get_variable_rangevalue(scope_str, pred, graph)
            map_rnode_to_jblock[json_block['addr']] = pred
            json_blocks.append(json_block)

    for i in range(0, len(json_blocks)):
        if json_blocks[i] == '||':
            json_blocks[i-1]['instructions'][-1] = json_blocks[i-1]['instructions'][-1] + ' ' + json_blocks[i + 1]['addr'] + ' ' + json_blocks[i + 1]['addr']
        else:
            if i < len(json_blocks) - 1:
                if json_blocks[i+1] != '||':
                    pred_node = map_rnode_to_jblock[json_blocks[i]['addr']]

                    if range_node._true_or_false[pred_node] == 'true':
                        json_blocks[i]['instructions'][-1] = json_blocks[i]['instructions'][-1] + ' ' + json_blocks[i + 1]['addr'] + ' ' + nop_block_addr
                    
                    else:
                        json_blocks[i]['instructions'][-1] = json_blocks[i]['instructions'][-1] + ' ' + nop_block_addr + ' ' + json_blocks[i + 1]['addr']

    
    if len(json_blocks) != 0:
        pred_node = map_rnode_to_jblock[json_blocks[-1]['addr']]
        
        try:
            if range_node._true_or_false[pred_node] == 'true':
                json_blocks[-1]['instructions'][-1] = json_blocks[-1]['instructions'][-1] + ' ' + target_addr + ' ' + nop_block_addr
            
            else:
                json_blocks[-1]['instructions'][-1] = json_blocks[-1]['instructions'][-1] + ' ' + nop_block_addr + ' ' + target_addr
        except:
            traceback.print_exc()
            sys.exit(1)

    blocks = []
    for block in json_blocks:
        if block != '||':
            blocks.append(block)
    
    return blocks

def create_NOP_ir():
    ir = Nop()
    return str(ir)

def find_origin_var(state_var):
    if hasattr(state_var, 'origin'):
        origin_var = find_origin_var(state_var.origin)
    
    elif hasattr(state_var, '_origin_var'):
        origin_var = find_origin_var(state_var._origin_var)
    
    elif hasattr(state_var, '_state_var'):
        origin_var = find_origin_var(state_var._state_var)
    
    else:
        origin_var = state_var
    
    return origin_var

def get_statevar_assignments(slither_obj, vrg_obj):
    global_vars = {}
    global_constant_vars = {}
    range_vars = {}

    #global_blocks = []
    #range_blocks = []

    global_blocks = {}
    range_blocks = {}

    NOP_block = JsonBlock([create_NOP_ir()], '__RANGE__')
    NOP_block_dict = NOP_block.get_block_dict()
    nop_block_addr = NOP_block_dict['addr']
    
    dummy_range_block = JsonBlock([create_NOP_ir()], '__RANGE__')
    dummy_range_block_dict = dummy_range_block.get_block_dict()
    dummy_block_addr = dummy_range_block_dict['addr']

    for contract in slither_obj.contracts:
        global_vars[contract] = OrderedDict()
        global_constant_vars[contract] = {}
        range_vars[contract] = {}

        global_blocks[contract] = []
        range_blocks[contract] = []
        range_blocks[contract].append(NOP_block_dict)
        range_blocks[contract].append(dummy_range_block_dict)

    owner_only_state_vars = get_owner_only_vars(vrg_obj)

    for cfg_obj in vrg_obj.value_graph.keys():
        contract = cfg_obj._function.contract

        # Creates block for constant global vars
        if cfg_obj._function.name == 'slitherConstructorConstantVariables':
            for s_var, triplets in vrg_obj.value_graph[cfg_obj].items():
                for triplet in triplets:
                    range_node = triplet[0]

                    if global_constant_vars[contract].get(str(s_var)) is None:
                        global_constant_vars[contract][str(s_var)] = []
                    
                    json_block = get_variable_rangevalue('__GLOBAL__', range_node, triplet[1])
                    create_msg_sender(json_block)
                    global_constant_vars[contract][str(s_var)].append(json_block['addr'])
                    global_blocks[contract].append(json_block)

        # Creates block for global vars
        elif cfg_obj._function.name in INIT_ASSIGNMENT_FUNCTIONS or cfg_obj._function.is_constructor is True:
            for s_var, triplets in vrg_obj.value_graph[cfg_obj].items():

                # Add global vars to blocks only if it is solely written in a constructors which is created
                # by contract creator
                ## This condition is commented out since globals should always be initialized
                ## irrestive of whether it can only be set by owner or not, otherwise it can result in false positives
                #if s_var not in owner_only_state_vars:
                    #continue

                for triplet in triplets:
                    range_node = triplet[0]
                    if global_vars[contract].get(str(s_var)) is None:
                        global_vars[contract][str(s_var)] = []
                    
                    json_block = get_variable_rangevalue('__GLOBAL__', range_node, triplet[1])
                    create_msg_sender(json_block)
                    global_vars[contract][str(s_var)].append(json_block['addr'])
                    global_blocks[contract].append(json_block)
        
        else:
            if cfg_obj._function.visibility in function_visibility:
                for s_var, triplets in vrg_obj.value_graph[cfg_obj].items():
                    for triplet in triplets:
                        range_node = triplet[0]
                        scope_str = '__RANGE__'
                        
                        origin_svar = str(find_origin_var(s_var))
                        #else:
                            #origin_svar = str(s_var)
                        
                        if range_vars[contract].get(origin_svar) is None:
                            range_vars[contract][origin_svar] = [dummy_block_addr]

                        json_block = get_variable_rangevalue(scope_str, range_node, triplet[1])
                        conditional_blocks = generate_conditional_irs(scope_str, json_block['addr'], nop_block_addr, range_node, triplet[1])
                        conditional_blocks.append(json_block)
                        range_vars[contract][str(origin_svar)].append(conditional_blocks[0]['addr'])
                    range_blocks[contract].extend(conditional_blocks)

    # This part converts the range blocks into a list of dicts
    range_vars_list = {}
    for contract in range_vars.keys():
        if range_vars_list.get(contract) is None:
            range_vars_list[contract] = []

        var_details = range_vars[contract]

        for var_name in var_details.keys():
            new_dict = {}
            new_dict['name'] = var_name
            new_dict['addrs'] = var_details[var_name]
            range_vars_list[contract].append(new_dict)

    range_vars = range_vars_list

    return global_vars, global_constant_vars, range_vars, global_blocks, range_blocks

def create_msg_sender(json_block):
    length = len(json_block['instructions'])
    for i in range(0, length):
        if 'msg.sender' in json_block['instructions'][i]:
            json_block['instructions'][i] = json_block['instructions'][i].replace('msg.sender', 'msg_sender')


def get_global_enums(log, slither_obj):
    all_enums = []

    for contract in slither_obj.contracts:
        for enum in contract.enums:
            enum_format = {}
            value_info = {}

            for element in enum.values:
                value = enum.values.index(element)
                value_info[element] = value
            
            enum_format['name'] = enum.name
            enum_format['values'] = value_info
            all_enums.append(enum_format)
    
    return all_enums


def get_owner_only_vars(vrg):
    owner_only_state_vars = []
    for state_var in vrg._state_var_written.keys():
        functions = vrg._state_var_written[state_var]
        flag = True
        for function in functions:
            if function.name not in INIT_ASSIGNMENT_FUNCTIONS:
                flag = False
                break
        if flag:
            owner_only_state_vars.append(state_var)
    return owner_only_state_vars

def get_global_structs(log, slither_obj):
    all_structures = []
    structure_format = {}
    type_info = {}

    for contract in slither_obj.contracts:
        for structure in contract.structures:
        
            structure_format = {}
            type_info = {}
            
            for elem in structure.elems.keys():
                element = structure.elems[elem]
                type_info[elem] = get_type_information(element, log)

            structure_format['name'] = structure.name
            structure_format['fields'] = type_info
            
            all_structures.append(structure_format)
    
    return all_structures

def derive_different_var_type(var_type, log):
    if type(var_type.type).__name__ == 'ElementaryType':
        pass
    elif type(var_type.type).__name__ == 'MappingType':
        pass
    elif type(var_type.type).__name__ == 'UserDefinedType':
        pass


def get_type_information(s_var, log):
    type_info = []

    if isinstance(s_var, Variable):
        var_type = s_var.type

    elif isinstance(s_var, Type):
        var_type = s_var

    else:
        log.warning("Something unknown type!, debug")
        sys.exit(1)

    if type(var_type).__name__ == 'MappingType':
        type_info.append('mapping')

        if type(var_type.type_from).__name__ == 'ElementaryType':
            type_info.append(str(var_type.type_from))
        else:
            type_info.append(get_type_information(var_type.type_from, log))

        if type(var_type.type_to).__name__ == 'ElementaryType':
            type_info.append(str(var_type.type_to))

        else:
            type_info.append(get_type_information(var_type.type_to, log))

    elif type(var_type).__name__ == 'ElementaryType':
        type_info.append(str(var_type))

    elif type(var_type).__name__ == 'StructureSolc':
        type_info.append(str(var_type.name))

    elif type(var_type).__name__ == 'UserDefinedType':
        if type(var_type.type).__name__ == 'StructureSolc':
            type_info.append(str(var_type.type.name))

        elif type(var_type.type).__name__ == 'ContractSolc04':
            type_info.append('address')

        elif type(var_type.type).__name__ == 'Enum':
            #type_info.append(str(var_type.type.name))
            type_info.append("integer")

        else:
            log.warning("Other types of variable in symex helper")
            sys.exit(1)


    elif type(var_type).__name__ == 'ArrayType':
        type_info.append('array')

        if type(var_type.type).__name__ == 'MappingType' or type(var_type.type).__name__ == 'ArrayType':
            type_info.append(get_type_information(var_type.type, log))

        elif isinstance(var_type.type, Type):
            type_info.extend(get_type_information(var_type.type, log))

        else:
            type_info.append(str(var_type.type))

    else:
        log.warning("Other types of variables, debug!")
        sys.exit(1)

    return type_info


def insert_vars(var_list, g_vars, var_dependency, target_var):
    for addr in g_vars[target_var]:
        if var_dependency.get(addr) is None:
            continue
        dep_vars = list(set(var_dependency[addr]) - set([target_var]))
        for dep_var in dep_vars:
            if dep_var not in var_list:
                insert_vars(var_list, g_vars, var_dependency, dep_var)

        if target_var not in var_list:
            var_list.append(target_var)

def get_variables_and_types(slither_obj, g_vars, g_constant_vars, g_blocks, log):
    global_vars = []
    global_constant_vars = []
    solidity_vars = []
    state_vars = []

    global_vars_list = list(g_vars.keys())
    sv_list = []
    var_dependency = {}

    for block in g_blocks:
        instructions = block['instructions']
        common_state_vars = []

        for instr in instructions:
            if "=" in instr:
                tokens = set(instr.split("=")[1].split(" "))
            if "->" in instr:
                tokens = set(instr.split("->")[1].split(" "))
            common_vars = list(tokens.intersection(list(g_vars.keys())))
            common_state_vars.extend(common_vars)
        if len(common_state_vars) > 0:
            var_dependency[block['addr']] = common_state_vars

    temp_var_list = []
    for g_var in g_vars.keys():
        addrs = g_vars[g_var]
        for addr in addrs:
            if var_dependency.get(addr) is None:
                if g_var not in temp_var_list:
                    temp_var_list.insert(0, g_var)

    for g_var in g_vars.keys():
        for addr in g_vars[g_var]:
            if var_dependency.get(addr) is not None:
                insert_vars(temp_var_list, g_vars, var_dependency, g_var)

    global_vars_list = copy.copy(temp_var_list)

    for contract in slither_obj.contracts:
        for state_variable in contract.state_variables:
            if state_variable not in state_vars:
                if str(state_variable) not in global_vars_list:
                    sv_list.append(state_variable)
                else:
                    index = global_vars_list.index(str(state_variable))
                    state_vars.insert(index, state_variable)
    state_vars = sv_list + state_vars

    for s_var in state_vars + list(solidity_special_vars.keys()):
        variable_details = {}

        if s_var not in solidity_special_vars.keys():
            if str(s_var) in g_vars.keys():
                variable_details['name'] = str(s_var)
                variable_details['type'] = get_type_information(s_var, log)
                variable_details['init'] = g_vars[str(s_var)]
                global_vars.append(variable_details)

            elif str(s_var) in g_constant_vars.keys():
                variable_details['name'] = str(s_var)
                variable_details['type'] = get_type_information(s_var, log)
                variable_details['init'] = g_constant_vars[str(s_var)]
                global_constant_vars.append(variable_details)

            else:
                variable_details['name'] = str(s_var)
                variable_details['type'] = get_type_information(s_var, log)
                variable_details['init'] = []
                global_vars.append(variable_details)

        else:
            if str(s_var) in initialize_special_vars.keys():
                variable_details['name'] = str(s_var)
                variable_details['type'] = [solidity_special_vars[s_var]]
                json_block = JsonBlock(initialize_special_vars[str(s_var)], '__GLOBAL__')
                json_block_dict = json_block.get_block_dict()
                g_blocks.append(json_block_dict)
                variable_details['init'] = json_block_dict['addr']

            else:
                variable_details['name'] = str(s_var)
                variable_details['type'] = [solidity_special_vars[s_var]]
                variable_details['init'] = []

            solidity_vars.append(variable_details)

    for contract in slither_obj.contracts:
        variable_details = {}
        variable_details['name'] = str(contract)
        variable_details['type'] = ['integer']
        variable_details['init'] = []
        global_vars.append(variable_details)

    global_vars = solidity_vars + global_solidity_functions + global_constant_vars + global_vars
    return global_vars

def get_localvar_type(local_var, log):
    if type(local_var.type).__name__ == 'MappingType':
        type_info = get_localvar_type(local_var.type.type_from, log) + " " + get_localvar_type(local_var.type.type_to, log)

    elif type(local_var.type).__name__ == 'ElementaryType':
        type_info = get_localvar_type(local_var.type, log)

    elif type(local_var.type).__name__ == 'UserDefinedType':
        if type(local_var.type.type).__name__ == 'ContractSolc04':
            type_info = 'integer'

        elif type(local_var.type.type).__name__ == 'StructureSolc':
            type_info = str(local_var.type.type.name)

        elif type(local_var.type.type).__name__ == 'Enum':
            type_info = str(local_var.type.type.name)

        else:
            type_info = 'unknown'

    elif type(local_var.type).__name__ == 'ArrayType':
        type_info = get_localvar_type(local_var.type.type, log)

    elif local_var.type == 'address':
        type_info = 'integer'

    elif local_var.type == 'bool':
        type_info = 'boolean'

    elif local_var.type.startswith('int'):
        type_info = 'integer'

    elif local_var.type.startswith('uint'):
        type_info = 'integer'

    elif local_var.type.startswith('bytes'):
        type_info = 'integer'

    else:
        type_info = 'unknown'

    return type_info

def patch_constant_str_bool():
  # this patch update the str value of a bool constant in Slither IR
  # where originally it displays "True" but now "true" ("False" but now "false")
  # which corresponds with the Solidity language
	def new_str(self):
		if isinstance(self.value,bool):
			return str(self.value).lower()
		else:
			return str(self.value)
	Constant.__str__ = new_str

def create_uninterpretable_functions(instr):
    solidity_func_name = instr.function.name

    if NOP_FUNCTIONS.get(solidity_func_name) is not None:
        if hasattr(instr, 'lvalue'):
            str_instr = str(instr.lvalue) + " := " + "NEW_VAL integer"
        else:
            str_instr = "NOP"

    elif UNINTERPRETABLE_FUNCTIONS.get(solidity_func_name) is not None:

        if solidity_func_name.startswith("this"):
            str_instr = str(UNINTERPRETABLE_FUNCTIONS[solidity_func_name][0])

        else:
            arguments = instr.arguments

            if len(arguments) == 0:
                str_instr = []
                temp_var = str(TemporaryVariable(" "))
                instr_1 = str(temp_var) + " = " + UNINTERPRETABLE_FUNCTIONS[solidity_func_name][1]
                str_instr.append(instr_1)

                instr_2 = str(instr.lvalue) + " = " + UNINTERPRETABLE_FUNCTIONS[solidity_func_name][0] \
                    + " " + str(temp_var)
                str_instr.append(instr_2)

                UNINTERPRETABLE_FUNCTIONS[solidity_func_name][1] += UNINTERPRETABLE_FUNCTIONS[solidity_func_name][1]

            else:
                str_instrs = []
                function_type = UNINTERPRETABLE_FUNCTIONS[solidity_func_name][0]

                if function_type.startswith('CALL1'):
                    loop = 1

                elif function_type.startswith('CALL2'):
                    loop = 2

                elif function_type.startswith('CALL3'):
                    loop = 3
                else:
                    loop = 4

                str_instr = str(instr.lvalue) + " = " + UNINTERPRETABLE_FUNCTIONS[solidity_func_name][0]

                count = 0
                for argument in arguments:
                    if count >= loop:
                        break
                    if str(argument.type) == 'string':
                        if string_to_integer.get(str(argument)) is None:
                            string_to_integer[str(argument)] = UNINTERPRETABLE_FUNCTIONS[solidity_func_name][1]
                            UNINTERPRETABLE_FUNCTIONS[solidity_func_name][1] += \
                            UNINTERPRETABLE_FUNCTIONS[solidity_func_name][1]

                        temp_var = str(TemporaryVariable(" "))
                        instr_1 = str(temp_var) + " = " + str(string_to_integer[str(argument)])
                        str_instr += " " + str(temp_var)
                        str_instrs.append(instr_1)

                    else:
                        str_instr += " " + str(argument)

                    count += 1

                str_instrs.append(str_instr)
                str_instr = str_instrs
    else:
        str_instr = str(instr)

    return str_instr

def create_new_datastructure(instr):
    if type(instr).__name__ == 'NewArray':
        str_instr = str(instr.lvalue) + " := " + "NEW_COL " + str(instr.array_type)

    elif type(instr).__name__ == 'NewContract':
        str_instr = str(instr.lvalue) + " := " + "NEW_VAL " + "integer"

    elif type(instr).__name__ == 'NewElementaryType':
        str_instr = str(instr.lvalue) + " := " + "NEW_VAL " + str(instr.type)

    elif type(instr).__name__ == 'NewStructure':
        str_instr = str(instr.lvalue) + " := " + "NEW_VAL " + instr.structure_name

    else:
        str_instr = str(instr)

    return str_instr

def parse_reference_variable_names(instructions, log):
    str_instructions = []
    for instr in instructions:
        if type(instr).__name__ in external_calls and hasattr(instr, 'lvalue') and instr.lvalue is not None:
            if type(instr.lvalue.type).__name__ == 'UserDefinedType' and type(instr.lvalue.type.type).__name__ == 'ContractSolc04':
                instr.lvalue.set_type(int_type)

        str_instr = create_new_datastructure(instr)

        # Should consider modelling delete
        if type(instr).__name__ in NOPED_OUT:
            str_instr = 'NOP'

        elif type(instr).__name__ == 'SolidityCall':
            str_instr = create_uninterpretable_functions(instr)

        elif type(instr).__name__ == 'Member':
            var_left = instr.variable_left

            if type(var_left).__name__ == 'ContractSolc04':
                str_instr = str(instr.lvalue) + " -> " + str(instr.variable_right)

        elif type(instr).__name__ == 'Unpack':
            try:
                index_type = instr.tuple.type[instr.tuple.index]
                if type(index_type).__name__ == 'Elementary':
                    str_instr = str(instr.lvalue) + " := " + "NEW_VAL " + str(index_type)

                elif type(index_type).__name__ == 'ArrayType':
                    str_instr = str(instr.lvalue) + " := " + "NEW_COl " + "unknown"

                elif type(index_type).__name__ == 'UserDefinedType':

                    if type(index_type.type).__name__ == 'ContractSolc04':
                        str_instr = str(instr.lvalue) + " := " + "NEW_VAL " + "integer"

                    elif type(index_type.type).__name__ == 'StructureSolc':
                        str_instr = str(instr.lvalue) + " := " + "NEW_VAL " + str(index_type.type.name)

                    elif type(index_type.type).__name__ == 'Enum':
                        str_instr = str(instr.lvalue) + " := " + "NEW_VAL " + 'unknown'

                    else:
                        str_instr = str(instr.lvalue) + " := " + "NEW_VAL " + "unknown"

                else:
                    str_instr = str(instr.lvalue) + " := " + "NEW_VAL unknown"
            except:
                str_instr = str(instr.lvalue) + " := " + "NEW_VAL unknown"

        elif str(instr).startswith('EXPRESSION') or str(instr).startswith('BREAK'):
            str_instr = 'NOP'

        elif str(instr).startswith('INLINE') or str(instr).startswith('THROW') or str(instr).startswith('CONTINUE'):
            str_instr = 'NOP'

        elif type(instr).__name__ == 'Assignment':
            if type(instr.rvalue).__name__ == 'Constant' and type(instr.rvalue.type).__name__ == 'ElementaryType' \
                    and instr.rvalue.type.type == 'string':
                str_instr = str(instr.lvalue) + " := " + "NEW_VAL unknown"

            elif type(instr.rvalue.type).__name__ == 'ElementaryType' and instr.rvalue.type.type == 'string':
                str_instr = str(instr.lvalue) + " := " + "NEW_VAL unknown"

        elif type(instr).__name__ == 'Length':
            value = instr.value

            if str(value.type) == 'string' or str(value.type) == 'bytes':
                str_instr = str(instr.lvalue) + " = " + "NEW_VAL integer"

        elif type(instr).__name__ == 'TypeConversion':
            if type(instr.variable).__name__ == 'Constant':
                str_instr = str(instr.lvalue) + " = " + str(instr.variable)

            else:
                str_instr = str(instr.lvalue) + " = " + "NEW_VAL unknown"

        elif type(instr).__name__ == 'Binary':
            is_string = False

            for var in instr.used:
                if str(var.type) == 'string':
                    is_string = True
                    break
            if is_string:
                str_instr = str(instr.lvalue) + " := " + "NEW_VAL unknown"

        elif type(instr).__name__ == 'Index':
            var_right = instr.variable_right
            if str(var_right.type) == 'string':
                if global_imports.constants.get(str(var_right)) is not None:
                    str_instr = str(instr)
                    str_instr = str_instr.replace('price', str(global_imports.constants[str(var_right)]))
                else:
                    global_imports.constants[str(var_right)] = global_imports.str_count % 10
                    global_imports.str_count = global_imports.str_count + 1

        # Process the converted str_instr
        if isinstance(str_instr, list):
            str_instrs = str_instr

            for str_instr in str_instrs:
                # Get instruction tokens

                instr_tokens = str_instr.split(" ")
                if instr_tokens[0].startswith('REF_') and (instr_tokens[1] == ':=' or instr_tokens[1] == '='):

                    try:
                        instr_tokens[0] = CFG.refvar_names[instr_tokens[0]]

                    except:
                        log.error("This can occur due to slither insanity, for now we are bailing out!")
                        sys.exit(1)

                    str_instr = instr_tokens[0]
                    for token in instr_tokens[1:]:
                        str_instr = str_instr + " " + token

                str_instructions.append(str_instr)
        else:
            # Get instruction tokens
            instr_tokens = str_instr.split(" ")
            if instr_tokens[0].startswith('REF_') and (instr_tokens[1] == ':=' or instr_tokens[1] == '='):
                try:
                    token = CFG.refvar_names[instr_tokens[0]]
                    if token == 'LENGTH' or token == 'BALANCE':
                        pass

                    else:
                        instr_tokens[0] = token

                except:
                    log.error("This can occur due to slither insanity, for now we are bailing out!")
                    sys.exit(1)

                str_instr = instr_tokens[0]

                for token in instr_tokens[1:]:
                    str_instr = str_instr + " " + token

            str_instructions.append(str_instr)

    return str_instructions

    pass

def output_tod_amount_or_receiver_paths(slither_obj, file_n, result_dir, log, global_vars, global_constant_vars, range_vars, global_blocks, range_blocks, total_range_instructions, varnode, element, count, per_function_paths, symex_paths, tod_type):
    error_node = BasicBlock([Nop()])
    #symex_paths = {}
    output_json = {}
    #count = 0
    #per_function_paths = {}

    primary_function = element[0]
    matched_function = element[1]

    if per_function_paths.get(primary_function) is None:
        per_function_paths[primary_function] = []

    p_locals = ICFG.locals_to_declare[primary_function]
    parameters = {}

    if primary_function == matched_function:
        function_name_1 = primary_function.name + '_v1'
        function_name_2 = matched_function.name + '_v2'

    else:
        function_name_1 = matched_function.name
        function_name_2 = primary_function.name

    #function_name_1 = primary_function.name
    #function_name_2 = primary_function.name
    contract = primary_function.contract

    ### File Name ###
    output_json['file'] = str(file_n)

    ### Globals ###
    global_variables = copy.copy(global_vars[contract])
    global_constant_variables = copy.copy(global_constant_vars[contract])
    global_var_blocks = copy.copy(global_blocks[contract])
    output_json['global_structs'] = get_global_structs(log, slither_obj)
    output_json['global_enums'] = get_global_enums(log, slither_obj)
    output_json['global_variables'] = get_variables_and_types(slither_obj, global_variables,
                                                              global_constant_variables,
                                                              global_var_blocks, log)
    output_json['global_blocks'] = global_var_blocks

    ### Ranges ###
    output_json['range_variables'] = copy.copy(range_vars[contract])
    output_json['range_blocks'] = copy.copy(range_blocks[contract])

    ### Blocks ###
    output_json['root_addr'] = ''
    output_json['dest_addrs'] = []
    output_json['normal_blocks'] = []
    #count += 1

    path_graph = element[2]
    path_graph.add_node(error_node, function_type='P')
    graph = path_graph.copy(as_view=False)
    dest_node = []

    total_block_instructions = 0

    for node in graph.nodes:
        if node not in json_blocks_mapping.keys():
            scope_str = get_scope_for_blocks(path_graph, node, function_name_1, function_name_2)
            instructions = parse_reference_variable_names(node._instructions, log)

            # instructions = [str(x) for x in node._instructions]
            json_block = JsonBlock(instructions, scope_str)
            json_blocks_mapping[node] = json_block
            json_block_dict = json_block.get_block_dict()

        else:
            json_block_dict = json_blocks_mapping[node].get_block_dict()

        locals_undeclared = []

        if type(node._instructions[-1]).__name__ == 'NodeSolc' and node._instructions[-1].type == 0x0 and node._is_root == True:
            if path_graph.nodes[node]['function_type'] == 'P':
                locals_undeclared = ICFG.locals_to_declare[primary_function]

            else:
                locals_undeclared = ICFG.locals_to_declare[matched_function]
            '''
            else:
                log.warning("We should not be here! Debug what is the the issue!")
                sys.exit(1)
            '''

        for local_d in locals_undeclared:
            if type(local_d.type).__name__ == 'ElementaryType':
                var_creation_instr = str(local_d) + ' ' + ':=' + ' ' + 'NEW_VAL' + ' ' + get_localvar_type(local_d, log)
                json_block_dict['instructions'].append(var_creation_instr)

            elif type(local_d.type).__name__ == 'MappingType' or type(local_d.type).__name__ == 'ArrayType':
                var_creation_instr = str(local_d) + ' ' + ':=' + ' ' + 'NEW_COL' + ' ' + get_localvar_type(local_d, log)
                json_block_dict['instructions'].append(var_creation_instr)

            elif type(local_d.type).__name__ == 'UserDefinedType':
                if type(local_d.type.type).__name__ == 'ContractSolc04':
                    var_creation_instr = str(local_d) + ' ' + ':=' + ' ' + 'NEW_VAL' + ' ' + 'integer'
                    json_block_dict['instructions'].append(var_creation_instr)

                elif type(local_d.type.type).__name__ == 'StructureSolc':
                    var_creation_instr = str(local_d) + ' ' + ':=' + ' ' + 'NEW_VAL' + ' ' + str(
                        local_d.type.type.name)
                    json_block_dict['instructions'].append(var_creation_instr)

                elif type(local_d.type.type).__name__ == 'Enum':
                    var_creation_instr = str(local_d) + ' ' + ':=' + ' ' + 'NEW_VAL' + ' ' + 'unknown'
                    json_block_dict['instructions'].append(var_creation_instr)

                else:
                    log.warning('Any other userdefined type! debug')
                    sys.exit(1)
            else:
                log.warning('Different type of local variable, debug')
                sys.exit(1)

        successors, addrs = get_successors_block_address(path_graph, node, error_node)
        new_addrs = {}

        for successor in successors:
            if successor not in json_blocks_mapping.keys():
                instructions = parse_reference_variable_names(successor._instructions, log)

                # instructions = [str(x) for x in successor._instructions]
                scope_str = get_scope_for_blocks(path_graph, successor, function_name_1, function_name_2)
                json_blocks_mapping[successor] = JsonBlock(instructions, scope_str)

            new_addrs[json_blocks_mapping[successor].get_block_dict()['addr']] = addrs[hex(successor._block_id)]

        if len(new_addrs.keys()) != 0:
            if type(node._instructions[-1]).__name__ == 'Condition':
                for n_addr in new_addrs.keys():
                    if new_addrs[n_addr] == True:
                        true_addr = n_addr
                    else:
                        false_addr = n_addr

                try:
                    json_block_dict['instructions'][-1] = json_block_dict['instructions'][
                                                          -1] + ' ' + true_addr + ' ' + false_addr
                except:
                    log.warning("Undefined addresses in tod, debug!")
                    sys.exit(1)

            elif node._is_ext_call == True:
                jmp_instr = 'JUMP' + ' ' + list(new_addrs.keys())[0]

                if node._instructions[-1].lvalue != None:
                    lvalue = node._instructions[-1].lvalue

                    if type(lvalue.type).__name__ == 'ElementaryType':
                        ext_call_lvalue_instr = str(lvalue) + " := " + "NEW_VAL " + str(lvalue.type.type)

                    else:
                        if isinstance(lvalue.type, list):
                            ext_call_lvalue_instr = str(lvalue) + " := " + "NEW_COL " + "unknown"

                        else:
                            if type(lvalue.type).__name__ == 'UserDefinedType':
                                if type(lvalue.type.type).__name__ == 'ContractSolc04':
                                    ext_call_lvalue_instr = str(lvalue) + " := " + "NEW_VAL " + "integer"

                                elif type(lvalue.type.type).__name__ == 'StructureSolc':
                                    ext_call_lvalue_instr = str(lvalue) + " := " + "NEW_VAL " + str(
                                        lvalue.type.type.name)

                                elif type(lvalue.type.type).__name__ == 'Enum':
                                    ext_call_lvalue_instr = str(lvalue) + " := " + "NEW_VAL " + 'unknown'

                                else:
                                    ext_call_lvalue_instr = str(lvalue) + " := " + "NEW_VAL " + "unknown"
                            else:
                                ext_call_lvalue_instr = str(lvalue) + " := " + "NEW_VAL " + "unknown"
                else:
                    ext_call_lvalue_instr = None

                json_block_dict['instructions'] = json_block_dict['instructions'][:-1]

                if path_graph.nodes[node]['function_type'] == 'P':
                    json_block_dict['instructions'].append('ATTACK')

                    if ext_call_lvalue_instr != None:
                        json_block_dict['instructions'].append(ext_call_lvalue_instr)

                json_block_dict['instructions'].append(jmp_instr)

            else:
                jmp_instr = 'JUMP' + ' ' + list(new_addrs.keys())[0]
                json_block_dict['instructions'].append(jmp_instr)

        total_block_instructions += len(json_block_dict['instructions'])
        output_json['normal_blocks'].append(json_block_dict)

        # Get the block address for root basic block
        if path_graph.in_degree(node) == 0 and path_graph.out_degree(node) >= 1 and node._is_root is True:
            output_json['root_addr'] = json_block_dict['addr']
            src_node = str(node)

        # Get the block addresses for target basic blocks
        if path_graph.in_degree(node) >= 1 and path_graph.out_degree(node) == 0 and str(node._instructions[-1]) != 'NOP':
            # Fix if the last instruction is a Condition
            if json_block_dict['instructions'][-1].startswith('CONDITION'):
                json_block_dict['instructions'][-1] = 'NOP'
            output_json['dest_addrs'].append(json_block_dict['addr'])
            dest_node.append(str(node))

        '''
        if node._is_root is True and path_graph.nodes[node]['function_type'] == 'P':
            output_json['dest_addrs'].append(json_block_dict['addr'])
            dest_node.append(str(node))
        '''

    file_name = 'tod_' + 'symex_path' + '_' + str(count) + '.json'
    file_name_1 = 'tod_' + 'path_org' + '_' + str(count) + '.json'
    total_executable_instructions = total_range_instructions[contract] + total_block_instructions

    # symex_paths[file_name] = populate_output_paths(src_node, dest_node, varnode, function_name_2, function_name_1, total_executable_instructions, output_json)
    symex_paths[file_name] = populate_output_paths(src_node, dest_node, varnode, primary_function, matched_function, total_executable_instructions, output_json, tod_type)
    #dump_json(result_dir, output_json, file_name_1)

    # This is to call the post processing translation module in order to generate
    # a checker compatible IR
    new_json = invoke_post_processing_translation(output_json)
    dump_json(result_dir, new_json, file_name)
    per_function_paths[primary_function].append(file_name)

    # For now simply generate 100 sympaths
    #if count == 100:
        #break
    #return symex_paths, per_function_paths

def output_tod_paths(slither_obj, file_n, result_dir, log, global_vars, global_constant_vars, range_vars, global_blocks, range_blocks, total_range_instructions, varnode, element, count, per_function_paths, symex_paths):
    error_node = BasicBlock([Nop()])
    #symex_paths = {}
    output_json = {}
    #count = 0
    #per_function_paths = {}

    primary_function = element[0]

    if per_function_paths.get(primary_function) is None:
        per_function_paths[primary_function] = []

    p_locals = ICFG.locals_to_declare[primary_function]
    parameters = {}

    function_name_1 = primary_function.name
    function_name_2 = primary_function.name
    contract = primary_function.contract

    ### File Name ###
    output_json['file'] = str(file_n)

    ### Globals ###
    global_variables = copy.copy(global_vars[contract])
    global_constant_variables = copy.copy(global_constant_vars[contract])
    global_var_blocks = copy.copy(global_blocks[contract])
    output_json['global_structs'] = get_global_structs(log, slither_obj)
    output_json['global_enums'] = get_global_enums(log, slither_obj)
    output_json['global_variables'] = get_variables_and_types(slither_obj, global_variables,
                                                              global_constant_variables,
                                                              global_var_blocks, log)
    output_json['global_blocks'] = global_var_blocks

    ### Ranges ###
    output_json['range_variables'] = copy.copy(range_vars[contract])
    output_json['range_blocks'] = copy.copy(range_blocks[contract])

    ### Blocks ###
    output_json['root_addr'] = ''
    output_json['dest_addrs'] = []
    output_json['normal_blocks'] = []
    #count += 1

    path_graph = element[1]
    path_graph.add_node(error_node, function_type='P')
    graph = path_graph.copy(as_view=False)
    dest_node = []

    total_block_instructions = 0

    for node in graph.nodes:
        if node not in json_blocks_mapping.keys():
            scope_str = get_scope_for_blocks(path_graph, node, function_name_1, function_name_2)
            instructions = parse_reference_variable_names(node._instructions, log)

            # instructions = [str(x) for x in node._instructions]
            json_block = JsonBlock(instructions, scope_str)
            json_blocks_mapping[node] = json_block
            json_block_dict = json_block.get_block_dict()

        else:
            json_block_dict = json_blocks_mapping[node].get_block_dict()

        locals_undeclared = []

        if type(node._instructions[-1]).__name__ == 'NodeSolc' and node._instructions[-1].type == 0x0 and node._is_root == True:
            if path_graph.nodes[node]['function_type'] == 'P':
                locals_undeclared = ICFG.locals_to_declare[primary_function]

            '''
            else:
                log.warning("We should not be here! Debug what is the the issue!")
                sys.exit(1)
            '''

        for local_d in locals_undeclared:
            if type(local_d.type).__name__ == 'ElementaryType':
                var_creation_instr = str(local_d) + ' ' + ':=' + ' ' + 'NEW_VAL' + ' ' + get_localvar_type(local_d, log)
                json_block_dict['instructions'].append(var_creation_instr)

            elif type(local_d.type).__name__ == 'MappingType' or type(local_d.type).__name__ == 'ArrayType':
                var_creation_instr = str(local_d) + ' ' + ':=' + ' ' + 'NEW_COL' + ' ' + get_localvar_type(local_d, log)
                json_block_dict['instructions'].append(var_creation_instr)

            elif type(local_d.type).__name__ == 'UserDefinedType':
                if type(local_d.type.type).__name__ == 'ContractSolc04':
                    var_creation_instr = str(local_d) + ' ' + ':=' + ' ' + 'NEW_VAL' + ' ' + 'integer'
                    json_block_dict['instructions'].append(var_creation_instr)

                elif type(local_d.type.type).__name__ == 'StructureSolc':
                    var_creation_instr = str(local_d) + ' ' + ':=' + ' ' + 'NEW_VAL' + ' ' + str(
                        local_d.type.type.name)
                    json_block_dict['instructions'].append(var_creation_instr)

                elif type(local_d.type.type).__name__ == 'Enum':
                    var_creation_instr = str(local_d) + ' ' + ':=' + ' ' + 'NEW_VAL' + ' ' + 'unknown'
                    json_block_dict['instructions'].append(var_creation_instr)

                else:
                    log.warning('Any other userdefined type! debug')
                    sys.exit(1)
            else:
                log.warning('Different type of local variable, debug')
                sys.exit(1)

        successors, addrs = get_successors_block_address(path_graph, node, error_node)
        new_addrs = {}

        for successor in successors:
            if successor not in json_blocks_mapping.keys():
                instructions = parse_reference_variable_names(successor._instructions, log)

                # instructions = [str(x) for x in successor._instructions]
                scope_str = get_scope_for_blocks(path_graph, successor, function_name_1, function_name_2)
                json_blocks_mapping[successor] = JsonBlock(instructions, scope_str)

            new_addrs[json_blocks_mapping[successor].get_block_dict()['addr']] = addrs[hex(successor._block_id)]

        if len(new_addrs.keys()) != 0:
            if type(node._instructions[-1]).__name__ == 'Condition':
                for n_addr in new_addrs.keys():
                    if new_addrs[n_addr] == True:
                        true_addr = n_addr
                    else:
                        false_addr = n_addr

                try:
                    json_block_dict['instructions'][-1] = json_block_dict['instructions'][
                                                          -1] + ' ' + true_addr + ' ' + false_addr
                except:
                    log.warning("Undefined addresses in tod, debug!")
                    sys.exit(1)

            elif node._is_ext_call == True:
                jmp_instr = 'JUMP' + ' ' + list(new_addrs.keys())[0]

                if node._instructions[-1].lvalue != None:
                    lvalue = node._instructions[-1].lvalue

                    if type(lvalue.type).__name__ == 'ElementaryType':
                        ext_call_lvalue_instr = str(lvalue) + " := " + "NEW_VAL " + str(lvalue.type.type)

                    else:
                        if isinstance(lvalue.type, list):
                            ext_call_lvalue_instr = str(lvalue) + " := " + "NEW_COL " + "unknown"

                        else:
                            if type(lvalue.type).__name__ == 'UserDefinedType':
                                if type(lvalue.type.type).__name__ == 'ContractSolc04':
                                    ext_call_lvalue_instr = str(lvalue) + " := " + "NEW_VAL " + "integer"

                                elif type(lvalue.type.type).__name__ == 'StructureSolc':
                                    ext_call_lvalue_instr = str(lvalue) + " := " + "NEW_VAL " + str(
                                        lvalue.type.type.name)

                                elif type(lvalue.type.type).__name__ == 'Enum':
                                    ext_call_lvalue_instr = str(lvalue) + " := " + "NEW_VAL " + 'unknown'

                                else:
                                    ext_call_lvalue_instr = str(lvalue) + " := " + "NEW_VAL " + "unknown"
                            else:
                                ext_call_lvalue_instr = str(lvalue) + " := " + "NEW_VAL " + "unknown"
                else:
                    ext_call_lvalue_instr = None

                json_block_dict['instructions'] = json_block_dict['instructions'][:-1]

                if path_graph.nodes[node]['function_type'] == 'P':
                    json_block_dict['instructions'].append('ATTACK')

                    if ext_call_lvalue_instr != None:
                        json_block_dict['instructions'].append(ext_call_lvalue_instr)

                json_block_dict['instructions'].append(jmp_instr)

            else:
                jmp_instr = 'JUMP' + ' ' + list(new_addrs.keys())[0]
                json_block_dict['instructions'].append(jmp_instr)

        total_block_instructions += len(json_block_dict['instructions'])
        output_json['normal_blocks'].append(json_block_dict)

        # Get the block address for root basic block
        if path_graph.in_degree(node) == 0 and path_graph.out_degree(node) >= 1 and node._is_root is True:
            output_json['root_addr'] = json_block_dict['addr']
            src_node = str(node)

        # Get the block addresses for target basic blocks
        if path_graph.in_degree(node) >= 1 and path_graph.out_degree(node) == 0 and str(node._instructions[-1]) != 'NOP':
            # Fix if the last instruction is a Condition
            if json_block_dict['instructions'][-1].startswith('CONDITION'):
                json_block_dict['instructions'][-1] = 'NOP'
            output_json['dest_addrs'].append(json_block_dict['addr'])
            dest_node.append(str(node))

        '''
        if node._is_root is True and path_graph.nodes[node]['function_type'] == 'P':
            output_json['dest_addrs'].append(json_block_dict['addr'])
            dest_node.append(str(node))
        '''

    file_name = 'tod_' + 'symex_path' + '_' + str(count) + '.json'
    file_name_1 = 'tod_' + 'path_org' + '_' + str(count) + '.json'
    total_executable_instructions = total_range_instructions[contract] + total_block_instructions

    # symex_paths[file_name] = populate_output_paths(src_node, dest_node, varnode, function_name_2, function_name_1, total_executable_instructions, output_json)
    symex_paths[file_name] = populate_output_paths(src_node, dest_node, varnode, primary_function, None, total_executable_instructions, output_json, 'tod_transfer')
    #dump_json(result_dir, output_json, file_name_1)

    # This is to call the post processing translation module in order to generate
    # a checker compatible IR
    new_json = invoke_post_processing_translation(output_json)
    dump_json(result_dir, new_json, file_name)
    per_function_paths[primary_function].append(file_name)

    # For now simply generate 100 sympaths
    #if count == 100:
        #break
    #return symex_paths, per_function_paths

def compute_range_blocks(slither_obj, vrg_obj, log):
    patch_constant_str_bool()
    global_vars, global_constant_vars, range_vars, global_blocks, range_blocks = get_statevar_assignments(slither_obj, vrg_obj)

    total_range_instructions = {}
    for contract in range_blocks.keys():
        blocks = range_blocks[contract]

        for block in blocks:
            if total_range_instructions.get(contract) is None:
                total_range_instructions[contract] = 0
            total_range_instructions[contract] += len(block['instructions'])

    return global_vars, global_constant_vars, range_vars, global_blocks, range_blocks, total_range_instructions

def output_ir_paths_new(slither_obj, vrg_obj, dao_feasible_paths, tod_feasible_paths, file_n, result_dir, log):


    dao_symex_paths, dao_per_function_paths = output_dao_paths(slither_obj, vrg_obj, dao_feasible_paths, file_n, result_dir, log, global_vars,
                     global_constant_vars, range_vars, global_blocks, range_blocks, total_range_instructions)

    tod_symex_paths, tod_per_function_paths = output_tod_paths(slither_obj, vrg_obj, tod_feasible_paths, file_n, result_dir, log, global_vars,
                     global_constant_vars, range_vars, global_blocks, range_blocks, total_range_instructions)


    return dao_symex_paths, dao_per_function_paths, tod_symex_paths, tod_per_function_paths

def output_dao_paths(slither_obj, file_n, result_dir, log, global_vars, global_constant_vars, range_vars, global_blocks, range_blocks, total_range_instructions, varnode, element, count, per_function_paths, symex_paths):
    error_node = BasicBlock([Nop()])
    output_json = {}

    primary_function = element[0]
    matched_function = element[1]

    if per_function_paths.get(primary_function) is None:
        per_function_paths[primary_function] = []

    p_locals = ICFG.locals_to_declare[primary_function]
    m_locals = ICFG.locals_to_declare[matched_function]
    parameters = {}

    if primary_function == matched_function:
        function_name_1 = primary_function.name + '_v1'
        function_name_2 = matched_function.name + '_v2'
    else:
        function_name_1 = primary_function.name
        function_name_2 = matched_function.name

    contract = primary_function.contract

    ### File Name ###
    output_json['file'] = str(file_n)

    ### Globals ###
    output_json['global_structs'] = get_global_structs(log, slither_obj)
    output_json['global_enums'] = get_global_enums(log, slither_obj)
    output_json['global_variables'] = get_variables_and_types(slither_obj, global_vars[contract], global_constant_vars[contract], global_blocks[contract], log)
    output_json['global_blocks'] = global_blocks[contract]

    ### Ranges ###
    output_json['range_variables'] = range_vars[contract]
    output_json['range_blocks'] = range_blocks[contract]

    ### Blocks ###
    output_json['root_addr'] = ''
    output_json['dest_addrs'] = []
    output_json['normal_blocks'] = []
    #count += 1


    path_graph = element[2]
    path_graph.add_node(error_node, function_type='G')
    graph = path_graph.copy(as_view=False)
    dest_node = []

    total_block_instructions = 0

    for node in graph.nodes:
        if node not in json_blocks_mapping.keys():
            scope_str = get_scope_for_blocks(path_graph, node, function_name_1, function_name_2)
            instructions = parse_reference_variable_names(node._instructions, log)

            #instructions = [str(x) for x in node._instructions]
            json_block = JsonBlock(instructions, scope_str)
            json_blocks_mapping[node] = json_block
            json_block_dict = json_block.get_block_dict()

        else:
            json_block_dict = json_blocks_mapping[node].get_block_dict()


        locals_undeclared = []

        if type(node._instructions[-1]).__name__ == 'NodeSolc' and node._instructions[-1].type == 0x0 and node._is_root == True:
            if path_graph.nodes[node]['function_type'] == 'P':
                locals_undeclared = ICFG.locals_to_declare[primary_function]

            else:
                locals_undeclared = ICFG.locals_to_declare[matched_function]

        for local_d in locals_undeclared:
            if type(local_d.type).__name__ == 'ElementaryType':
                var_creation_instr = str(local_d) + ' ' + ':=' + ' ' + 'NEW_VAL' + ' ' + get_localvar_type(local_d, log)
                json_block_dict['instructions'].append(var_creation_instr)

            elif type(local_d.type).__name__ == 'MappingType' or type(local_d.type).__name__ == 'ArrayType':
                var_creation_instr = str(local_d) + ' ' + ':=' + ' ' + 'NEW_COL' + ' ' + get_localvar_type(local_d, log)
                json_block_dict['instructions'].append(var_creation_instr)

            elif type(local_d.type).__name__ == 'UserDefinedType':
                if type(local_d.type.type).__name__ == 'ContractSolc04':
                    var_creation_instr = str(local_d) + ' ' + ':=' + ' ' + 'NEW_VAL' + ' ' + 'integer'
                    json_block_dict['instructions'].append(var_creation_instr)

                elif type(local_d.type.type).__name__ == 'StructureSolc':
                    var_creation_instr = str(local_d) + ' ' + ':=' + ' ' + 'NEW_VAL' + ' ' + str(local_d.type.type.name)
                    json_block_dict['instructions'].append(var_creation_instr)

                elif type(local_d.type.type).__name__ == 'Enum':
                    var_creation_instr = str(local_d) + ' ' + ':=' + ' ' + 'NEW_VAL' + ' ' + 'unknown'
                    json_block_dict['instructions'].append(var_creation_instr)

                else:
                    log.warning('Any other userdefined type! debug')
                    sys.exit(1)
            else:
                log.warning('Different type of local variable, debug')
                sys.exit(1)

        successors, addrs = get_successors_block_address(path_graph, node, error_node)
        new_addrs = {}

        for successor in successors:
            if successor not in json_blocks_mapping.keys():
                instructions = parse_reference_variable_names(successor._instructions, log)

                #instructions = [str(x) for x in successor._instructions]
                scope_str = get_scope_for_blocks(path_graph, successor, function_name_1, function_name_2)
                json_blocks_mapping[successor] = JsonBlock(instructions, scope_str)

            new_addrs[json_blocks_mapping[successor].get_block_dict()['addr']] = addrs[hex(successor._block_id)]

        if len(new_addrs.keys()) != 0:
            if type(node._instructions[-1]).__name__ == 'Condition':
                for n_addr in new_addrs.keys():
                    if new_addrs[n_addr] == True:
                        true_addr = n_addr
                    else:
                        false_addr = n_addr
                try:
                    json_block_dict['instructions'][-1] = json_block_dict['instructions'][-1] + ' ' + true_addr + ' ' + false_addr
                except:
                    log.warning("Undefined addresess, debug!")
                    sys.exit(1)

            elif node._is_ext_call == True:
                jmp_instr = 'JUMP' + ' ' + list(new_addrs.keys())[0]

                if node._instructions[-1].lvalue != None:
                    lvalue = node._instructions[-1].lvalue

                    if type(lvalue.type).__name__ == 'ElementaryType':
                        ext_call_lvalue_instr = str(lvalue) + " := " + "NEW_VAL " + str(lvalue.type.type)

                    else:
                        if isinstance(lvalue.type, list):
                            ext_call_lvalue_instr = str(lvalue) + " := " + "NEW_COL " + "unknown"

                        else:
                            if type(lvalue.type).__name__ == 'UserDefinedType':
                                if type(lvalue.type.type).__name__ == 'ContractSolc04':
                                    ext_call_lvalue_instr = str(lvalue) + " := " + "NEW_VAL " + "integer"

                                elif type(lvalue.type.type).__name__ == 'StructureSolc':
                                    ext_call_lvalue_instr = str(lvalue) + " := " + "NEW_VAL " + str(lvalue.type.type.name)

                                elif type(lvalue.type.type).__name__ == 'Enum':
                                    ext_call_lvalue_instr = str(lvalue) + " := " + "NEW_VAL " + 'unknown'

                                else:
                                    ext_call_lvalue_instr = str(lvalue) + " := " + "NEW_VAL " + "unknown"
                            else:
                                ext_call_lvalue_instr = str(lvalue) + " := " + "NEW_VAL " + "unknown"
                else:
                    ext_call_lvalue_instr = None

                json_block_dict['instructions'] = json_block_dict['instructions'][:-1]

                if path_graph.nodes[node]['function_type'] == 'P':
                    json_block_dict['instructions'].append('ATTACK')

                    if ext_call_lvalue_instr != None:
                        json_block_dict['instructions'].append(ext_call_lvalue_instr)


                json_block_dict['instructions'].append(jmp_instr)

            else:
                jmp_instr = 'JUMP' + ' ' + list(new_addrs.keys())[0]
                json_block_dict['instructions'].append(jmp_instr)

        total_block_instructions += len(json_block_dict['instructions'])
        output_json['normal_blocks'].append(json_block_dict)

        # Get the block address for root basic block
        if path_graph.in_degree(node) == 0 and path_graph.out_degree(node) >= 1 and node._is_root is True:
            output_json['root_addr'] = json_block_dict['addr']
            src_node = str(node)

        # Get the block addresses for target basic blocks
        if path_graph.in_degree(node) >= 1 and path_graph.out_degree(node) == 0 and str(node._instructions[-1]) != 'NOP' and path_graph.nodes[node]['function_type'] != 'G':
            # Fix if the last instruction is a Condition
            if json_block_dict['instructions'][-1].startswith('CONDITION'):
                json_block_dict['instructions'][-1] = 'NOP'
            output_json['dest_addrs'].append(json_block_dict['addr'])
            dest_node.append(str(node))

    file_name = 'dao_symex_path' + '_' + str(count) + '.json'
    file_name_1 = 'dao_path_org' + '_' + str(count) + '.json'
    total_executable_instructions = total_range_instructions[contract] + total_block_instructions

    #symex_paths[file_name] = populate_output_paths(src_node, dest_node, varnode, function_name_2, function_name_1, total_executable_instructions, output_json)
    symex_paths[file_name] = populate_output_paths(src_node, dest_node, varnode, primary_function, matched_function, total_executable_instructions, output_json, 'dao')
    #dump_json(result_dir, output_json, file_name_1)

    # This is to call the post processing translation module in order to generate
    # a checker compatible IR
    new_json = invoke_post_processing_translation(output_json)
    dump_json(result_dir, new_json, file_name)
    per_function_paths[primary_function].append(file_name)

    #return symex_paths, per_function_paths

def get_scope_for_blocks(path_graph, node, function_name_1, function_name_2):

    if path_graph.nodes[node]['function_type'] == 'P':
        scope_str = function_name_1

    elif path_graph.nodes[node]['function_type'] == 'M':
        scope_str = function_name_2

    else:
        scope_str = 'trap'

    return scope_str

def populate_output_paths(src_node, dest_node, variable, primary_function, matched_function, total_instructions, output_json, bug_type):
    symex_json = {}
    #symex_json['contract'] = output_json['contract']
    symex_json['file_name'] = ""
    symex_json['from_function'] = primary_function.name
    if matched_function is not None:
        symex_json['to_function'] = matched_function.name
    symex_json['bug_type'] = bug_type
    symex_json['src_node'] = src_node
    symex_json['dest_node'] = dest_node
    symex_json['executable_instructions'] = total_instructions
    symex_json['state_variable'] = str(variable)
    symex_json['error'] = ""
    symex_json['result'] = ""
    symex_json['execution_details'] = ""
    return symex_json


