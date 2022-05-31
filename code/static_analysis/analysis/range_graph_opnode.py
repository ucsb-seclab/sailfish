import slither
import shutil
import os
import pydot
import glob
import traceback
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
from value_node import *
from range_node import *
from op_node import *
import traceback


CONSTANT_TYPES = ['int', 'str', 'Constant']
VARIABLE_TYPES = ['StateVariableSolc', 'LocalVariableSolc']
DESIRABLE_TYPES = ['StateVariableSolc', 'int', 'Constant', 'str']
function_visibility = ['public', 'external']

class VRG:
    varnode_list = []
    contract_vars = {}
    map_svars_to_struct = {}
    map_svars_to_sobj = {}

    def __init__(self, slither_obj, callgraph, sdg_objects, graph_dir):
        self.slither_obj = slither_obj
        self.sdg_objects = sdg_objects
        self.graph_dir = graph_dir
        self.callgraph = callgraph
        self._ref_to_state = {}
        self.value_graph = {}
        self._variable_taint = {}
        self._summarized_libraries = ['sub', 'mul', 'div', 'add']
        self.setup()

    def print_VRG(self):
        for cfg_obj in self.value_graph.keys():
            for svar_obj in self.value_graph[cfg_obj].keys():
                triplets = self.value_graph[cfg_obj][svar_obj]
                index = 1
                
                for triplet in triplets:
                    self.print_cfg_dot(self.graph_dir, triplet[0], triplet[1], index)
                    index += 1


    def setup(self):
        leaf_nodes = self.get_leaf_function_nodes(self.callgraph._callgraph)
        root_nodes = self.get_root_function_nodes(self.callgraph._callgraph)
        
        for root_node in root_nodes:
            if root_node._function.visibility in function_visibility:
                print(root_node._function.name)
                cfg_obj = CFG.function_cfg[root_node._function]
                for parameter in cfg_obj._function.parameters:
                    self._variable_taint[parameter] = 'U'
            
        for leaf_node in leaf_nodes:
            contract = leaf_node._contract
            function = leaf_node._function
            cfg_obj = self.generate_cfgs(contract, function)
            self.process_functions(cfg_obj)
        
        #self.print_VRG()
        self.process_bottom_up(leaf_nodes, self.callgraph._callgraph)
    
    
    def process_bottom_up(self, leaf_nodes, graph):
        processed_nodes = []
        processed_nodes.extend(leaf_nodes)
        processed_stack = []
        processed_stack.extend(leaf_nodes)
        
        while len(processed_stack) != 0:
            node = processed_stack.pop(0)

            if node not in processed_nodes:
                contract = node._contract
                function = node._function
                cfg_obj = self.generate_cfgs(contract, function)
                self.process_nonleaf_functions(cfg_obj)
                processed_nodes.append(node)
             
            predecessors = graph.predecessors(node)
            
            for predecessor in predecessors:
                 # Alert! We need to convert to list first and the assign, otherwise if we directly do list(successors) after assignment
                 # next list(successors) return empty list
                successors = list(graph.successors(predecessor))
                left = list(set(successors) - set(processed_nodes))
                
                if len(left) == 0:
                    processed_stack.append(predecessor)
        
    def get_state_var_obj(self, var):
        if var not in SDG.map_svars_to_struct.keys():
            return SDG.map_svars_to_sobj[var]
        
        else:
            pass
    
    def process_variable_left(self, var_left, cfg_obj, instr, parameters=[], parent=None, node=None, graph=None):
        s_lvar = None
        s_rvar = None
        type_str = None        
        
        if type(var_left).__name__ == 'TemporaryVariable':
            s_lvar, s_rvar, type_str = self.process_temporary_variable(var_left, cfg_obj, parameters, parent, node, graph)

        else:
            if type(var_left).__name__ == 'StateVariableSolc':
                s_lvar = self.get_state_var_obj(var_left)

            if type(var_left).__name__ == 'ReferenceVariable':
                s_lvar = self.get_origin_variable_from_refvariable(instr, var_left, cfg_obj)  
            
            if type(var_left).__name__ == 'Constant':
                s_lvar = var_left.value
            
            if type(var_left).__name__ == 'LocalVariableSolc':
                if var_left in parameters:
                    s_lvar = var_left
                
                else:
                    print("This should not be executed!")

        return s_lvar
    
    def process_variable_right(self, var_right, cfg_obj, instr, parameters=[], parent=None, node=None, graph=None):
        s_lvar = None
        s_rvar = None
        type_str = None
        
        if type(var_right).__name__ == 'TemporaryVariable':
            s_lvar, s_rvar, type_str = self.process_temporary_variable(var_right, cfg_obj, parameters, parent, node, graph)
        
        else:
            if type(var_right).__name__ == 'StateVariableSolc':
                s_rvar = self.get_state_var_obj(var_right)
            
            if type(var_right).__name__ == 'SolidityVariableComposed':
                s_rvar = var_right
            
            if type(var_right).__name__ == 'Constant':
                s_rvar = var_right.value
            
            if type(var_right).__name__ == 'LocalVariableSolc':
                if var_right in parameters:
                    s_rvar = var_right
                
                else:
                    print("This should not be executed!")

            if type(var_right).__name__ == 'ReferenceVariable':
                s_rvar = self.get_origin_variable_from_refvariable(instr, var_right, cfg_obj)

        return s_rvar
    
    def perform_arithmetic_op(self, arg1, arg2, op):
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

    def process_temporary_variable(self, variable, cfg_obj, parameters=[], parent=None, node=None, graph=None):
        instrs = cfg_obj._vars_written[variable]
        s_lvar = None
        s_rvar = None
        type_str = None

        for instr in instrs:
            if type(instr).__name__ == 'Binary':
                var_left = instr.variable_left
                var_right = instr.variable_right
                type_str = instr.type_str
                s_lvar = self.process_variable_left(var_left, cfg_obj, instr, parameters, parent, node, graph)
                s_rvar = self.process_variable_right(var_right, cfg_obj, instr, parameters, parent, node, graph)
                
                if type_str == '&&' or type_str == '||':
                    pass
                
                elif type_str == '-' or type_str == '+' or type_str == '*' or type_str == '/' or type_str == '**':
                    if type(s_lvar).__name__ == 'int' and type(s_rvar).__name__ == 'int':
                        s_lvar = self.perform_arithmetic_op(s_lvar, s_rvar, type_str)
                        s_rvar = None
                        type_str = None
                    else:
                        op_node = OpNode(s_lvar, type_str, s_rvar)
                        s_lvar = op_node
                        s_rvar = None
                        type_str = None

                else:
                    try:
                        range_node = RangeNode(s_lvar, parent, s_rvar, type_str)
                        graph.add_edge(range_node, node)
                    
                    except:
                        print(": To be filled up")

            elif type(instr).__name__ == 'TypeConversion':
                var_right = instr.read[0]
                s_rvar = self.process_variable_right(var_right, cfg_obj, instr, parameters, parent, node, graph)

            elif type(instr).__name__ == 'Assignment':
                rvalue = self.process_variable_right(instr.rvalue, cfg_obj, instr, parameters)

            
            elif type(instr).__name__ == 'InternelCall':
                pass
            
            elif type(instr).__name__ == 'HighLevelCall':
                pass
            
            elif type(instr).__name__ == 'LibraryCall':
                callee  = instr.function
                caller_arguments = instr.arguments
                temp_arr = []
                return_list = self.map_callee_returns_to_caller_args(callee, caller_arguments)
                # Arguments of the call can be temporary variables, constants, state vars or reference vars. 
                # We need to get the actual source of the var
                
                try:
                    for value in return_list:
                        if isinstance(value, OpNode):
                            lvalue = value.left_value
                            rvalue = value.right_value
                            
                            value.left_value = self.get_call_arguments_origin(lvalue, instr, parameters, cfg_obj)
                            value.right_value = self.get_call_arguments_origin(rvalue, instr, parameters, cfg_obj)
                            temp_arr.append(value)
                        
                        else:
                            temp_arr.append(self.get_call_arguments_origin(value, instr, parameters, cfg_obj))
                except:
                    print("Error")

                s_lvar = temp_arr
            
            return s_lvar, s_rvar, type_str
    
    def process_right(self, rvalue):
        if isinstance(rvalue, OpNode):
            return self.recursively_process_op_node(rvalue)
        else:
            return rvalue

    def process_left(self, lvalue):
        if isinstance(lvalue, OpNode):
            return self.recursively_process_op_node(lvalue)
        else:
            return lvalue
    
    def recursively_process_op_node(self, opnode):
        lvalue = self.process_left(opnode.left_value)
        rvalue = self.process_right(opnode.right_value)

        return lvalue, rvalue, opnode.op_str
        
    def map_callee_returns_to_caller_args(self, callee_function, call_arguments):
        # Callee function's return values and parameters
        function_returns = CFG.function_cfg[callee_function]._return_summary
        function_parameters = callee_function.parameters
        return_list = []

        for return_key in function_returns.keys():
            function_return = function_returns[return_key]

            if isinstance(function_return, OpNode):
                lvalue, rvalue, op_str = self.recursively_process_op_node(function_return)
                opnode = OpNode(lvalue, op_str, rvalue)
                
                if type(lvalue).__name__ in DESIRABLE_TYPES and type(rvalue).__name__ in DESIRABLE_TYPES:
                    opnode.left_value = lvalue
                    opnode.right_value = rvalue
                
                else:
                    if lvalue in function_parameters:
                        index = function_parameters.index(lvalue)
                        caller_var = call_arguments[index]
                        opnode.left_value = caller_var
                    
                    if type(lvalue).__name__  in DESIRABLE_TYPES:
                        opnode.left_value = lvalue
                    
                    if rvalue in function_parameters:
                        index = function_parameters.index(rvalue)
                        caller_var = call_arguments[index]
                        opnode.right_value = caller_var                
                    
                    if type(rvalue).__name__  in DESIRABLE_TYPES:
                        opnode.right_value = rvalue
                    
                    else:
                        print("What happens if callee return values are not caller arguments!")

                    return_list.append(opnode)
            
            else:
                if function_return in function_parameters:
                    index = function_parameters.index(function_return)
                    caller_var = call_arguments[index]
                    return_list.append(caller_var)
                
                elif type(function_return) == 'StateVariableSolc':
                    return_list.append(function_return)
                
                else:
                    print("Watch out here! can be an outlier")
                    return_list.append(function_return)
        
        return return_list
    
    def get_call_arguments_origin(self, argument, call_instr, caller_parameters, caller_cfg_obj):
        origin_res = None

        if type(argument).__name__ == 'TemporaryVariable':
            s_lvar, s_rvar, type_str = self.process_temporary_variable(argument, caller_cfg_obj, caller_parameters)
            origin_res = s_lvar

        elif type(argument).__name__ == 'ReferenceVariable':
            origin_res = self.get_origin_variable_from_refvariable(call_instr, argument, caller_cfg_obj)
        
        elif type(argument).__name__ == 'StateVariableSolc':
            origin_res = argument
        
        elif type(argument).__name__ == 'LocalVariableSolc':
            #: Fix this, need to check what is such local variables
            origin_res = argument
        
        elif type(argument).__name__ == 'Constant':
            origin_res = argument.value
        
        elif type(argument).__name__ == 'int' or type(argument).__name__ == 'str':
            origin_res = argument
        
        else:
            print("Why I am here!")

        return origin_res

    def get_overapproximate_binary_op_res(self, vleft, vright, op_str):
        if isinstance(vleft, list):
            return vleft
        
        else:
            if type(vleft).__name__ == 'int' and type(vright).__name__ == 'int':
                return ['C']
 
    def collect_conditional_pre_dominators(self, basic_block, cfg_obj, graph, node, parameters = []):
        parents = cfg_obj._conditional_pre_dominators[basic_block]
        parents = list(set(parents))
        flag_condition = False

        for parent in parents:
            instruction = parent._instructions[-1]
            
            if type(instruction).__name__ == 'SolidityCall':
                if instruction.function.name.startswith('require') or instruction.function.name.startswith('assert'):
                    flag_condition = True
                    arguments = instruction.arguments
            
            if type(instruction).__name__ == 'Condition':
                flag_condition = True
                arguments = instruction.used
            
            if flag_condition:
                for argument in arguments:
                    if type(argument).__name__ == 'TemporaryVariable':
                        break
                
                self.process_temporary_variable(argument, cfg_obj, parameters, parent, node, graph)
                #range_node = RangeNode(s_var, parent, var_right, type_str)
                #graph.add_edge(range_node, node)
                flag_condition = False
        
    def process_local_variable(self, cfg_obj, variable, parameters, return_values):
        instrs = cfg_obj._vars_written[variable]
        s_lvar = None
        s_rvar = None
        type_str = None

        for instr in instrs:
            if type(instr).__name__ == 'Assignment':
                rvalue = instr.rvalue

                if type(rvalue).__name__ == 'TemporaryVariable':
                    s_lvar, s_rvar, type_str = self.process_temporary_variable(rvalue, cfg_obj, parameters, return_values)
                
                if type(rvalue).__name__ == 'LocalVariableSolc':
                    pass
            else:
                pass
            
            return s_lvar, s_rvar, type_str
    
    #: Need to think about place holders in modifier nodes
    def process_nonleaf_functions(self, cfg_obj):

        function = cfg_obj._function
        parameters = function.parameters
        return_values = function.return_values
        print("[*]  Processing function %s"  % cfg_obj._function.name)

        try:
            for ircall in cfg_obj._ircall_to_bb.keys():
                call_basic_block = cfg_obj._ircall_to_bb[ircall]
                call_cfg = CFG.function_cfg[ircall.function]
                
                if call_cfg in self.value_graph.keys():
                    
                    for svar_obj in self.value_graph[call_cfg].keys():
                        svar_triplets = self.value_graph[call_cfg][svar_obj]
                        
                        for svar_triplet in svar_triplets:
                            assignment_node = svar_triplet[0]
                            s_graph = svar_triplet[1]
                            s_graph_copy = s_graph.copy(as_view=False)
                            self.collect_conditional_pre_dominators(call_basic_block, cfg_obj, s_graph_copy, assignment_node, parameters)
                            
                            if cfg_obj not in self.value_graph.keys():
                                self.value_graph[cfg_obj] = {}
                            if svar_obj not in self.value_graph[cfg_obj].keys():
                                self.value_graph[cfg_obj][svar_obj] = []
                            
                            target_triplet = (assignment_node, s_graph_copy, svar_triplet[2])
                            self.value_graph[cfg_obj][svar_obj].append(target_triplet)
                
            self.process_statevar_assignment(cfg_obj, parameters, return_values)
            print("[*] Processed function %s"  % cfg_obj._function.name)
        
        except Exception as e:
            traceback.print_exc()
            print(str(e))

    # The idea of processing functions are the following:
    # 1. We should only keep state variable assignments in the range graph. Once we have
    #    seen a state variable assignment, we should add that as node in the range graph.
    #    We know the lvalue is a state variable and rvalue is something other than state variable
    #    we need to track the source of the rvalue
    # 2. Once we have a state variable assignment, we need to see the pre-conditions that is needed
    #    for state variable to be written, we add that as predecessor to the state var node
    # 3. For functions which has return values we track the source of the return values and store 
    #    as mapping    

    def process_statevar_assignment(self, cfg_obj, parameters, return_values):
        cfg_graph = cfg_obj._cfg

        for basic_block in cfg_graph.nodes:
            for instruction in basic_block._instructions:
                
                # If an instruction has lvalue, the type of the lvalue can be anything. But
                # we are only interested in lvalues being a reference variable or state variable
                # : Need to handle arbitrary types of instructions having lvalue
                if hasattr(instruction, 'lvalue'):
                    # If a lvalue is a reference variable we need to get the state variable
                    # for this reference variable
                    if type(instruction.lvalue).__name__ == 'ReferenceVariable':
                        variable = self.get_origin_variable_from_refvariable(instruction, instruction.lvalue, cfg_obj)

                    else:
                        variable = instruction.lvalue
                    
                    # The state variable is not a structure
                    if variable not in SDG.map_svars_to_struct.keys() and variable in SDG.map_svars_to_sobj.keys():
                        s_var = SDG.map_svars_to_sobj[variable]
                        
                        if cfg_obj not in self.value_graph.keys():
                            self.value_graph[cfg_obj] = {}
                        
                        if s_var not in self.value_graph[cfg_obj].keys():
                            self.value_graph[cfg_obj][s_var] = []
                        
                        # If the instruction is an assignment
                        if hasattr(instruction, 'rvalue'):
                            value = instruction.rvalue
                            
                            # If the rvalue belongs to function parameters
                            if value in parameters:
                                s_graph = nx.MultiDiGraph()
                                range_node = RangeNode(s_var, basic_block, value, "=")
                                s_graph.add_node(range_node)
                                self.collect_conditional_pre_dominators(basic_block, cfg_obj, s_graph, range_node, parameters)
                                svar_identifier_triplet = (range_node, s_graph, value)
                                self.value_graph[cfg_obj][s_var].append(svar_identifier_triplet)
                            
                            # Else : Need to handle for arbitrary type rvalues
                            else:
                                
                                if type(value).__name__ == "TemporaryVariable":
                                    s_lvar, s_rvar, type_str = self.process_temporary_variable(value, cfg_obj, parameters)
                                    s_graph = nx.MultiDiGraph()
                                    range_node = RangeNode(s_var, basic_block, s_lvar, "=")
                                    s_graph.add_node(range_node)
                                    self.collect_conditional_pre_dominators(basic_block, cfg_obj, s_graph, range_node, parameters)
                                    svar_identifier_triplet = (range_node, s_graph, value)
                                    self.value_graph[cfg_obj][s_var].append(svar_identifier_triplet)
                                    #self.print_cfg_dot(self.graph_dir, cfg_obj._function, s_graph)

                                else:
                                    s_graph = nx.MultiDiGraph()
                                    range_node = RangeNode(s_var, basic_block, value, "=")
                                    s_graph.add_node(range_node)
                                    self.collect_conditional_pre_dominators(basic_block, cfg_obj, s_graph, range_node, parameters)
                                    svar_identifier_triplet = (range_node, s_graph, value)
                                    self.value_graph[cfg_obj][s_var].append(svar_identifier_triplet)

                            self.print_cfg_dot(self.graph_dir, cfg_obj._function, s_graph)
                        else:
                            pass
                    else:
                        pass
                
                # If the function have return value, we should summarize the return
                else:
                    pass

    def get_origin_variable_from_refvariable(self, instruction, variable, cfg_obj):
        instrs = cfg_obj._vars_written[variable]
        for instr in instrs:
            if type(instr).__name__ == 'Index':
                if type(instr.variable_left).__name__ == 'StateVariableSolc':
                    self._ref_to_state[instr.lvalue] = instr.variable_left
                    return instr.variable_left
                
                elif type(instr.variable_left).__name__ == 'LocalVariableSolc':
                    self._ref_to_state[instr.lvalue] = instr.variable_left
                    return instr.variable_left
                
                else:
                    if instr.lvalue not in self._ref_to_state.keys():
                        self._ref_to_state[instr.lvalue] = self.get_origin_variable_from_refvariable(instr, instr.variable_left, cfg_obj)
                    
                    return self._ref_to_state[instr.lvalue]
            else:
                pass
    
    # This function processes functions one by one. Right now it just processes only
    # leaf functions, i.e function which does not have any calls to other functions
    def process_functions(self, cfg_obj):
        function = cfg_obj._function
        parameters = function.parameters
        return_values = function.return_values
        
        try:
            if function.name in self._summarized_libraries:
                self.process_statevar_assignment(cfg_obj, parameters, return_values)
            else:
                self.process_statevar_assignment(cfg_obj, parameters, return_values)   
            
        except Exception as e:
            traceback.print_exc()
            print(str(e))

    def generate_cfgs(self, contract, function):
        if function not in CFG.function_cfg.keys():
            cfg_obj = CFG(self.slither_obj, contract, function, self.graph_dir)
            CFG.function_cfg[function] = cfg_obj
        return CFG.function_cfg[function]
    
    def get_root_nodes(self, graph):
        root_nodes = [x for x in graph.nodes if graph.out_degree(x) >= 0 and graph.in_degree(x) == 0]
        return root_nodes
    
    def get_leaf_function_nodes(self, graph):
        leaf_nodes = [x for x in graph.nodes if graph.out_degree(x) == 0 and graph.in_degree(x) >= 0]
        return leaf_nodes

    def get_root_function_nodes(self, graph):
        root_nodes = [x for x in graph.nodes if graph.in_degree(x) == 0 and graph.out_degree(x) >= 0]
        return root_nodes
    
    def print_cfg_dot(self, graph_dir, function, graph, index=1):
        content = ''
        index_str = "_" + str(index)
        # Ref: https://stackoverflow.com/questions/33722809/nx-write-dot-generates-redundant-nodes-when-input-nodes-have-a-colon
        dot_file_name = function.name + "_range" + index_str + ".dot"
        dot_file_path = os.path.join(graph_dir, dot_file_name)
        with open(dot_file_path, 'w', encoding='utf8') as fp:
            nx.drawing.nx_pydot.write_dot(graph, fp)

        (graph, ) = pydot.graph_from_dot_file(dot_file_path)

        png_file_name = function.name + "_range" + index_str + ".png"
        png_file_path = os.path.join(graph_dir, png_file_name)
        graph.write_png(png_file_path)