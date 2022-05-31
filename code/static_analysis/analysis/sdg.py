import slither
import shutil
import os
import sys
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
from slither.slither import Slither
from instr_block import *
from icfg import *
from varnode import *
import copy
from util import *

'''
Functions can be declared view in which case they promise not to modify the state.
The following statements are considered modifying the state:
1. Writing to state variables. (We consider)
2. Emitting events. (We consider)
2. Creating other contracts.
3. Using selfdestruct.
4. Sending Ether via calls. (We consider)
5. Calling any function not marked view or pure.
6. Using low-level calls. (We consider)
7. Using inline assembly that contains certain opcodes.

'''

TEMPVAR_TYPES = ['LocalVariableSolc', 'TemporaryVariable']
class SDG:
    """
        Given an ICFG this class first builds a simplified icfg containting only Conditional, SSTORE, Lowlevel Call and High level 
        call instuction. High level call intructions are those where destination is tainted.

        Once we have the simplified icfg, we build a sdg out of it. SDG captures the data dependency of storage variables 
        on those instructions.

    """
    sdg_generated = {}
    contract_vars = {}
    map_svars_to_struct = {}
    map_svars_to_sobj = {}
    var_node_list = []
    inter_contract_analysis = {}

    def __init__(self, slither_obj, contract, function, icfg, graph_dir, dump_graph, log):
        self._slither = slither_obj
        self._ext_calls = {}
        self._is_ether_sending_functions = {}
        self._is_msg_sender = False
        self._sdg = None
        self._dump_graph = dump_graph
        self._log = log
        self._ir_to_irb = {}
        self._vars_written = {}
        self._root_nodes = []
        self._ref_to_state = {}
        self._leaf_nodes = []
        self._contract = contract
        self._function = function
        self._icfg = icfg
        self._sicfg = None
        self._newbb_to_old = {}
        self._instrb_to_basicb = {}
        self._result_dir = graph_dir
        self._is_ext_call = False
        self.inter_contract_calls = []
        self._collect_critical_variables = {}
        self.setup()
    
    @staticmethod
    def initialize_sdg(contract_vars, map_svars_to_struct, map_svars_to_sobj):
        SDG.contract_vars = contract_vars
        SDG.map_svars_to_struct = map_svars_to_struct
        SDG.map_svars_to_sobj = map_svars_to_sobj
    
    def get_root_nodes(self, graph):
        root_node = None
        nodes = [x for x in graph.nodes if graph.in_degree(x) == 0 and isinstance(x, InstrBlock)]
        return nodes
    
    def get_leaf_nodes(self, graph):
        leaf_nodes = [x for x in graph.nodes if graph.out_degree(x) == 0 and isinstance(x, InstrBlock)]
        return leaf_nodes

    def setup(self):
        # This generates a simplified icfg containting basic blocks which can change the state of the
        # contract, for now we just consider 1, 4, 6

        self._sicfg = self.build_simplified_icfg()

        # Get the root and the leaf nodes of the sicfg
        self._root_nodes = self.get_root_nodes(self._sicfg)
        self._leaf_nodes = self.get_leaf_nodes(self._sicfg)

        # Given the sicfg we build the storage dependency graph by adding the data flow edges
        # from the storage variables

        self._sdg = self.build_sdg(self._contract, self._function, self._sicfg)
        SDG.sdg_generated[self._function] = self._sdg

        if self._dump_graph == True:
            self.print_sdg_dot(self._result_dir, self._function, self._sdg, "_sdg")
            self.print_sdg_dot(self._result_dir, self._function, self._sicfg, "_sicfg")
    
    # This function checks whether the structure var and member var is 
    # already present in our var node list. If yes, return that
    def is_var_node_present(self, svar, field):
        vnode = None
        
        for var_node in SDG.var_node_list:
            if var_node._origin_var == svar and var_node._field == field:
                vnode = var_node
                break
        
        return vnode
    
    def get_used_vars(self, target_node):
        var_list = []                                                                                                                                                                                    
        for dominator in target_node.dominators:                                                                                                                                                          
	        for ir in dominator.irs:                                                                                                                                                                      
		        var_list.extend(ir.used)
        
        used_var = []
        for var in var_list:
	        if type(var).__name__ != 'Constant':
		        used_var.append(var)
        
        return used_var
    
    # Given a set of variables, this function finds out which
    # are of type state variable amoung them and returns those
    def find_dependent_statevars(self, dep_vars):
        state_var_dep_list = []
        for var in dep_vars:
            if type(var).__name__ == 'StateVariableSolc':
                state_var_dep_list.append(var)

        return state_var_dep_list        

    # This function computes the origin state variable 
    # corresponding to a reference variable. A reference variable
    # involving as a lvalue in an operation can help us finding the
    # original variable
    def get_origin_state_var(self, ref_var):
        try:
            # Extract all the instruction where the reference variable is involved 
            # as an lvalue
            lvalue = None
            instrs = CFG.lvalue_vars[ref_var]

            # For every such instruction we recursively see whether the instruction is of type 
            # Index or Member. For Index, it means it ir trying to access an element
            # from an state var array. We figure the state var
            # If Member, it means that it is trying to access a member for a state var structure
            # we get the member var.
            for instr in instrs:

                # If the instruction is of type Index, we extract the left variable, if the left
                # variable is a state variable itself, we output that and done
                # If the left variable is not a state variable, we recursively call get_origin_var
                if type(instr).__name__ == 'Index':
                    if type(instr.variable_left).__name__ == 'StateVariableSolc':
                        lvalue = instr.lvalue
                        s_var_obj = SDG.map_svars_to_sobj[instr.variable_left]
                        self._ref_to_state[lvalue] = s_var_obj

                    else:
                        lvalue = instr.lvalue
                        
                        if lvalue not in self._ref_to_state.keys():
                            origin_var = self.get_origin_state_var(instr.variable_left)
                            if origin_var == None:
                                return None
                            
                            else:
                                self._ref_to_state[lvalue] = origin_var

                # If the instruction is of type Member, we get the variable left and variable right. Variable right
                # is always the member of the structure, but left variable can a state variable itself or a reference
                # variable. In the first case, we output that. For the second case we recursive call get_origin_var unless
                # we find a origin variable of type state variable. After we get that, we put that in our var node structure
                # where store the structure var and the member var
                elif type(instr).__name__ == 'Member':
                    var_left = instr.variable_left
                    struct_member = instr.variable_right
                    lvalue = instr.lvalue

                    if instr.lvalue not in self._ref_to_state.keys():
                        if type(var_left).__name__ == 'StateVariableSolc':
                            origin_var = SDG.map_svars_to_sobj[instr.variable_left]
                        
                        elif type(var_left).__name__ == 'Enum':
                            origin_var = var_left
                        
                        elif type(var_left).__name__ == 'ContractSolc04':
                            origin_var = var_left 

                        elif type(var_left).__name__ == 'Contract':
                            self._log.warning("Contract type var left should be handled!")
                            sys.exit(1)

                        elif type(var_left).__name__ == 'SolidityVariable' or type(var_left).__name__ == 'SolidityVariableComposed':
                            origin_var = var_left
                        # : Storage reference
                        else:
                            origin_var = self.get_origin_state_var(var_left)
                            if origin_var == None:
                                return None
                        
                        varnode = self.is_var_node_present(origin_var, struct_member)
                        
                        if varnode == None:
                            varnode = VarNode(origin_var, instr.expression, struct_member)
                            SDG.var_node_list.append(varnode)
                        
                        self._ref_to_state[lvalue] =  varnode
            
            if lvalue == None:
                return None
            
            else:
                return self._ref_to_state[lvalue]
        
        except Exception as e:
            traceback.print_exc()
            sys.exit(1)
            #print(str(e))


    # This function computes what are the state variables amoung a set of 
    # variables
    def find_dependent_vars(self, contract, function, dep_vars):
        state_var_dep_list = []
        all_state_vars = []
        
        # If a variable is directly a state variable add that into the list
        state_var_dep_list.extend(self.find_dependent_statevars(dep_vars))
        ref_vars = {}

        # If a variable is a reference variable then we should compute the
        # origin state variable
        s_var_list = []
        for dep_var in dep_vars:
            if type(dep_var).__name__ == 'ReferenceVariable':
                
                if dep_var not in CFG.member_ir_var_left and type(dep_var.points_to_origin).__name__ != 'LocalVariableSolc':
                    origin_var = self.get_origin_state_var(dep_var)

                    if origin_var == None:
                        continue
                    else:
                        if origin_var not in s_var_list:
                            ref_vars[dep_var] = origin_var
                            s_var_list.append(origin_var)
        
        # For every reference variable, we see whether its points to origin 
        # is already added in the list of state variables, if yes then we should remove that
        # state variable from the state var dep list. This is because the reference variable
        # can point to structure member and slither does not support structure member, So even if the
        # the state variable is actually a.b, slither's point to origin will say it's a. But, our refernce variable 
        # analysis can figure out whether it's a structure member or not. So, we should keep the result found by our 
        # reference variable analysis
        for ref_var in ref_vars.keys():
            if ref_var.points_to_origin in state_var_dep_list:
                state_var_dep_list.remove(ref_var.points_to_origin)
            
            all_state_vars.append(ref_vars[ref_var])
        
        # Now, if there exist any non structure member state variable, we get its corresponding
        # state var object
        for state_var in state_var_dep_list:
            s_obj = SDG.map_svars_to_sobj[state_var]
            all_state_vars.append(s_obj)
        
        return all_state_vars
    
    # This function adds store edge from the instr block to the storage variable being written
    # If value to be written is dependent on a set of other storage variables, then add data 
    # flow edges from those variables to the variable being written. If the set of storage variables
    # contain the variable being written, then remove the variable being written from the set of
    # variables.
    def add_store_edge(self, contract, graph, instr_block, state_var_w):
        node = instr_block._instr_to_node
        s_var_list = []
        
        # If the value being written is a state variable, get the state var object
        if type(state_var_w).__name__ == 'StateVariableSolc':
            s_var_list.append(SDG.map_svars_to_sobj[state_var_w])
        
        # If the value being written is a reference variable
        # get the origin state variable from the reference variable
        else:
            s_var_list.append(self.get_origin_state_var(state_var_w))
        
        # For every storage variable being written add a store edge from 
        # the instr block to the storage variable
        for var_w in s_var_list:

            if type(var_w).__name__ == 'StateVariableSolc':
                var_w = SDG.map_svars_to_sobj[var_w]
            
            # Adds only edge if the storage variable already exists
            if graph.has_node(var_w):
                graph.add_edge(instr_block, var_w, key='W')
           
            # Adds both the storage variable node and edge from store to itself
            # if the variable does not exist already
            else:
                graph.add_node(var_w, key='state_var')
                graph.add_edge(instr_block, var_w, key='W')

        return s_var_list

    def do_context_based_dependency_analysis(self, variable, function, call_context):
        dep_vars = []
        
        if type(variable).__name__ in TEMPVAR_TYPES:
            
            #for function in call_context:
            dep_vars.extend(list(slither.analyses.data_dependency.data_dependency.get_dependencies(variable, function.contract)))
        else:
            dep_vars.extend(list(slither.analyses.data_dependency.data_dependency.get_dependencies(variable, function.contract)))

        dep_vars = list(set(dep_vars))

        return dep_vars


    def get_vars_used_untill(self, current_ir, instr_block):
        vars_used = []
        
        for ir in instr_block._pred_vars_used.keys():
            vars_used.extend(instr_block._pred_vars_used[ir])
            vars_used = list(set(vars_used))
        
        for ir in instr_block._state_vars_used.keys():
            if ir == current_ir:
                vars_used.extend(instr_block._state_vars_used[ir])
                break
            
            else:
                vars_used.extend(instr_block._state_vars_used[ir])
            
            vars_used = list(set(vars_used))
        
        return vars_used
    
    # This function adds the data flow edges from the dependent state variables to the instuction block.
    # I.e we compute the set of storage variables that influence the variables used in that instruction and
    # add a data flow edge for each one of them
    def add_data_flow_edge(self, contract, function, graph, instr_block, call_context, arguments, is_modifier, is_state='', variable_written=None):
        ir = instr_block._instruction
        node = instr_block._instr_to_node
        
        variables = []
        
        # If the variable is constant we should not consider it
        for argument in arguments:
            if type(argument).__name__ == 'Constant':
                pass

            elif isinstance(argument, list):
                for element in argument:
                    if type(element).__name__ == 'Constant':
                        pass
                    
                    else:
                        variables.append(element)
            
            else:
                variables.append(argument)                       
        try:
            if len(variables) > 0:
                dep_vars = []
                dep_vars.extend(variables)

                # For each of the variable involved in the instruction compute the set of 
                # variables that influence the the value of the variable in question
                for variable in variables:
                    dep_vars.extend(self.do_context_based_dependency_analysis(variable, function, call_context))
                
                dep_vars = set(dep_vars)                            
                context_dep_vars = dep_vars

                if is_modifier is True:
                    for dep_var in dep_vars:
                        if str(dep_var) == 'msg.sender':
                            self._is_msg_sender = True

                
                # From the set of variable we compute the state variables among them
                common_vars = self.find_dependent_vars(contract, function, list(context_dep_vars))

                if is_state == 'S':
                    common_vars = set(common_vars).difference(set(variable_written))
                    common_vars = list(common_vars)               
                
                vars_used_upto = self.get_vars_used_untill(ir, instr_block)

                for s_var in common_vars:

                    if type(s_var).__name__ == 'StateVariableSolc':
                        s_var = SDG.map_svars_to_sobj[s_var]
                    
                    if s_var not in vars_used_upto:
                        continue
                    
                    # Adds only edge, if the variable already exists
                    if graph.has_node(s_var):
                        graph.add_edge(s_var, instr_block, key='D')

                    # Adds both the storage variable node and edge from store to itself
                    # if the variable does not exist already
                    else:
                        graph.add_node(s_var, key='state_var')
                        graph.add_edge(s_var, instr_block, key='D')
        
        except Exception as e:
            traceback.print_exc()
            sys.exit(1)
            #print(str(e))


    # This function generates storage dependency graph i.e adding
    # dataflow edges to those important IR instructions
    def build_sdg(self, contract, function, sicfg):
        graph = sicfg.copy(as_view=False)
        is_modifier = False

        for instr_block in sicfg.nodes:
            node = instr_block._instr_to_node

            ir_instr = instr_block._instruction
            call_context = instr_block._call_context
            state_var_w = []
            

            # Extract the variables that are involved in a conditional statement
            # add data flow edges for each one of them if exist
            if type(ir_instr).__name__ == 'Condition':
                arguments = []

                arguments = self.get_conditional_dependencies(instr_block, sicfg, ir_instr.used[0], [], [])

                #else:
                #    for ir in node.irs:
                #        arguments.extend(ir.used)

                if type(function).__name__ == "ModifierSolc":
                    is_modifier = True

                self.add_data_flow_edge(node.function.contract, node.function, graph, instr_block, call_context, arguments, is_modifier, 'N')

            if type(ir_instr).__name__ == 'NewContract':
                arguments = ir_instr.arguments
                for arg in arguments:
                    if hasattr(arg, 'type') and type(arg.type).__name__ == 'ElementaryType':
                        if arg.type.type.startswith('address') or arg.type.type.startswith('bytes'):
                            if is_tainted_destination(arg, node, True):
                                self._is_ext_call = True
                                self._ext_calls[ir_instr] = True
                                self._ir_to_irb[ir_instr] = instr_block

                arguments = ir_instr.arguments
                self.add_data_flow_edge(node.function.contract, node.function, graph, instr_block, call_context, arguments, is_modifier)

            # Extract the arguments that are involved in a conditional statement
            # add data flow edges for each one of them if exist            
            if type(ir_instr).__name__ == 'SolidityCall':
                
                if ir_instr.function.name.startswith('require') or ir_instr.function.name.startswith('assert'):
                    if type(function).__name__ == "ModifierSolc":
                        is_modifier = True

                arguments = []

                #for ir in node.irs:
                    #arguments.extend(ir.used)

                arguments = self.get_conditional_dependencies(instr_block, sicfg, ir_instr.used[0], [], [])
                self.add_data_flow_edge(node.function.contract, node.function, graph, instr_block, call_context, arguments, is_modifier)

            # If the lvalue written is a state variable, add store edge for that variable
            if type(ir_instr).__name__ == "Binary" or type(ir_instr).__name__ == 'Assignment' or type(ir_instr).__name__ == 'Unary':
                lvalue = ir_instr.lvalue
                variable_written = None
                
                if type(lvalue).__name__ == 'ReferenceVariable' or  type(lvalue).__name__ == 'StateVariableSolc':
                    variable_written = self.add_store_edge(contract, graph, instr_block, lvalue)
                
                if hasattr(ir_instr, 'rvalue'):
                    arguments = [ir_instr.rvalue]
                
                else:
                    arguments = [ir_instr.variable_left, ir_instr.variable_right]

                if variable_written is not None:
                    self.add_data_flow_edge(node.function.contract, node.function, graph, instr_block, call_context, arguments, is_modifier, 'S', variable_written)
                else:
                    self.add_data_flow_edge(node.function.contract, node.function, graph, instr_block, call_context, arguments, is_modifier)

            if type(ir_instr).__name__ == 'Delete':
                lvalue = ir_instr.lvalue

                if type(lvalue).__name__ == 'ReferenceVariable' or type(lvalue).__name__ == 'StateVariableSolc':
                    variable_written = self.add_store_edge(contract, graph, instr_block, lvalue)

            if type(ir_instr).__name__ == 'Push':
                lvalue = ir_instr.lvalue
                variable_written = None
                if type(lvalue).__name__ == 'ReferenceVariable' or type(lvalue).__name__ == 'StateVariableSolc':
                    variable_written = self.add_store_edge(contract, graph, instr_block, lvalue)

                arguments = [ir_instr.value]
                if variable_written is not None:
                    self.add_data_flow_edge(node.function.contract, node.function, graph, instr_block, call_context, arguments, is_modifier, 'S', variable_written)
                else:
                    self.add_data_flow_edge(node.function.contract, node.function, graph, instr_block, call_context, arguments, is_modifier)

            # Add data flow edges for the arguments of low level call
            if type(ir_instr).__name__ == "LowLevelCall":
                is_tainted = is_tainted_destination(ir_instr.destination, node, True)

                call_value = ir_instr.call_value

                if call_value is not None:
                    if type(call_value).__name__ == 'Constant':
                        if call_value.value > 0:
                            self._is_ether_sending_functions[ir_instr] = True
                    else:
                        self._is_ether_sending_functions[ir_instr] = True

                call_gas = ir_instr.call_gas

                if is_tainted:# and self.analyze_call_gas(ir_instr, function):
                    self._is_ext_call = True
                    self._ext_calls[ir_instr] = True
                else:
                    values = []
                    visited_instrs = []

                    try:
                        get_source_variable(self._log, CFG, function, ir_instr, ir_instr.destination, values, visited_instrs)
                        for value in values:
                            if value != 'U':
                                if (value, ir_instr) not in self.inter_contract_calls:
                                    self.inter_contract_calls.append((value, ir_instr))
                    except:
                        self._log.warning("Issues with getting the high level call destination address")

                    arguments = ir_instr.arguments
                    for arg in arguments:
                        if hasattr(arg, 'type') and type(arg.type).__name__ == 'ElementaryType':
                            if arg.type.type.startswith('address') or arg.type.type.startswith('bytes'):
                                if is_tainted_destination(arg, node, True):
                                    self._is_ext_call = True
                                    self._ext_calls[ir_instr] = True

                arguments = []
                arguments.append(ir_instr.call_value)
                arguments.append(ir_instr.destination)
                self.add_data_flow_edge(node.function.contract, node.function, graph, instr_block, call_context, arguments, is_modifier)
            
            # Add data flow edges for the arguments of Transfer call
            if type(ir_instr).__name__ == 'Transfer':
                arguments = []

                call_value = ir_instr.call_value

                if call_value is not None:
                    if type(call_value).__name__ == 'Constant':
                        if call_value.value > 0:
                            self._is_ether_sending_functions[ir_instr] = True
                    else:
                        self._is_ether_sending_functions[ir_instr] = True

                arguments.append(ir_instr.call_value)
                arguments.append(ir_instr.destination)
                self.add_data_flow_edge(node.function.contract, node.function, graph, instr_block, call_context, arguments, is_modifier)
            
            # Add data flow edges for the arguments of Send
            if type(ir_instr).__name__ == 'Send':
                arguments = []
                call_value = ir_instr.call_value

                if call_value is not None:
                    if type(call_value).__name__ == 'Constant':
                        if call_value.value > 0:
                            self._is_ether_sending_functions[ir_instr] = True
                    else:
                        self._is_ether_sending_functions[ir_instr] = True

                arguments.append(ir_instr.call_value)
                arguments.append(ir_instr.destination)
                self.add_data_flow_edge(node.function.contract, node.function, graph, instr_block, call_context, arguments, is_modifier)

            # Add data flow edges for the arguments of Highlevel call
            if type(ir_instr).__name__ == "HighLevelCall":
                is_tainted = is_tainted_destination(ir_instr.destination, node, True)

                if is_tainted:
                    self._is_ext_call = True
                    self._ext_calls[ir_instr] = True

                else:
                    values = []
                    visited_instrs = []
                    try:
                        get_source_variable(self._log, CFG, node.function, ir_instr, ir_instr.destination, values, visited_instrs)
                        for value in values:
                            if value != 'U':
                                if (value, ir_instr) not in self.inter_contract_calls:
                                    self.inter_contract_calls.append((value, ir_instr))
                    except:
                        self._log.warning("Issues with getting the high level call destination address")

                arguments = []
                arguments.extend(ir_instr.arguments)
                arguments.append(ir_instr.destination)
                arguments.append(ir_instr.call_value)
                self.add_data_flow_edge(node.function.contract, node.function, graph, instr_block, call_context, arguments, is_modifier)

        return graph

    #  implement this
    def do_inter_contract_analysis(self, contract_address, destination_function):
        imported_package = get_imported_module("main_helper")
        contract_path = "/home/cinderella/research/creame_finance_incident/modified_cream.sol"
        contract_name = os.path.basename(contract_path)

        if SDG.inter_contract_analysis.get(contract_name) is None:
            SDG.inter_contract_analysis[contract_name] = True
        else:
            return

        _, solc_path = get_solc_path(contract_path, self._log)

        # Initialize Slither
        slither_obj = Slither(contract_path, solc=solc_path)

        # Build interprocedural cfg for all public functions
        self._log.info('Interprocedural CFG generation started!')
        generated_icfg, icfg_objects = imported_package.generate_icfg(slither_obj, None, self._result_dir, self._dump_graph, self._log)
        self._log.info('Interprocedural CFG generation finished!')

        # Build storage dependency graph
        self._log.info('Storage dependency graph generation started!')
        generated_sdg, sdg_objects, owner_only_modifiers = imported_package.generate_sdg(slither_obj, generated_icfg, self._result_dir, self._dump_graph, self._log)
        self._log.info('Storage dependency graph generation finished!')
        is_ext_tainted = self.check_for_tainted_call(sdg_objects, generated_sdg, owner_only_modifiers, destination_function)
        return is_ext_tainted

    def check_for_tainted_call(self, sdg_objects, generated_sdg, owner_only_modifiers, destination_function):
        for function in sdg_objects.keys():
            if destination_function.name == function.name and sdg_objects[function]._is_ext_call is True:
                return True

        return False

    # So far the below types of instructions matter for us for basic block simplification
    # : needs to check whether this is exhaustive
    def is_important_ir(self, ir_instr):
        if type(ir_instr).__name__ == 'Condition':
            return True

        elif type(ir_instr).__name__ == 'NewContract':
            return True

        elif type(ir_instr).__name__ == 'SolidityCall':
            #if ir_instr.function.name.startswith('require') or ir_instr.function.name.startswith('assert') or ir_instr.function.name.startswith('revert'):
            return True
            
            #else:
                #return False
        
        elif is_ir_call(ir_instr):
            return True
        
        elif type(ir_instr).__name__ == 'Binary' or type(ir_instr).__name__ == 'Assignment' or type(ir_instr).__name__ == 'Unary' or type(ir_instr).__name__ == 'Delete':
            lvalue = ir_instr.lvalue
            
            if type(lvalue).__name__ == 'ReferenceVariable':
                lvalue = lvalue.points_to_origin
            
            if type(lvalue).__name__ == 'StateVariableSolc':
                return True
            
            else:
                return False

        elif type(ir_instr).__name__ == 'Push':
            lvalue = ir_instr.lvalue

            if type(lvalue).__name__ == 'ReferenceVariable':
                lvalue = lvalue.points_to_origin

            if type(lvalue).__name__ == 'StateVariableSolc':
                return True

            else:
                return False

        else:
            return False


    def get_conditional_dependencies(self, instr_block, sicfg, target, dependent_vars, visited_instrs):
        if type(target).__name__ == 'Constant':
            dependent_vars = list(set(dependent_vars))
            return dependent_vars

        elif type(target).__name__ == 'SolidityVariableComposed':
            dependent_vars = list(set(dependent_vars))
            dependent_vars.append(target)

        elif type(target).__name__ == 'LocalVariableSolc' or type(target).__name__ == 'TemporaryVariable'\
                or type(target).__name__ == 'LocalVariableInitFromTupleSolc' or type(target).__name__ == 'TupleVariable':

            if CFG.lvalue_vars.get(target) is not None:
                lvalue_instrs = CFG.lvalue_vars[target]

                vars_read = []
                for instruction in lvalue_instrs:
                    if instruction in visited_instrs:
                        continue
                    visited_instrs.append(instruction)

                    if not is_ext_call(instruction):

                        if type(instruction).__name__ == 'InternalCall':
                            vars_read.append(instruction.lvalue)
                            return vars_read

                        else:
                            for variable in instruction.read:
                                if variable != target and variable not in vars_read:
                                    vars_read.append(variable)

                for var_read in vars_read:
                    dependent_vars.extend(self.get_conditional_dependencies(instr_block, sicfg, var_read, dependent_vars, visited_instrs))
            else:
                dependent_vars.append(target)

        else:

            if CFG.lvalue_vars.get(target) is not None:
                lvalue_instrs = CFG.lvalue_vars[target]

                for instruction in lvalue_instrs:
                    if not is_ext_call(instruction):
                        dependent_vars.append(target)
            else:
                dependent_vars.append(target)

        dependent_vars = list(set(dependent_vars))

        return dependent_vars

    def simplify_basic_block(self, basic_block):
        instr_block_list = []
        pred_var_used = copy.copy(basic_block._pred_state_var_used)

        if self.is_root_basic_block(basic_block):
            ir_instr = basic_block._instructions[0]
            instr_block = InstrBlock(ir_instr)
            instr_block._instr_to_node = basic_block._ir_to_node_map[ir_instr]
            instr_block._origin_bb = basic_block
            instr_block._call_context = basic_block._call_context
            instr_block_list.append(instr_block)
            instr_block._pred_vars_used = copy.copy(pred_var_used)

            if ir_instr in basic_block._state_vars_used.keys():
                instr_block._state_vars_used[ir_instr] = basic_block._state_vars_used[ir_instr]

        else:
            for ir_instr in basic_block._instructions:
                # If the ir involves important instructions then we create a separate instr block
                # for it.
                if self.is_important_ir(ir_instr):
                    self.collect_critical_variables(ir_instr)
                    basic_block._is_critical = True
                    instr_block = InstrBlock(ir_instr)
                    instr_block._instr_to_node = basic_block._ir_to_node_map[ir_instr]
                    instr_block._origin_bb = basic_block
                    instr_block._call_context = basic_block._call_context
                    instr_block_list.append(instr_block)

                    instr_block._pred_vars_used = copy.copy(pred_var_used)
                    if ir_instr in basic_block._state_vars_used.keys():
                        instr_block._state_vars_used[ir_instr] = basic_block._state_vars_used[ir_instr]

                if ir_instr in basic_block._state_vars_used.keys():
                    pred_var_used[ir_instr] = basic_block._state_vars_used[ir_instr]

        return instr_block_list 

    def is_root_basic_block(self, basic_block):
       if self._icfg.in_degree(basic_block) == 0:
           return True

    def collect_critical_variables(self, ir_instr):
        dep_vars = []
        for var in ir_instr.used:
            if type(var).__name__ == 'Constant':
                continue
            try:
                dep_vars.extend(list(slither.analyses.data_dependency.data_dependency.get_dependencies(var, self._function)))
            except:
                pass
        for var in dep_vars:
            try:
                self._collect_critical_variables[var] = True
            except:
                #this is intentional pass
                pass

        #self._collect_critical_variables = list(set(self._collect_critical_variables))

    def add_src_to_dest_edges(self, graph, src_nodes, dest_nodes):
        for src_node in src_nodes:
            for dest_node in dest_nodes:
                graph.add_edge(src_node, dest_node)

    def get_state_vars_used(self, basic_block):
        state_vars = {}
        
        for instr in basic_block._instructions:
            if type(instr).__name__ != 'NodeSolc':
                vars_used = instr.used
                for var_used in vars_used:
                    
                    if type(var_used).__name__ == 'StateVariableSolc':
                        var_used = SDG.map_svars_to_sobj[var_used]
                        if instr not in state_vars.keys():
                            state_vars[instr] = []
                        
                        state_vars[instr].append(var_used)

                    if type(var_used).__name__ == 'ReferenceVariable':
                        if var_used not in CFG.member_ir_var_left and type(var_used.points_to_origin).__name__ != 'LocalVariableSolc':
                            origin_var = self.get_origin_state_var(var_used)

                            if origin_var == None:
                                continue
                            else:
                                if instr not in state_vars.keys():
                                    state_vars[instr] = []
                                
                                state_vars[instr].append(origin_var)

        return state_vars

    def propagate_state_vars_used(self):
        sicfg = self._icfg
        root_nodes = []
        
        for x in sicfg.nodes:
            if sicfg.in_degree(x) == 0:
                root_nodes.append(x)
            x._state_vars_used = {}
            x._pred_state_var_used = {}

        processed_blocks = []
        bfs_queue = []
        bfs_queue.extend(root_nodes)
        processed_blocks.extend(root_nodes)
        
        for basic_block in bfs_queue:            
            state_vars = self.get_state_vars_used(basic_block)
            basic_block._state_vars_used = state_vars
            basic_block._pred_state_var_used = {}
        
        while len(bfs_queue) != 0:
            basic_block = bfs_queue.pop(0)
            
            successors = list(sicfg.successors(basic_block)) #get_successors_copy(sicfg, basic_block)
            
            for successor in successors:                
                if successor not in processed_blocks:
                    successor._state_vars_used = self.get_state_vars_used(successor)
                    processed_blocks.append(successor)
                    bfs_queue.append(successor)
                
                before_length = len(successor._pred_state_var_used)
                successor._pred_state_var_used.update(basic_block._pred_state_var_used)
                successor._pred_state_var_used.update(basic_block._state_vars_used)
                after_length = len(successor._pred_state_var_used)
                
                if before_length < after_length and successor not in bfs_queue:
                    bfs_queue.append(successor)

    def build_simplified_icfg(self):
        self.propagate_state_vars_used()
        sicfg = self._icfg.copy(as_view=False)


        # For every basic block in icfg simplify the basic block and removes instructions which
        # which are not required for the creation of inconsistant state
        for basic_block in self._icfg.nodes:
            predecessors = list(sicfg.predecessors(basic_block))
            predecessors = list(set(predecessors) - {basic_block})

            successors = list(sicfg.successors(basic_block))
            successors = list(set(successors) - {basic_block})

            sicfg.remove_node(basic_block)
            instr_block_list = self.simplify_basic_block(basic_block)

            # If the instr block list is empty and it has two predecessors 
            # then assume it is a phi node and create a separate instr block for that
            if len(predecessors) > 1 and len(instr_block_list) == 0:
                instr_block = InstrBlock("Phi Node")
                instr_block._instr_to_node = basic_block
                instr_block_list.append(instr_block)
            
            # If the instr block list not empty, then add edges in between then
            # also, add edges from predecessors to instr block and instr block to
            # successors
            if len(instr_block_list) != 0:
                prev_block = instr_block_list[0]
                
                for instr_block in instr_block_list:
                    self._newbb_to_old[instr_block] = basic_block
                    
                    if prev_block != instr_block:
                        self.add_src_to_dest_edges(sicfg, [prev_block], [instr_block])
                        prev_block = instr_block
                
                self.add_src_to_dest_edges(sicfg, predecessors, [instr_block_list[0]])
                self.add_src_to_dest_edges(sicfg, [instr_block_list[-1]], successors)

                # There can be cases where this is the only single node, it has no predecessors or
                # successors. In those cases, we need to make sure that it is added in the graph.
                if not sicfg.has_node(instr_block_list[0]):
                    sicfg.add_node(instr_block_list[0])
            
            # Else add edges between predecessors and successors
            else:
                self.add_src_to_dest_edges(sicfg, predecessors, successors)
        
        return sicfg

    def get_root_basic_block(self, graph):
        root_node = None
        nodes = [x for x in graph.nodes if graph.in_degree(x) == 0]
        for node in nodes:
            instr_type = node._instructions[0]
            if instr_type.type == 0x0:
                root_node = node
        return root_node

    def print_sdg_dot(self, graph_dir, function, graph, name=None):
        content = ''
        styles = ['dashed']

        # Ref: https://stackoverflow.com/questions/33722809/nx-write-dot-generates-redundant-nodes-when-input-nodes-have-a-colon
        dot_file_name = function.name + name + ".dot"
        dot_file_path = os.path.join(graph_dir, dot_file_name)
        
        with open(dot_file_path, 'w', encoding='utf8') as fp:
            nx.drawing.nx_pydot.write_dot(graph, fp)

        (dot_graph, ) = pydot.graph_from_dot_file(dot_file_path)

        # Ref: https://github.com/pydot/pydot/issues/169
        for i, node in enumerate(dot_graph.get_nodes()):
            node.set_shape('box')
        
        for i, edge in enumerate(dot_graph.get_edges()):
            key = edge.get('key')
            
            if key == 'D' or key == 'W':
                edge.set_style(styles[0])
            edge.set_label(edge.get('key'))

        png_file_name = function.name + name + ".png"
        png_file_path = os.path.join(graph_dir, png_file_name)
        dot_graph.write_png(png_file_path)