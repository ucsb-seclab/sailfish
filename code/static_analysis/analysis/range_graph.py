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
from slither.core.declarations.solidity_variables import SolidityFunction
from slither.core.solidity_types.elementary_type import ElementaryType
from slither.core.declarations.function import Function
from slither.core.variables.variable import Variable
from slither.printers.call.call_graph import *
from slither.core.cfg.node import NodeType
from slither.slithir.variables.constant import Constant
from cfg import *
from basic_block import *
from instr_block import *
from icfg import *
import copy
from sdg import *
from util import *
from value_node import *
from range_node import *
from state_var import *
from process_ir import *
from index_node import *
from return_summary import *
import traceback

# Improvements: Probably we may need to field sensitive
CONSTANT_TYPES = ['int', 'str', 'Constant']
VARIBLE_TYPES = ['StateVariableSolc', 'LocalVariableSolc']
SOLIDITY_VARS = ['SolidityVariableComposed', 'SolidityVariable']
int_type = ElementaryType('int')

'''
    This class generates the conditional value range graph for every state variable assignment
'''
class VRG:
    varnode_list = []
    index_dictionaries = {}
    contract_vars = {}
    map_svars_to_struct = {}
    map_svars_to_sobj = {}

    def __init__(self, slither_obj, callgraph, sdg_objects, derived_contracts, graph_dir, dump_graph, log):
        self._loop_count = {}
        self._derived_contracts = {}
        self._dump_graph = dump_graph
        self._state_var_written = {}
        self.local_visit_stack = []
        self._lvalue_equals = {} 
        self._active_instr = {}
        self.slither_obj = slither_obj
        self.sdg_objects = sdg_objects
        self.contant_state_vars = {}
        self.graph_dir = graph_dir
        self.callgraph = callgraph
        self._ref_to_state = {}
        self._reference_variables = {}
        self._var_op_list = {}
        self._constant_state_vars = {}
        self._condition_to_bb = defaultdict(dict)
        self._condition_to_node = defaultdict(dict)
        self._predecessors = {}
        self.log = log
        self.value_graph = {}
        self.setup()

    # This function prints the VRG graph for every state variable assignment
    def print_VRG(self):
        index = 1
        for cfg_obj in self.value_graph.keys():

            # : This ran result in regressions so watch out
            if cfg_obj._function.visibility not in ['public', 'external']:
                continue

            for svar_obj in self.value_graph[cfg_obj].keys():
                triplets = self.value_graph[cfg_obj][svar_obj]
                if svar_obj not in self._state_var_written.keys():
                    self._state_var_written[svar_obj] = []

                if cfg_obj._function not in self._state_var_written[svar_obj]:
                    self._state_var_written[svar_obj].append(cfg_obj._function)

                if self._dump_graph is True:
                #if cfg_obj._function.name == 'initializeDistribution':
                    for triplet in triplets: # The triplet is a combination of (state var, graph , value)
                        self.print_range_graph(self.graph_dir, cfg_obj._function, triplet[1], index)
                        index += 1

    def print_partial_VRG(self, cfg_obj, value_graph):
        index = 1
        
        for svar_obj in value_graph.keys():
            triplets = value_graph[svar_obj]
            
            for triplet in triplets:
                #self.print_range_graph(self.graph_dir, cfg_obj._function, triplet[1], index)
                index += 1        
    
    # This function first generates the graph for any constant state var assignment in the constructor.
    # Generally slither generates two such functions 'slitherConstructorConstantVariables' and 'slitherConstructorVariables'
    # that handles that handles the constant assignment in the constructor
    def initialize_constant_vars(self):
        for contract in self.slither_obj.contracts:
            for enum in contract.enums:
                enum_values = enum.values
                for value in enum_values:
                    varnode = create_var_node(self.log, None, enum, value)
                    const = Constant(str(enum_values.index(value)), int_type)
                    self._constant_state_vars[varnode] = const
        
        slither_special_functions = self.callgraph._slither_special_functions
        if slither_special_functions.get('slitherConstructorConstantVariables') is not None:
            constant_functions = slither_special_functions['slitherConstructorConstantVariables']

            for constant_function in constant_functions:
                cfg_obj = self.generate_cfgs(constant_function.contract, constant_function)
                self.process_leaf_functions(cfg_obj)

    # This first finds the leaf node of the callgraph and generate 
    # returns summaries and state variable assignment graph for them if exist
    # After that it gradually generate range graph for precessessor nodes of the leaves
    # in BFS order
    def setup(self):
        self.initialize_constant_vars()
        self.populate_predecessors(self.callgraph._callgraph)
        leaf_nodes = self.get_leaf_function_nodes(self.callgraph._callgraph)

        for leaf_node in leaf_nodes:
            contract = leaf_node._contract
            function = leaf_node._function
            
            '''
            if function not in self._predecessors.keys():
                self._predecessors[function] = []
            
            predecessors = list(self.callgraph._callgraph.predecessors(leaf_node))
            
            for predecessor in predecessors:
                self._predecessors[function].append(predecessor._function)
            '''
            
            # We won't generate the range graph again for this slither special functions, since we have already generated one
            if function.name in self.callgraph._slither_special_functions.keys():
                continue
            
            if type(function).__name__ == 'StateVariableSolc':
                continue
            cfg_obj = self.generate_cfgs(contract, function)
            
            self.process_leaf_functions(cfg_obj)
        
        self.process_bottom_up(leaf_nodes, self.callgraph._callgraph)

        #if self._dump_graph == True:
        self.print_VRG()
        #for function in CFG.function_cfg.keys():
            #self.check_return_summary(CFG.function_cfg[function])

    def populate_predecessors(self, graph):
        for node in graph.nodes:
            contract = node._contract
            function = node._function
            self._predecessors[node._function] = self.get_predecessors(node, graph)



    # We already have generated the range graph for leaf functions, now we will gradually generate
    # range graph and return summary for their predecessors
    # This is a standard BFS travelsal implementation
    def process_bottom_up(self, leaf_nodes, graph):
        processed_nodes = []
        processed_nodes.extend(leaf_nodes)
        processed_stack = []
        processed_stack.extend(leaf_nodes)
        
        while len(processed_stack) != 0:
            node = processed_stack.pop(0)
            #self._predecessors[node._function] = self.get_predecessors(node, graph)
            
            if node not in processed_nodes:
                contract = node._contract
                function = node._function
                cfg_obj = self.generate_cfgs(contract, function)
                self.process_nonleaf_functions(cfg_obj)
                processed_nodes.append(node)
  
            
            predecessors = list(graph.predecessors(node))
            for predecessor in predecessors:
                 
                # Alert! We need to convert to list first and the assign, otherwise if we directly do list(successors) after assignment
                # next list(successors) return empty list
                successors = list(graph.successors(predecessor))
                left = list(set(successors) - set(processed_nodes))
                
                if len(left) == 0:
                    processed_stack.append(predecessor)

    def get_predecessors(self, node, graph):
        functions = []
        predecessors = list(graph.predecessors(node))
        for pred in predecessors:
            functions.append(pred._function)
        return functions
    
    # This is for debug purpose
    # For every function, this prints it's return summary if exists
    def check_return_summary(self, cfg_obj):
        if len(cfg_obj._return_summary) != 0:
            print("=======================================================================")
            self.log.info("Analysing return summary for function %s" %cfg_obj._function.name)
            print(cfg_obj._return_summary)
            print("=======================================================================")

    def return_summary_handler(self, cfg_obj):
        parameters = cfg_obj._function.parameters
        return_values = get_return_values(self.log, self, cfg_obj)
        self.log.info("Generating return summary for %s"  % cfg_obj._function.name)
        generate_return_summary(self.log, self, cfg_obj, parameters, return_values)
        self.log.info("Return summary generated for %s"  % cfg_obj._function.name)
        
    # This function generates range graph and return summary for 
    # leaf functions, i.e function which does not have any calls to other functions
    def process_leaf_functions(self, cfg_obj):
        function = cfg_obj._function
        parameters = function.parameters
        returns_a = set(function.returns)
        returns_b = set(function.return_values)
        return_values = get_return_values(self.log, self, cfg_obj)

        if len(cfg_obj._return_summary) == 0:
            self.log.info("Generating return summary for %s"  % cfg_obj._function.name)
            generate_return_summary(self.log, self, cfg_obj, parameters, return_values)
            self.log.info("Return summary generated for %s"  % cfg_obj._function.name)

        self.generate_range_graph(cfg_obj, parameters, return_values)

        
    # : Need to think about place holders in modifier nodes
    # This function generates range graph and return summary for non-leaf functions
    def process_nonleaf_functions(self, cfg_obj):
        function = cfg_obj._function
        parameters = function.parameters

        returns_a = set(function.returns)
        returns_b = set(function.return_values)
        return_values =  get_return_values(self.log, self, cfg_obj)

        if len(cfg_obj._return_summary) == 0:
            self.log.info("Generating return summary for %s"  % cfg_obj._function.name)
            generate_return_summary(self.log, self, cfg_obj, parameters, return_values)
            self.log.info("Return summary generated for %s"  % cfg_obj._function.name)


        self.generate_range_graph(cfg_obj, parameters, return_values)
        


    # This function records teh constant variables declared in a constructor.
    # Since Slither has special function to handle those constants in a constructor,
    # We only records variables only the containting function is one of those special functions
    def record_constructor_constant_vars(self, cfg_obj, lvalue, rvalue):
        if cfg_obj._function.name in self.callgraph._slither_special_functions.keys():
            
            if type(rvalue).__name__ == 'Constant':
                self._constant_state_vars[lvalue] = rvalue
            
            elif type(rvalue).__name__ == 'int':
                 self._constant_state_vars[lvalue] = rvalue
            
            elif type(rvalue).__name__ in SOLIDITY_VARS:
                self._constant_state_vars[lvalue] = rvalue
            
            else:
                if DEBUG:
                    self.log.warning("Any other types of constant!")
                else:
                    pass
    # This function generates range graph for functions in a bottom-up fashion
    # If the function calls some other function which already has some range graph,
    # then the caller function merge that graph within itself.       
    def generate_range_graph(self, cfg_obj, parameters, return_values):
        for ircall in cfg_obj._ircall_to_bb.keys():
            call_basic_block = cfg_obj._ircall_to_bb[ircall]
            if type(ircall.function).__name__ == 'StateVariableSolc':
                continue
            call_cfg = CFG.function_cfg[ircall.function]
            
            # Check if callee has a range graph already, if yes merge that graph 
            # with the caller's own graph, since this is how interprocedural range graph generation
            # should work
            if call_cfg in self.value_graph.keys():
                
                for svar_obj in self.value_graph[call_cfg].keys():
                    svar_triplets = self.value_graph[call_cfg][svar_obj]
                    
                    for svar_triplet in svar_triplets:
                        assignment_node = svar_triplet[0]
                        s_graph = svar_triplet[1]
                        s_graph_copy = s_graph.copy(as_view=False)
                        # Once the caller have already merged the range graph, now it should
                        # include the pre-conditions the graph.
                        self.collect_conditional_pre_dominators(call_basic_block, cfg_obj, s_graph_copy, assignment_node, parameters)
                        
                        if cfg_obj not in self.value_graph.keys():
                            self.value_graph[cfg_obj] = {}
                        if svar_obj not in self.value_graph[cfg_obj].keys():
                            self.value_graph[cfg_obj][svar_obj] = []
                        
                        target_triplet = (assignment_node, s_graph_copy, svar_triplet[2])
                        self.value_graph[cfg_obj][svar_obj].append(target_triplet)
        
        # Now the caller should proceed to find it's own state variable assignment
        self.process_statevar_assignment(cfg_obj, parameters, return_values)
        
        if cfg_obj in self.value_graph.keys():
            self.print_partial_VRG(cfg_obj, self.value_graph[cfg_obj])
            self.log.info("Range graph generated")
        
        else:
            self.log.info("State variable assignement do not exist")
        
        self.log.info("Processed function %s"  % cfg_obj._function.name)
            #self.check_return_summary(cfg_obj)

    def map_parent_condition_to_bb(self, parent, child_bb, cfg_obj):
        pre_dominators = cfg_obj._pre_dominators[child_bb]
        for condition in cfg_obj._condition_to_sons[parent].keys():
            son_bb = cfg_obj._condition_to_sons[parent][condition]
            
            if son_bb in pre_dominators or son_bb == child_bb:
                self._condition_to_bb[parent][child_bb] = condition
    
    # This function collects all the conditional pre-dominator of a particular basic block
    # Once found it adds out-going edges to that basic block in the range graph 
    def collect_conditional_pre_dominators(self, basic_block, cfg_obj, graph, node, parameters = []):
        if not cfg_obj._cfg.has_node(basic_block):
            return
        parents = cfg_obj._conditional_pre_dominators[basic_block]
        parents = list(set(parents))
        flag_condition = False
        self._condition_to_node[node] = []

        for parent in parents:
            instruction = parent._instructions[-1]
            self.map_parent_condition_to_bb(parent, basic_block, cfg_obj)
            
            # If the pre-condition is a solidity call, collect the arguments of the call
            if type(instruction).__name__ == 'SolidityCall':
                if instruction.function.name.startswith('require') or instruction.function.name.startswith('assert'):
                    self._condition_to_bb[parent][basic_block] = 'true'
                    flag_condition = True
                    arguments = instruction.arguments
            
            # If the pre-condition is a condition, collect the variables used
            if type(instruction).__name__ == 'Condition':
                flag_condition = True
                arguments = instruction.used


            argument = None

            if flag_condition:
                for arg in arguments:
                    if type(arg).__name__ == 'Constant':
                        continue
                    else:
                        argument = arg

                if argument != None:
                    # The argument is a local variable process it using the corresponding method
                    # for processing local vars
                    if type(argument).__name__ == 'LocalVariableSolc':

                        # If the argument is tainted, we know that the pre-condition on a tainted argument handrly matters
                        # as the attacker can cotrol it arbitrarily to satify te pre-condition, so we don't add that as an pre-condition
                        if argument in parameters and is_tainted(self.log, argument, cfg_obj, cfg_obj._function.contract):
                            continue

                        # If the argument is not tainted, then call the corresponding method of processing locals,
                        # this is track the definition of the local in form of state-vars and constants
                        else:
                            var_list = []

                            for lvar, rvar, type_str in process_local_variable(self.log, self, cfg_obj, instruction, 'C', argument, parameters, parent, node, graph):
                                var_list.append(lvar)

                            # If one of value in the val list id 'U', again we don't process it further
                            if 'U' in var_list:
                                continue

                            # Else, we add this in the range node
                            else:
                                if isinstance(var_list[0], RangeNode):
                                    self._condition_to_node[node].append((parent, var_list[0]))

                                else:
                                    # Need to write use-def analysis for this
                                    range_node = RangeNode(var_list[0], parent, 'true', '==')
                                    graph.add_edge(range_node, node)
                                    self._condition_to_node[node].append((parent, range_node))

                    # The argument is a temporary variable process it using the corresponding method
                    # for processing temporary vars
                    elif type(argument).__name__ == 'TemporaryVariable':
                        s_lvar, s_rvar, type_str = process_temporary_variable(self.log, self, argument, cfg_obj, 'C', parameters, parent, node, graph)
                        if s_lvar != 'U' or 'U' not in s_lvar:
                        #if isinstance(s_lvar, list):
                            self._condition_to_node[node].append((parent, s_lvar))

                    # If the argument involves state variable directly, don't need to process further,
                    # we just add that as a pre-condition
                    elif type(argument).__name__ == 'StateVariableSolc':
                        res_var = get_state_var_obj(self.log, argument)
                        range_node = RangeNode(res_var, parent, 'true', '==')
                        graph.add_edge(range_node, node)
                        self._condition_to_node[node].append((parent, range_node))


                    elif type(argument).__name__ == 'ReferenceVariable':
                        s_var = get_origin_variable_from_refvariable(self.log, self, instruction, argument, cfg_obj, 'C', parent)
                        s_var = replace_state_var_with_index_node(s_var, argument, self)
                        range_node = RangeNode(s_var, parent, 'true', '==')
                        graph.add_edge(range_node, node)
                        self._condition_to_node[node].append((parent, range_node))

                    elif type(argument).__name__ == 'LocalVariableInitFromTupleSolc':
                        s_lvar = process_localVariableInitFromTupleSolc(self.log, self, cfg_obj, instruction, 'C', argument, parameters, parent)

                        if s_lvar == 'U' or (isinstance(s_lvar, list) and 'U' in s_lvar):
                            continue

                        else:
                            range_node = RangeNode(s_lvar, parent, 'true', '==')
                            graph.add_edge(range_node, node)
                            self._condition_to_node[node].append((parent, range_node))

                    # We should raise an alert if other types of variable is involved directly
                    # in an conditinal statement
                    else:
                        self.log.warning("Someother variable in condition, figure out!")
                        sys.exit(1)
                    
                    #range_node = RangeNode(s_var, parent, var_right, type_str)
                    #graph.add_edge(range_node, node)
                    flag_condition = False
        
        
        if len(parents) > 0:
            self.get_node_true_false(parents, basic_block, node)


    def get_range_nodes(self, nodes, node_list):
        for node in nodes:
            if isinstance(node, RangeNode):
                node_list.append(node)
            elif isinstance(node, list):
                self.get_range_nodes(node, node_list)
    
    def get_node_true_false(self, parents, child_block, child_node):
        for node_tuple in self._condition_to_node[child_node]:
            parent_bb = node_tuple[0]
            parent_rn = node_tuple[1]

            if parent_bb in parents:
                child_cond = self._condition_to_bb[parent_bb][child_block]
                
                if isinstance(parent_rn, list):
                    node_list = []
                    self.get_range_nodes(parent_rn, node_list)
                    for node in node_list:
                        child_node._true_or_false[node] = child_cond
                
                elif isinstance(parent_rn, RangeNode):
                    child_node._true_or_false[parent_rn] = child_cond

    def process_rvalues(self, cfg_obj, s_var, container_bb, rvalue, parameters, svar_assign_ir, return_values):
        if type(rvalue).__name__ == 'Constant':
            graph_list = self.process_constant_rvalue(s_var, rvalue, container_bb, cfg_obj, svar_assign_ir)

        elif type(rvalue).__name__ == 'LocalVariableSolc':
            graph_list = self.process_localvar_rvalue(s_var, rvalue, parameters, container_bb, cfg_obj, svar_assign_ir)

        elif type(rvalue).__name__ == 'TemporaryVariable':
            graph_list = self.process_tempvar_rvalue(s_var, rvalue, parameters, container_bb, cfg_obj, svar_assign_ir)
        
        elif type(rvalue).__name__ == 'StateVariableSolc':
            graph_list = self.process_statevar_rvalue(s_var, rvalue, parameters, container_bb, cfg_obj, svar_assign_ir)

        elif type(rvalue).__name__ == 'ReferenceVariable':
            graph_list = self.process_refvar_rvalue(s_var, rvalue, container_bb, cfg_obj, svar_assign_ir)
        
        elif type(rvalue).__name__ in SOLIDITY_VARS:
            graph_list = self.process_solidityvar_rvalue(s_var, rvalue, container_bb, cfg_obj, svar_assign_ir)
        else:
            self.log.warning("Other types of rvalues! debug")
            sys.exit(1)
            

        return graph_list

    # We should only keep state variable assignments in the range graph. Once we have
    # seen a state variable assignment, we should add that as node in the range graph.
    # We know the lvalue is a state variable and rvalue is something other than state variable
    # we need to track the source of the rvalue
    def process_statevar_assignment(self, cfg_obj, parameters, return_values):
        count = 1
        graph_list = []
        
        for svar_assign_ir in cfg_obj.state_vars_written.keys():
            container_bb = cfg_obj.state_vars_written[svar_assign_ir]
            lvalue = svar_assign_ir.lvalue

            # If lvalue is a reference variable, we tract it's definition and get the actual storage
            # variable
            if type(lvalue).__name__ == 'ReferenceVariable':
                s_var = get_origin_variable_from_refvariable(self.log, self, svar_assign_ir, lvalue, cfg_obj, '')
                s_var = replace_state_var_with_index_node(s_var, lvalue, self)

            else:
                s_var = get_state_var_obj(self.log, lvalue)
            
            # If an instruction has rvalue, it mean that the instruction is an assignment
            if hasattr(svar_assign_ir, 'rvalue'):   
                if cfg_obj not in self.value_graph.keys():
                    self.value_graph[cfg_obj] = {}
                
                if s_var not in self.value_graph[cfg_obj].keys():
                    self.value_graph[cfg_obj][s_var] = []
            
                rvalue = svar_assign_ir.rvalue
                graph_list = self.process_rvalues(cfg_obj, s_var, container_bb, rvalue, parameters, svar_assign_ir, return_values)
            
            # If the instruction is not an assignment
            else:
                # If it is an Member or Index then we know that this can be a state var assignment
                if type(svar_assign_ir).__name__ == 'Member' or type(svar_assign_ir).__name__ == 'Index' or type(svar_assign_ir).__name__ == 'Length':
                    continue

                elif type(svar_assign_ir).__name__ == 'Delete':
                    continue
                
                elif type(svar_assign_ir).__name__ == 'Push':
                    if cfg_obj not in self.value_graph.keys():
                        self.value_graph[cfg_obj] = {}
                    
                    if s_var not in self.value_graph[cfg_obj].keys():
                        self.value_graph[cfg_obj][s_var] = []

                    graph_list = self.process_rvalues(cfg_obj, s_var, container_bb, svar_assign_ir.value, parameters, svar_assign_ir, return_values)
                
                # : fix issues with unary assignment
                elif type(svar_assign_ir).__name__ == 'Unary':
                    if cfg_obj not in self.value_graph.keys():
                        self.value_graph[cfg_obj] = {}
                    
                    if s_var not in self.value_graph[cfg_obj].keys():
                        self.value_graph[cfg_obj][s_var] = []
                    graph_list = self.process_unary_statements(s_var, svar_assign_ir, container_bb, parameters, cfg_obj)
                
                
                # If the instruction is binary, then proceed to handle the binary instruction
                elif type(svar_assign_ir).__name__ == 'Binary':
                    if cfg_obj not in self.value_graph.keys():
                        self.value_graph[cfg_obj] = {}
                    
                    if s_var not in self.value_graph[cfg_obj].keys():
                        self.value_graph[cfg_obj][s_var] = []

                    graph_list = self.process_binary_statements(s_var, svar_assign_ir, container_bb, parameters, cfg_obj)

                elif type(svar_assign_ir).__name__ == 'InitArray':
                    if cfg_obj not in self.value_graph.keys():
                        self.value_graph[cfg_obj] = {}
                    
                    if s_var not in self.value_graph[cfg_obj].keys():
                        self.value_graph[cfg_obj][s_var] = []
                    
                    graph_list = self.process_array_initialization(s_var, svar_assign_ir, container_bb, parameters, cfg_obj)

                elif type(svar_assign_ir).__name__ == 'Unpack':
                    if cfg_obj not in self.value_graph.keys():
                        self.value_graph[cfg_obj] = {}

                    if s_var not in self.value_graph[cfg_obj].keys():
                        self.value_graph[cfg_obj][s_var] = []

                    graph_list = self.process_tuple_unpack(s_var, svar_assign_ir, container_bb, parameters, cfg_obj)

                else:
                    #if DEBUG:
                    self.log.warning("Not any rvalue, can it still be assigning to state variable!")
                    sys.exit(1)
            
            
            for graph in graph_list:
                self.collect_conditional_pre_dominators(container_bb, cfg_obj, graph[0], graph[1], parameters)
                #self.print_range_graph(self.graph_dir, cfg_obj._function, graph[0], str(count))
                count += 1

    def process_tuple_unpack(self, svar, svar_assign_ir, container_bb, parameters, cfg_obj):
        graphs_list = []
        tuple_var = svar_assign_ir.tuple
        lvar, rvar, type_str = process_tuple_variable(self.log, self, cfg_obj, svar_assign_ir, '', tuple_var, parameters)
        index = svar_assign_ir.index
        try:
            s_lvar = lvar[index]
        except:
            self.log.warning("This can only happen due to slither insanity, where slither does not capture the returned tuple properly, we ignore it for now!")
            sys.exit(1)

        range_node = RangeNode(svar, container_bb, s_lvar, "=")
        s_graph = nx.MultiDiGraph()
        s_graph.add_node(range_node)
        svar_identifier_triplet = (range_node, s_graph, range_node._value)
        self.value_graph[cfg_obj][svar].append(svar_identifier_triplet)
        graphs_list.append((s_graph, range_node))

        return graphs_list

    def process_array_initialization(self, svar, svar_assign_ir, container_bb, parameters, cfg_obj):
        graphs_list = []
        rvalue = ['initarray']
        rvalue.extend(svar_assign_ir.init_values)
        range_node = RangeNode(svar, container_bb, rvalue, "=")
        s_graph = nx.MultiDiGraph()
        s_graph.add_node(range_node)
        svar_identifier_triplet = (range_node, s_graph, range_node._value)
        self.value_graph[cfg_obj][svar].append(svar_identifier_triplet)
        graphs_list.append((s_graph, range_node))            

        return graphs_list
    
    def process_unary_statements(self, svar, svar_assign_ir, container_bb, parameters, cfg_obj):
        graphs_list = []
        range_node_list = []
        var_right = process_left_or_right_variable(self.log, self, svar_assign_ir.variable_right, cfg_obj, '', svar_assign_ir, parameters)
        op_str = svar_assign_ir.type_str

        if type(var_right).__name__ == 'int':
            res = perform_arithmetic_op('', var_right, op_str)
            range_node = RangeNode(svar, container_bb, res, "=")
            range_node_list.append(range_node)

        else:
            res_list = []
            res_list.append(op_str)
            res_list.append(var_right)
            range_node = RangeNode(svar, container_bb, res_list, "=")
            range_node_list.append(range_node)

        for range_node in range_node_list:
            s_graph = nx.MultiDiGraph()
            s_graph.add_node(range_node)
            svar_identifier_triplet = (range_node, s_graph, range_node._value)
            self.value_graph[cfg_obj][svar].append(svar_identifier_triplet)
            graphs_list.append((s_graph, range_node))

        return graphs_list                                     

    def process_binary_statements(self, svar, svar_assign_ir, container_bb, parameters, cfg_obj):
        graphs_list = []
        range_node_list = []
        var_left = process_left_or_right_variable(self.log, self, svar_assign_ir.variable_left, cfg_obj, '', svar_assign_ir, parameters)
        var_right = process_left_or_right_variable(self.log, self, svar_assign_ir.variable_right, cfg_obj, '', svar_assign_ir, parameters)
        op_str = svar_assign_ir.type_str

        if type(var_left).__name__ == 'int' and type(var_right).__name__ == 'int':
            res = perform_arithmetic_op(var_left, var_right, op_str)
            range_node = RangeNode(svar, container_bb, res, "=")
            range_node_list.append(range_node)

        else:
            res_list = []
            s_lvar, s_rvar, type_str = handle_non_constant_binary_op(self.log, self, var_left, var_right, op_str)
            res_list.append(s_lvar)
            range_node = RangeNode(svar, container_bb, res_list, "=")
            range_node_list.append(range_node)

        for range_node in range_node_list:
            s_graph = nx.MultiDiGraph()
            s_graph.add_node(range_node)
            svar_identifier_triplet = (range_node, s_graph, range_node._value)
            self.value_graph[cfg_obj][svar].append(svar_identifier_triplet)
            graphs_list.append((s_graph, range_node))

        return graphs_list                 


    def process_localvar_rvalue(self, svar, rvalue, parameters, containter_bb, cfg_obj, svar_assign_ir):
        value_list = []
        graphs_list = []
        

        # If the local variable is tainted wrt to the contract mark the
        # state variable assignment as un-constrained
        if is_tainted(self.log, rvalue, cfg_obj, cfg_obj._function.contract):
            value_list.append('U')            
        else:
            value_list = []
            
            value_list = process_left_or_right_variable(self.log, self, rvalue, cfg_obj, '', svar_assign_ir, parameters)
            #for lvar, rvar, type_str in process_local_variable(self.log, self, cfg_obj, '', rvalue, parameters):
                #value_list.append(lvar)
            
            if DEBUG:
                self.log.warning("What condition makes rvalue to be not tainted!")

        for value in value_list:
            range_node = RangeNode(svar, containter_bb, value, "=")

            s_graph = nx.MultiDiGraph()
            s_graph.add_node(range_node)
            svar_identifier_triplet = (range_node, s_graph, value)
            self.value_graph[cfg_obj][svar].append(svar_identifier_triplet)
            graphs_list.append((s_graph, range_node))
        
        return graphs_list
            

    def process_statevar_rvalue(self, svar, rvalue, parameters, containter_bb, cfg_obj, svar_assign_ir):
        graphs_list = []
        rvalue_origin = get_state_var_obj(self.log, rvalue)

        if rvalue_origin in self._constant_state_vars.keys():
            rvalue_origin = self._constant_state_vars[rvalue_origin]
        
        s_graph = nx.MultiDiGraph()
        range_node = RangeNode(svar, containter_bb, rvalue_origin, "=")
        s_graph.add_node(range_node)
        svar_identifier_triplet = (range_node, s_graph, rvalue_origin)
        self.value_graph[cfg_obj][svar].append(svar_identifier_triplet)
        graphs_list.append((s_graph, range_node))      
        return graphs_list
    

    def get_structure_def(self, svar, cfg_obj):
        if isinstance(svar, StateVar):
            state_var = svar._state_var
            structure = SDG.map_svars_to_struct[state_var]

        elif isinstance(svar, VarNode):
            structure = SDG.map_svars_to_struct[svar._field]
        
        elif isinstance(svar, IndexNode):
            if svar.member is not None:
                structure = SDG.map_svars_to_struct[svar]
            else:
                structure = self.get_structure_def(svar.origin, cfg_obj)

        else:
            structure = SDG.map_svars_to_struct[svar]
        
        return structure
    
    def process_tempvar_rvalue(self, svar, rvalue, parameters, containter_bb, cfg_obj, svar_assign_ir):
        s_lvar = None
        s_rvar = None
        type_str = None
        graphs_list = []
        value_list = []

        if is_tainted(self.log, rvalue, cfg_obj, cfg_obj._function.contract):
            s_lvar = 'U'
            value_list.append(s_lvar)
        
        else:
            s_lvar, s_rvar, type_str = process_temporary_variable(self.log, self, rvalue, cfg_obj, '', parameters)
            value_list.append(s_lvar)
            
            if DEBUG:
                self.log.warning('Checkout Here')

        if type_str == 'new_s':
            structure = self.get_structure_def(svar, cfg_obj)

            i = 0
            initialization_length = len(s_lvar)
            for elem in structure.elems.keys():
                if i < initialization_length:
                    index_node = IndexNode(svar, None, structure.elems[elem])
                    s_graph = nx.MultiDiGraph()
                    range_node = RangeNode(index_node, containter_bb, s_lvar[i], "=")
                    s_graph.add_node(range_node)
                    svar_identifier_triplet = (range_node, s_graph, s_lvar[i])
                    self.value_graph[cfg_obj][svar].append(svar_identifier_triplet)
                    graphs_list.append((s_graph, range_node))
                    i += 1            
        else:
            for value in value_list:           
                self.record_constructor_constant_vars(cfg_obj, svar, value)
                s_graph = nx.MultiDiGraph()
                range_node = RangeNode(svar, containter_bb, value, "=")
                s_graph.add_node(range_node)
                svar_identifier_triplet = (range_node, s_graph, value)
                self.value_graph[cfg_obj][svar].append(svar_identifier_triplet)
                graphs_list.append((s_graph, range_node))
        
        return graphs_list

    def process_constant_rvalue(self, s_var, rvalue, container_bb, cfg_obj, svar_assign_ir):
        graphs_list = []
        self.record_constructor_constant_vars(cfg_obj, s_var, rvalue)
        range_node = RangeNode(s_var, container_bb, rvalue, "=")
        s_graph = nx.MultiDiGraph()
        s_graph.add_node(range_node)
        svar_identifier_triplet = (range_node, s_graph, rvalue)
        self.value_graph[cfg_obj][s_var].append(svar_identifier_triplet)
        graphs_list.append((s_graph, range_node))
        return graphs_list
    
    def process_solidityvar_rvalue(self, s_var, rvalue, container_bb, cfg_obj, svar_assign_ir):
        graphs_list = []
        self.record_constructor_constant_vars(cfg_obj, s_var, rvalue)
        range_node = RangeNode(s_var, container_bb, rvalue, "=")
        s_graph = nx.MultiDiGraph()
        s_graph.add_node(range_node)
        svar_identifier_triplet = (range_node, s_graph, rvalue)
        self.value_graph[cfg_obj][s_var].append(svar_identifier_triplet)
        graphs_list.append((s_graph, range_node))
        return graphs_list
    
    def process_refvar_rvalue(self, svar, rvalue, container_bb, cfg_obj, svar_assign_ir):
        graphs_list = []
        origin_var = get_origin_variable_from_refvariable(self.log, self, None, rvalue, cfg_obj, '')

        if origin_var in self._constant_state_vars.keys():
            origin_var = self._constant_state_vars[origin_var]
        
        range_node = RangeNode(svar, container_bb, origin_var, "=")
        s_graph = nx.MultiDiGraph()
        s_graph.add_node(range_node)
        svar_identifier_triplet = (range_node, s_graph, origin_var)
        self.value_graph[cfg_obj][svar].append(svar_identifier_triplet)
        graphs_list.append((s_graph, range_node))
        return graphs_list

    def generate_cfgs(self, contract, function):
        if function not in CFG.function_cfg.keys():
            cfg_obj = CFG(self.slither_obj, contract, function, self.graph_dir, self._dump_graph, self.log)
            CFG.function_cfg[function] = cfg_obj
        return CFG.function_cfg[function]
    
    def get_root_nodes(self, graph):
        root_nodes = [x for x in graph.nodes if graph.out_degree(x) >= 0 and graph.in_degree(x) == 0]
        return root_nodes
    
    def get_leaf_function_nodes(self, graph):
        leaf_nodes = [x for x in graph.nodes if graph.out_degree(x) == 0 and graph.in_degree(x) >= 0]
        return leaf_nodes
    
    def print_range_graph(self, graph_dir, function, graph, index=1):
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