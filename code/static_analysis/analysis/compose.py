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
from util import *
from basic_block import *
from instr_block import *
from icfg import *
from varnode import *
from sdg import *
import copy

class Compose:
    """
        
    """

    def __init__(self, slither_obj, sdg_obj, sdg_objects, is_ext_call, is_ether_sending, owner_only_functions, target_contracts, graph_dir, dump_graph, dao, tod, log):
        self._slither = slither_obj
        self._is_ext_call = is_ext_call  # Whether the sdg contains the external call or not
        self._is_ether_sending = is_ether_sending
        self.dao = dao  # Whether we want to detect dao
        self.tod = tod  # Whether we want to detect tod
        self._dump_graph = dump_graph
        self._target_contracts = target_contracts
        self._log = log
        self._sdg_obj = sdg_obj
        self._graph_dir = graph_dir
        self.owner_only_functions = owner_only_functions
        self._sdg = sdg_obj._sdg
        self._all_predecessors = []
        self._sdg_objects = sdg_objects

        # Composed sdg information for DAO
        self._dao_composed_sdgs = {}
        self._dao_composed_sdg_to_call_predecessors = {}
        self._dao_composed_sdg_details = defaultdict(dict)

        # Composed sdg information for TOD
        self._tod_composed_sdgs = None
        self._tod_composed_sdg_details = defaultdict(dict)
        self._tod_composed_sdg_to_predecessors = {}
        self.setup()
    
    def setup(self):
        self.build_composed_sdg(self._sdg, self._sdg_obj, self._sdg_objects)

        count = 1
        if self._dump_graph == True and self.dao is True:
            for function_1 in self._dao_composed_sdgs.keys():
                for function_2 in self._dao_composed_sdgs[function_1].keys():
                    composed_sdg_list = self._dao_composed_sdgs[function_1][function_2]

                    count = 1
                    for composed_sdg in composed_sdg_list:
                        name = "_dao_composed_sdg" + "_" + str(count)
                        self.print_sdg_dot(self._graph_dir, function_1, function_2, composed_sdg[0], name)
                        count = count + 1

        count = 1
        if self._dump_graph is True and self.tod is True:
            for function_1 in self._tod_composed_sdgs.keys():
                for function_2 in self._tod_composed_sdgs[function_1].keys():
                    composed_sdg_list = self._tod_composed_sdgs[function_1][function_2]

                    count = 1
                    for composed_sdg in composed_sdg_list:
                        name = "_tod_composed_sdg" + "_" + str(count)
                        self.print_sdg_dot(self._graph_dir, function_1, function_2, composed_sdg[0], name)
                        count = count + 1

    def get_root_nodes(self, graph):
        nodes = []

        for node in graph.nodes:
            if isinstance(node, InstrBlock):
                predecessors = graph.predecessors(node)
                count = 0
                
                for predecessor in predecessors:
                    if isinstance(predecessor, InstrBlock):
                        count = count + 1
                
                if count == 0:
                    nodes.append(node)

        return nodes
    
    def get_leaf_nodes(self, graph):
        nodes = []

        for node in graph.nodes:
            if isinstance(node, InstrBlock):
                successors = graph.successors(node)
                count = 0
                
                for successor in successors:
                    if isinstance(successor, InstrBlock):
                        count = count + 1
                
                if count == 0:
                    nodes.append(node)

        return nodes

    def get_all_variable_nodes(self, graph):
        varnodes = [x for x in graph.nodes if not isinstance(x, InstrBlock)]
        return varnodes

    def get_successors_copy(self, graph, node):
        successors = graph.successors(node)
        successors_copy = []
        
        for successor in successors:
            if isinstance(successor, InstrBlock):
                successors_copy.append(successor)
        
        return successors_copy
    
    def get_matching_sdgs(self, sdg_obj):
        source_sdg = sdg_obj._sdg

        source_sdg_varnodes = self.get_all_variable_nodes(source_sdg)
        matching_sdgs = []

        for function in self._sdg_objects:
            # We should not consider modifiers during sdg composition
            if type(function).__name__ == 'ModifierSolc' or function.is_constructor:
                continue

            # We should only compose functions which are part of same contract
            if function.contract == sdg_obj._function.contract:
                pre_modifiers = function.modifiers
                #common_modifiers = list(set(pre_modifiers).intersection(set(self._blacklisted_modifiers)))
                target_sdg = self._sdg_objects[function]._sdg
                target_sdg_varnodes = self.get_all_variable_nodes(target_sdg)
                common_varnodes = list(set(source_sdg_varnodes) & set(target_sdg_varnodes))

                if len(common_varnodes) != 0 and sdg_obj._contract == self._sdg_objects[function]._contract and function not in self.owner_only_functions:
                    matching_sdgs.append(self._sdg_objects[function])
        
        return matching_sdgs, source_sdg_varnodes

    def add_src_to_dest_edges(self, graph, src_nodes, dest_nodes, function_name=None):
        for src_node in src_nodes:
            for dest_node in dest_nodes:
                if function_name != None:
                    graph.add_edge(src_node, dest_node, key=function_name)
                else:
                    graph.add_edge(src_node, dest_node)
    
    def remove_edges(self, graph, src_nodes, dest_nodes):
        for src_node in src_nodes:
            for dest_node in dest_nodes:
                graph.remove_edge(src_node, dest_node)        

    def get_all_predecessors(self, graph, node):
        predecessors = graph.predecessors(node)

        for predecessor in predecessors:
            if isinstance(predecessor, InstrBlock) and predecessor not in self._all_predecessors:
                self._all_predecessors.append(predecessor)
                self.get_all_predecessors(graph, predecessor)


    def get_all_successors(self, node, graph, visited_nodes):
        all_succs = []
        successors = list(graph.successors(node))
        
        for successor in successors:
            if successor not in visited_nodes and isinstance(successor, InstrBlock):
                visited_nodes.append(successor)
                all_succs.append(successor)
                all_succs.extend(self.get_all_successors(successor, graph, visited_nodes))
        
        return all_succs

    def remove_nonused_varnode_edges(self, sdg, sdg_obj, var_nodes, all_preds, call_node):
        sdg.remove_nodes_from(all_preds)
        icfg = sdg_obj._icfg
        origin_bb = call_node._origin_bb
        leaf_basic_blocks = [x for x in icfg.nodes if icfg.out_degree(x) == 0]
        state_vars_used = copy.copy(origin_bb._pred_state_var_used)
        state_vars_used.update(origin_bb._state_vars_used)

        #if sdg_obj._function.name == 'splitFunds':
            #print("")
        leaf_state_vars_used = {}
        
        for basic_block in leaf_basic_blocks:
            leaf_state_vars_used.update(basic_block._pred_state_var_used)
            leaf_state_vars_used.update(basic_block._state_vars_used)
        
        difference = []
        for k,v in leaf_state_vars_used.items():
            if k not in state_vars_used.keys():
                difference.extend(v)

        difference = list(set(difference))
        all_nodes = list(sdg.nodes)
        for var_node in var_nodes:
            if var_node not in difference:
                successors = list(sdg.successors(var_node))
                for succ in successors:
                    if succ in all_nodes:
                        sdg.remove_edge(var_node, succ)

    def remove_nonused_varnode_edges_tod(self, sdg, sdg_obj, var_nodes, all_succs, target_node):
        # Remove the nodes from the sdg after the target node
        sdg.remove_nodes_from(all_succs)
        icfg = sdg_obj._icfg
        origin_bb = target_node._origin_bb
        leaf_basic_blocks = [x for x in icfg.nodes if icfg.out_degree(x) == 0]
        state_vars_used = copy.copy(origin_bb._pred_state_var_used)
        state_vars_used.update(origin_bb._state_vars_used)

        leaf_state_vars_used = {}

        for basic_block in leaf_basic_blocks:
            leaf_state_vars_used.update(basic_block._pred_state_var_used)
            leaf_state_vars_used.update(basic_block._state_vars_used)


        difference = []
        for k, v in state_vars_used.items():
            #if k not in lea.keys():
            difference.extend(v)

        difference = list(set(difference))

        # These nodes contains all the nodes in paths from the root node
        # till the target node
        all_nodes = list(sdg.nodes)

        # Now for every variable node present in the sdg
        # we iterate over it and see if it the part of the current
        # set of state variables which influences the current sdg
        # if it is not then we remove the edges which are not part of the
        # current sdg
        for var_node in var_nodes:
            if var_node not in difference:
                successors = list(sdg.successors(var_node))
                if len(successors) == 0:
                    sdg.remove_node(var_node)

                else:
                    for succ in successors:
                        if succ not in all_nodes:
                            sdg.remove_edge(var_node, succ)

    def get_dao_composed_sdg(self, all_sdgs, all_var_nodes, all_instr_nodes):
        composed_sdgs = defaultdict(dict)
        composed_sdg_to_call_predecessors = {}
        composed_sdgs[self._sdg_obj._function] = {}
        self._dao_composed_sdg_details[self._sdg_obj._function] = {}
        target_sdg = self._sdg
        sdg_obj = self._sdg_obj

        # When we combine two SDG graph's there can multiple ways two graphs
        # can be combined depending on the number of tainted high-level calls or
        # low level calls
        for matching_sdg_obj in all_sdgs:
            composed_sdgs[self._sdg_obj._function][matching_sdg_obj._function] = []

        for graph_node in target_sdg.nodes:
            if isinstance(graph_node, InstrBlock):
                instr = graph_node._instruction

                if type(instr).__name__ == 'LowLevelCall' or type(instr).__name__ == 'HighLevelCall':

                    if self._sdg_obj._ext_calls.get(instr) is None:
                        continue

                    else:
                        if self._sdg_obj._ext_calls[instr] is False:
                            continue

                    modified_sdg = target_sdg.copy(as_view=False)

                    # Find all the instruction blocks that appear after the external call
                    successors = self.get_successors_copy(target_sdg, graph_node)
                    self._all_predecessors = []
                    # Find all the instruction blocks that appear before the external call including
                    # the external call node

                    all_succs = self.get_all_successors(graph_node, target_sdg, [])
                    if graph_node not in all_succs:
                        all_succs.append(graph_node)

                    self._all_predecessors = list(set(all_instr_nodes) - set(all_succs))

                    # if sdg_obj._function.name == 'withdrawToken':

                    self.remove_nonused_varnode_edges(modified_sdg, sdg_obj, all_var_nodes, self._all_predecessors,
                                                      graph_node)
                    self._all_predecessors.append(graph_node)
                    temp_sdgs = {}

                    for matching_sdg_obj in all_sdgs:

                        # if sdg_obj._function.name == 'withdrawToken' and matching_sdg_obj._function.name == 'deposit':

                        # If the matching sdg function is same as the current sdg function, deepcopy
                        # the sdg graph
                        if matching_sdg_obj._function == self._sdg_obj._function:
                            matching_sdg = copy.deepcopy(matching_sdg_obj._sdg)
                            root_nodes = self.get_root_nodes(matching_sdg)
                            leaf_nodes = self.get_leaf_nodes(matching_sdg)

                        else:
                            matching_sdg = matching_sdg_obj._sdg
                            root_nodes = matching_sdg_obj._root_nodes
                            leaf_nodes = matching_sdg_obj._leaf_nodes

                        function_start = "Enter - " + matching_sdg_obj._function.name
                        function_end = "End - " + matching_sdg_obj._function.name

                        # This is for inlining matching sdg graph with the current sdg after the
                        # external call
                        composed_sdg = nx.compose(modified_sdg, matching_sdg)

                        self.remove_edges(composed_sdg, [graph_node], successors)

                        self.add_src_to_dest_edges(composed_sdg, [graph_node], root_nodes, function_start)
                        self.add_src_to_dest_edges(composed_sdg, leaf_nodes, successors, function_end)

                        composed_sdgs[self._sdg_obj._function][matching_sdg_obj._function].append((composed_sdg, graph_node, modified_sdg, matching_sdg))
                        composed_sdg_to_call_predecessors[composed_sdg] = copy.copy(self._all_predecessors)
                        self._dao_composed_sdg_details[self._sdg_obj._function][matching_sdg_obj._function] = (modified_sdg, matching_sdg)

        return composed_sdgs, composed_sdg_to_call_predecessors

    def get_tod_composed_sdg(self, all_sdgs, all_var_nodes, all_instr_nodes):
        composed_sdgs = defaultdict(dict)
        composed_sdg_to_predecessors = {}
        composed_sdgs[self._sdg_obj._function] = {}
        self._tod_composed_sdg_details[self._sdg_obj._function] = {}
        target_sdg = self._sdg
        sdg_obj = self._sdg_obj

        # We compose sdgs with the target sdg to see whether execution of the matching function
        # corresponding to the sdg has any effect on the execution of target function
        for matching_sdg_obj in all_sdgs:
            composed_sdgs[self._sdg_obj._function][matching_sdg_obj._function] = []

        # Iterate over the nodes of the target sdg
        for graph_node in all_instr_nodes:
            is_ether_sending = False

            # Here we see whether the ether sending functions are influenced by any storage
            # variable or not
            if isinstance(graph_node, InstrBlock):
                instruction = graph_node._instruction

                if type(instruction).__name__ == 'LowLevelCall' or type(instruction).__name__ == 'Send' or type(instruction).__name__ == 'Transfer':
                    #preds = list(target_sdg.predecessors(graph_node))
                    is_ether_sending = True
                else:
                    continue
            else:
                continue

            modified_sdg = target_sdg.copy(as_view=False)
            target_leaf_nodes = sdg_obj._leaf_nodes

            # Find all the instruction blocks that appear before the external call including
            # the external call node
            self._all_predecessors = []
            self.get_all_predecessors(target_sdg, graph_node)

            if graph_node not in self._all_predecessors:
                self._all_predecessors.append(graph_node)

            all_successors = list(set(all_instr_nodes) - set(self._all_predecessors))
            self.remove_nonused_varnode_edges_tod(modified_sdg, sdg_obj, all_var_nodes, all_successors, graph_node)

            for matching_sdg_obj in all_sdgs:
                # If the matching sdg function is same as the current sdg function, deepcopy
                # the sdg graph
                if matching_sdg_obj._function == self._sdg_obj._function:
                    matching_sdg = copy.deepcopy(matching_sdg_obj._sdg)
                    root_nodes = self.get_root_nodes(matching_sdg)
                    leaf_nodes = self.get_leaf_nodes(matching_sdg)

                else:
                    matching_sdg = matching_sdg_obj._sdg
                    root_nodes = matching_sdg_obj._root_nodes
                    leaf_nodes = matching_sdg_obj._leaf_nodes

                function_start = "Enter - " + matching_sdg_obj._function.name
                function_end = "End - " + matching_sdg_obj._function.name

                # This is for inlining matching sdg graph with the target sdg one after the other i.e,
                # matching sdg followed by target sdg
                composed_sdg = nx.compose(modified_sdg, matching_sdg)
                self.add_src_to_dest_edges(composed_sdg, leaf_nodes, sdg_obj._root_nodes, function_end)

                if len(root_nodes) != 1:
                    print("")
                #assert len(root_nodes) == 1, 'Fail here because root nodes can only be one'

                composed_sdgs[self._sdg_obj._function][matching_sdg_obj._function].append((composed_sdg, root_nodes[0], modified_sdg, matching_sdg))
                composed_sdg_to_predecessors[composed_sdg] = copy.copy(self._all_predecessors)
                self._tod_composed_sdg_details[self._sdg_obj._function][matching_sdg_obj._function] = (modified_sdg, matching_sdg)

        return composed_sdgs, composed_sdg_to_predecessors

    def build_composed_sdg(self, target_sdg, sdg_obj, sdg_objects):
        # Get all the matching SDG's which share common variables and are not owner only
        all_sdgs, all_var_nodes = self.get_matching_sdgs(self._sdg_obj)

        # Get all the instruction nodes for the target sdg, target sdg is the one which we want to analyse to see if
        # it is vulnerable or not.
        # In terms of DAO, target sdg is the one which has the external call.
        # In terms of TOD, target sdg is the one which is the function which can be influenced by
        # the execution of other functions before this one.
        all_instr_nodes = [x for x in target_sdg.nodes if isinstance(x, InstrBlock)]

        # We only consider composing sdg for the function if dao pattern is set to true and
        # the sdg for the function has external call
        if self.dao is True and self._is_ext_call is True:
            self._dao_composed_sdgs, self._dao_composed_sdg_to_call_predecessors = self.get_dao_composed_sdg(all_sdgs, all_var_nodes, all_instr_nodes)

        # Will only consider composing sdg only if the tos pattern is true
        if self.tod is True and self._is_ether_sending is True:
            self._tod_composed_sdgs, self._tod_composed_sdg_to_predecessors = self.get_tod_composed_sdg(all_sdgs, all_var_nodes, all_instr_nodes)

    def print_sdg_dot(self, graph_dir, function_1, function_2, graph, name=None):
        content = ''
        styles = ['dashed']
        # Ref: https://stackoverflow.com/questions/33722809/nx-write-dot-generates-redundant-nodes-when-input-nodes-have-a-colon
        dot_file_name = function_1.name + "_" + function_2.name + name + ".dot"
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

        png_file_name = function_1.name + "_" + function_2.name + name + ".png"
        png_file_path = os.path.join(graph_dir, png_file_name)
        dot_graph.write_png(png_file_path)