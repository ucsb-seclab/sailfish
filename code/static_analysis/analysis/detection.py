import slither
import shutil
import sys
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
from compose import *
from util import *
from symex_helper import *
import copy
import time

class Detection:
    """
        
    """
    def __init__(self, slither_obj, contract_name, composed_sdg_obj, sdg_objects, icfg_objects, graph_dir, dump_graph, dao, tod, vrg_obj, log):
        self._slither = slither_obj
        self.dao = dao
        self.tod = tod
        self.vrg_obj = vrg_obj
        self.dao_count = 1
        self.tod_count = 1
        self.dao_per_function_paths = {}
        self.dao_symex_paths = {}
        self.tod_per_function_paths = {}
        self.tod_symex_paths = {}

        self._dump_graph = dump_graph
        self.dao_feasible_paths = {}
        self.tod_feasible_paths = {}
        self._sdg_objects = sdg_objects
        self._icfg_objects = icfg_objects
        self._composed_sdg_obj = composed_sdg_obj
        self._graph_dir = graph_dir
        self._contract_name = contract_name
        self._detected_edges = {}
        self._final_results = {}
        self.global_detection = defaultdict(list)
        self._log = log
        self.global_vars = None
        self.global_constant_vars = None
        self.range_vars = None
        self.global_blocks = None
        self.range_blocks = None
        self.total_range_instructions = None
        self.setup()
    
    def setup(self):
        self.global_vars, self.global_constant_vars, self.range_vars, self.global_blocks, self.range_blocks, self.total_range_instructions = compute_range_blocks(self._slither, self.vrg_obj, self._log)

        if self.dao is True:
            self.detect_dao_patterns()
        if self.tod is True:
            self.detect_tod_patterns()

    def detect_dao_patterns(self):
        for function in self._composed_sdg_obj.keys():
            composed_graphs = self._composed_sdg_obj[function]._dao_composed_sdgs
            if composed_graphs is None:
                continue

            composed_graph_to_call_predecessors = self._composed_sdg_obj[function]._dao_composed_sdg_to_call_predecessors
            composed_sdg_details = self._composed_sdg_obj[function]._dao_composed_sdg_details

            for function_1 in composed_graphs.keys():
                for function_2 in composed_graphs[function_1].keys():
                    composed_graph_list = composed_graphs[function_1][function_2]
                    count = 1

                    for composed_graph in composed_graph_list:
                        # pair = composed_sdg_details[function_1][function_2]
                        src_graph = composed_graph[2]
                        target_graph = composed_graph[3]
                        self.detect_dao_read_write_dependencies(function_1, src_graph, function_2, target_graph,
                                                            composed_graph[0], composed_graph[1],
                                                            composed_graph_to_call_predecessors[composed_graph[0]],
                                                            str(count))
                        count = count + 1

    def detect_tod_patterns(self):
        for function in self._composed_sdg_obj.keys():
            composed_graphs = self._composed_sdg_obj[function]._tod_composed_sdgs
            if composed_graphs is None:
                continue
            composed_sdg_details = self._composed_sdg_obj[function]._tod_composed_sdg_details
            tod_composed_sdg_to_predecessors = self._composed_sdg_obj[function]._tod_composed_sdg_to_predecessors

            for function_1 in composed_graphs.keys():
                for function_2 in composed_graphs[function_1].keys():
                    composed_graph_list = composed_graphs[function_1][function_2]
                    count = 1

                    for composed_graph in composed_graph_list:
                        # pair = composed_sdg_details[function_1][function_2]
                        src_graph = composed_graph[2]
                        target_graph = composed_graph[3]

                        self.detect_tod_read_write_dependencies(function_1, src_graph, function_2, target_graph, composed_graph[0], composed_graph[1],
                                                                tod_composed_sdg_to_predecessors[composed_graph[0]], str(count))

    def get_all_variable_nodes(self, graph):
        varnodes = [x for x in graph.nodes if not isinstance(x, InstrBlock)]
        return varnodes

    def is_reachable_destination(self, src_node, dest_node, var_node, composed_graph):
        
        if nx.algorithms.shortest_paths.has_path(composed_graph, src_node, dest_node):
            return True
        else:
            return False

    def get_paths_from_src_dest(self, icfg, src_bbs, dest_bbs):
        all_paths = []
        for src_bb in src_bbs:
            
            for dest_bb in dest_bbs:
                for path in nx.algorithms.simple_paths.all_simple_paths(icfg, src_bb, dest_bb):
                    all_paths.append(path)
        
        return all_paths

    def get_root_nodes(self, graph):
        nodes = [x for x in graph.nodes if graph.in_degree(x) == 0 and isinstance(x, BasicBlock)]
        return nodes    
    
    def get_leaf_nodes(self, graph):
        nodes = [x for x in graph.nodes if graph.out_degree(x) == 0 and isinstance(x, BasicBlock)]
        return nodes  

    def get_nodes_from_paths(self, paths):
        all_nodes = []

        for path in paths:
            for node in path:
                all_nodes.append(node)
        
        all_nodes = list(set(all_nodes))
        return all_nodes
    
    def add_src_to_dest_edges(self, graph, src_nodes, dest_nodes):
        for src_node in src_nodes:
            for dest_node in dest_nodes:
                graph.add_edge(src_node, dest_node)
    
    def connect_two_graphs(self, subgraph_src, subgraph_target):
        src_leaf_nodes = self.get_leaf_nodes(subgraph_src)
        target_root_nodes = self.get_root_nodes(subgraph_target)
        composed_graph =  nx.compose(subgraph_src, subgraph_target)
        self.add_src_to_dest_edges(composed_graph, src_leaf_nodes, target_root_nodes)
        return composed_graph

    def get_target_node(self, icfg_obj, graph, node):
        target_node = None
        last_instruction = node._instructions[-1]
        
        if type(last_instruction).__name__ == 'SolidityCall' and (last_instruction.function.name.startswith('require') \
            or last_instruction.function.name.startswith('assert')):
            successors = list(graph.successors(node))
            assert len(successors) <= 1, 'Debug successors length can not greater than 1'
            
            if len(successors) > 0:
                graph.remove_edge(node, successors[0])
            basic_block = BasicBlock(['DESTINATION'])
            graph.add_edge(node, basic_block)
            target_node = basic_block

        if type(last_instruction).__name__ == 'Condition':
            successors = list(graph.successors(node))
            if len(successors) > 1:
                left = successors[0]
                right = successors[1]
            else:
                left = successors[0]
                right = successors[0]
            
            left_all_succs = icfg_obj._all_successors[left]
            right_all_succs = icfg_obj._all_successors[right]

            only_left = list(set(left_all_succs) - set(right_all_succs))
            only_left.append(left)
            
            only_right = list(set(right_all_succs) - set(left_all_succs))
            only_right.append(right)

            left_flag = False
            right_flag = False

            collected_vars = self._sdg_objects[icfg_obj._function]._collect_critical_variables

            for l_node in only_left:
                instr = l_node._instructions[-1]
                if type(instr).__name__ == 'NodeSolc':
                    continue

                used_vars = instr.used

                for var in used_vars:
                    if type(var).__name__ == 'Constant':
                        continue
                    if collected_vars.get(var) != None:
                        left_flag = True
                if l_node._is_critical == True:
                    left_flag = True
                    break

            for r_node in only_right:
                instr = r_node._instructions[-1]
                if type(instr).__name__ == 'NodeSolc':
                    continue
                used_vars = instr.used

                for var in used_vars:
                    if type(var).__name__ == 'Constant':
                        continue
                    if collected_vars.get(var) != None:
                        right_flag = True

                if r_node._is_critical == True:
                    right_flag = True
                    break
            
            # This is under-approximation, may be both the branches are critical
            # but we are considering only one of them
            if left_flag == True:
                target_node = left
            
            elif right_flag == True:
                if target_node is None:
                    target_node = right
                else:
                    target_nodes = []
                    target_nodes.append(target_node)
                    target_node.append(right)
                    target_node = target_nodes
            else:
                #self._log("No critical node found!")
                target_node = left

        return target_node
   
    def output_paths(self, matched_function, start_node, primary_function, end_node, call_node, all_preds):
        primary_icfg_obj = self._icfg_objects[primary_function]
        primary_icfg_root_nodes = primary_icfg_obj._root_nodes

        matched_icfg_obj = self._icfg_objects[matched_function]
        matched_icfg_root_nodes = matched_icfg_obj._root_nodes 
        matched_icfg_leaf_nodes = matched_icfg_obj._leaf_nodes 

        # This is the set of paths from the beginging of the caller till the external call
        self.set_root_true(primary_icfg_root_nodes)
        call_node._origin_bb._is_ext_call = True
        all_pred_nodes = get_nodes_between_src_dest(primary_icfg_obj, primary_icfg_root_nodes, [call_node._origin_bb])
        subgraph_1 = copy.deepcopy(primary_icfg_obj._function_icfg.subgraph(all_pred_nodes))
        nx.set_node_attributes(subgraph_1, 'P', 'function_type')
        self.set_root_none(primary_icfg_root_nodes)
        call_node._origin_bb._is_ext_call = None
        leaf_node = call_node._origin_bb._prev_bb
        
        # This is the set of paths from the begining of the function where the attacker jumps during the external call
        # till the end of the start node where D/W dependency edges are observed
        self.set_root_true(matched_icfg_root_nodes)
        all_nodes = []
        all_nodes.extend(get_nodes_between_src_dest(matched_icfg_obj, matched_icfg_root_nodes, [start_node._origin_bb]))



        # This is set of paths from the start node till the end of the function
        successors_1 = list(matched_icfg_obj._function_icfg.successors(start_node._origin_bb))
        all_nodes.extend(get_nodes_between_src_dest(matched_icfg_obj, successors_1, matched_icfg_leaf_nodes))
        all_nodes = list(set(all_nodes))
        subgraph_2 = copy.deepcopy(matched_icfg_obj._function_icfg.subgraph(all_nodes))
        nx.set_node_attributes(subgraph_2, 'M', 'function_type')


        # This is done to ensure that we can further modify the graph, otherwise
        # it will throw the following error
        # networkx.exception.NetworkXError: Frozen graph can't be modified
        subgraph_1 = nx.MultiDiGraph(subgraph_1)
        subgraph_2 = nx.MultiDiGraph(subgraph_2)


        composed_graph_12, call_node_succs = self.connect_callnode(subgraph_1, leaf_node, subgraph_2)
        self.set_root_none(matched_icfg_root_nodes)


        # This is the set of paths starting after the external call till the end node where the other edge D/W of dependency
        # are observed
        primary_icfg_copy = primary_icfg_obj._function_icfg.copy(as_view=False)
        target_node = self.get_target_node(primary_icfg_obj, primary_icfg_copy, end_node._origin_bb)
        successors_2 = list(primary_icfg_obj._function_icfg.successors(call_node._origin_bb))

        all_succ_nodes = get_nodes_between_src_dest(primary_icfg_obj, successors_2, [end_node._origin_bb]) # self.get_nodes_from_paths(paths_4)
        if isinstance(target_node, list):
            all_succ_nodes.extend(target_node)

        else:
            if target_node is not None:
                if target_node not in all_succ_nodes:
                    all_succ_nodes.append(target_node)



        # This means call node is a part of the loop, hence we should flatten it completely
        if call_node._origin_bb in all_succ_nodes:
            all_succ_nodes = list(set(all_succ_nodes) - set([call_node._origin_bb]))
            predecessors = primary_icfg_copy.predecessors(call_node._origin_bb)
            primary_icfg_copy.remove_node(call_node._origin_bb)
            new_node = copy.deepcopy(call_node._origin_bb)

            for pred in predecessors:
                primary_icfg_copy.add_edge(pred, new_node)
            all_succ_nodes.append(new_node)

        #start_time = time.time()
        subgraph_3 = copy.deepcopy(primary_icfg_copy.subgraph(all_succ_nodes))
        #end_time = time.time()
        #print("Time diff %s" % (end_time - start_time))
        nx.set_node_attributes(subgraph_3, 'P', 'function_type')

        composed_graph_123 = self.connect_two_graphs(composed_graph_12, subgraph_3)
        #primary_icfg_obj.print_icfg_dot(self._graph_dir, primary_function, composed_graph_123, 'icfg_dummy')

        return composed_graph_123

    def connect_callnode(self, source_subgraph, leaf_node, target_subgraph):
        target_root_nodes = self.get_root_nodes(target_subgraph)
        target_leaf_nodes = self.get_leaf_nodes(target_subgraph)
        successors = list(source_subgraph.successors(leaf_node))

        if len(successors) != 0:
            source_subgraph.remove_edge(leaf_node, successors[0])
            source_subgraph.add_edge(leaf_node, target_root_nodes[0])

        else:
            source_subgraph.add_edge(leaf_node, target_root_nodes[0])

        composed_graph = nx.compose(source_subgraph, target_subgraph)

        return composed_graph, successors

    def set_root_true(self, nodes):
        for node in nodes:
            node._is_root = True
    

    def set_root_none(self, nodes):
        for node in nodes:
            node._is_root = None


    def detect_tod_read_write_dependencies(self, primary_function, primary_sdg, matched_function, matched_sdg, composed_sdg, attack_node, all_predecessors, count):
        ## We need to distinguish here between TOD Amount, TOD transfer, TOD Receiver
        variable_nodes = self.get_all_variable_nodes(composed_sdg)
        dependencies = {}
        edge_list = []
        tod_type=None

        dependencies['attack_type'] = 'TOD'
        dependencies['composed_functions'] = [primary_function.name, matched_function.name]
        dependencies['First_function'] = matched_function.name
        dependencies['Second_function'] = primary_function.name
        dependencies['dependencies'] = []

        for var_node in variable_nodes:
            successors = list(composed_sdg.successors(var_node))
            predecessors = list(composed_sdg.predecessors(var_node))

            for successor in successors:
                if successor not in all_predecessors:
                    continue

                if primary_sdg.has_node(successor):
                    edges_2 = (var_node, successor)

                    for predecessor in predecessors:
                        if matched_sdg.has_node(predecessor):
                            edges_1 = (predecessor, var_node)

                            if type(successor._instruction).__name__ == 'LowLevelCall' or type(successor._instruction).__name__ == 'HighLevelCall' or \
                                    type(successor._instruction).__name__ == 'Transfer' or type(successor._instruction).__name__ == 'Send':
                                    tod_type = 'tod_amount_or_receiver'
                            else:
                                tod_type = 'tod_transfer'

                            target_node = successor

                            if tod_type == 'tod_transfer':
                                tod_composed_graph = self.tod_output_paths(primary_function, target_node, matched_function, predecessor)
                                #tod_composed_graph = self.tod_output_paths_amount_or_receiver(primary_function, target_node, matched_function, predecessor)

                            else:
                                tod_composed_graph = self.tod_output_paths_amount_or_receiver(primary_function, target_node, matched_function, predecessor)

                            if tod_type == 'tod_transfer':
                                tuple_pair = (primary_function, tod_composed_graph)
                                #tuple_pair = (primary_function, matched_function, tod_composed_graph)
                            else:
                                tuple_pair = (primary_function, matched_function, tod_composed_graph)

                            self.generate_symex_json(var_node, tuple_pair, tod_type)
                            self.tod_count += 1

                            #if var_node not in self.tod_feasible_paths.keys():
                                #self.tod_feasible_paths[var_node] = []

                            #self.tod_feasible_paths[var_node].append((primary_function, tod_composed_graph))
                            matched_dependency = {}
                            matched_dependency['path'] = (str(predecessor), str(successor))
                            matched_dependency['state_variable'] = str(var_node)
                            dependencies['dependencies'].append(matched_dependency)
                            edges_1 = (str(edges_1[0]), str(edges_1[1]))
                            edges_2 = (str(edges_2[0]), str(edges_2[1]))
                            edge_list.append(edges_1)
                            edge_list.append(edges_2)

        if len(dependencies['dependencies']) != 0:
            self.global_detection[self._contract_name].append(dependencies)
            self._log.info("TOD dependency detected in file %s in contract %s in by composing functions %s and %s" % (self._contract_name, primary_function.contract.name, primary_function.name, matched_function.name))

            name = "_tod_dependency" + "_" + count
            if self._dump_graph == True:
                self.print_dependency(self._graph_dir, primary_function, matched_function, composed_sdg, edge_list, name)

    def tod_output_paths_amount_or_receiver(self, primary_function, dest_node, matched_function, start_node):
        primary_icfg_obj = self._icfg_objects[primary_function]
        primary_icfg_root_nodes = primary_icfg_obj._root_nodes
        primary_icfg_copy = primary_icfg_obj._function_icfg.copy(as_view=False)

        matched_icfg_obj = self._icfg_objects[matched_function]
        matched_icfg_root_nodes = matched_icfg_obj._root_nodes
        matched_icfg_copy = matched_icfg_obj._function_icfg.copy(as_view=False)

        # Get the subgraph from the root node till the exit node through start nodes
        start_node_successors = list(matched_icfg_copy.successors(start_node._origin_bb))
        self.set_root_true(matched_icfg_root_nodes)
        nodes_1 = get_nodes_between_src_dest(matched_icfg_obj, matched_icfg_root_nodes, start_node_successors)
        nodes_2 = get_nodes_between_src_dest(matched_icfg_obj, start_node_successors, matched_icfg_obj._leaf_nodes)
        all_pred_nodes = []
        all_pred_nodes.extend(nodes_1)
        all_pred_nodes.extend(nodes_2)
        all_pred_nodes = list(set(all_pred_nodes))
        subgraph_1 = copy.deepcopy(matched_icfg_copy.subgraph(all_pred_nodes))
        subgraph_1 = nx.MultiDiGraph(subgraph_1)
        nx.set_node_attributes(subgraph_1, 'M', 'function_type')
        self.set_root_none(matched_icfg_root_nodes)

        # This is the set of paths from the begining of the icfg till target node
        self.set_root_true(primary_icfg_root_nodes)
        all_pred_nodes = get_nodes_between_src_dest(primary_icfg_obj, primary_icfg_root_nodes, [dest_node._origin_bb])
        target_node = self.get_target_node(primary_icfg_obj, primary_icfg_copy, dest_node._origin_bb)

        if isinstance(target_node, list):
            all_pred_nodes.extend(target_node)

        else:
            if target_node is not None:
                if target_node not in all_pred_nodes:
                    all_pred_nodes.append(target_node)

        composed_graph = copy.deepcopy(primary_icfg_obj._function_icfg.subgraph(all_pred_nodes))
        composed_graph = nx.MultiDiGraph(composed_graph)
        nx.set_node_attributes(composed_graph, 'P', 'function_type')
        self.set_root_none(primary_icfg_root_nodes)

        matched_leaf_nodes = [x for x in subgraph_1.nodes if subgraph_1.out_degree(x) == 0]
        primary_root_nodes = [x for x in composed_graph.nodes if composed_graph.in_degree(x) == 0]
        composed_graph_1 = nx.compose(composed_graph, subgraph_1)
        add_edges_from_node(composed_graph_1, matched_leaf_nodes, primary_root_nodes)
        #primary_icfg_obj.print_icfg_dot(self._graph_dir, primary_function, composed_graph_1, 'icfg_dummy')
        return composed_graph_1

    def tod_output_paths(self, primary_function, dest_node, matched_function, start_node):
        primary_icfg_obj = self._icfg_objects[primary_function]
        primary_icfg_root_nodes = primary_icfg_obj._root_nodes
        primary_icfg_copy = primary_icfg_obj._function_icfg.copy(as_view=False)

        # This is the set of paths from the begining of the icfg till the external call
        self.set_root_true(primary_icfg_root_nodes)
        all_pred_nodes = get_nodes_between_src_dest(primary_icfg_obj, primary_icfg_root_nodes, [dest_node._origin_bb])
        target_node = self.get_target_node(primary_icfg_obj, primary_icfg_copy, dest_node._origin_bb)

        if isinstance(target_node, list):
            all_pred_nodes.extend(target_node)

        else:
            if target_node is not None:
                if target_node not in all_pred_nodes:
                    all_pred_nodes.append(target_node)

        composed_graph = copy.deepcopy(primary_icfg_obj._function_icfg.subgraph(all_pred_nodes))
        composed_graph = nx.MultiDiGraph(composed_graph)
        nx.set_node_attributes(composed_graph, 'P', 'function_type')
        self.set_root_none(primary_icfg_root_nodes)
        return composed_graph

    def detect_dao_read_write_dependencies(self, primary_function, primary_sdg, matched_function, matched_sdg, composed_sdg, call_node, all_predecessors, count):
        variable_nodes = self.get_all_variable_nodes(composed_sdg)
        dependencies = {}
        edge_list = []
        dependencies['attack_type'] = 'DAO'
        dependencies['composed_functions'] = [primary_function.name, matched_function.name]
        dependencies['from_function'] = matched_function.name
        dependencies['to_function'] = primary_function.name
        dependencies['dependencies'] = []

        for var_node in variable_nodes:
            successors = list(composed_sdg.successors(var_node))
            predecessors = list(composed_sdg.predecessors(var_node))

            for successor in successors:
                if successor not in all_predecessors:
                    if primary_sdg.has_node(successor):
                        bit_1 = 0
                    else:
                        bit_1 = 1
                    
                    for predecessor in predecessors:
                        if predecessor not in all_predecessors:
                            if primary_sdg.has_node(predecessor):
                                bit_2 = 0

                            else:
                                bit_2 = 1
                            
                            xored_res = bit_1 ^ bit_2

                            if xored_res:
                                edges_1 = (predecessor, var_node)
                                edges_2 = (var_node, successor)


                                
                                try:
                                    if matched_sdg.has_node(predecessor):
                                        start_node = predecessor
                                        end_node = successor
                                    
                                    if matched_sdg.has_node(successor):
                                        start_node = successor
                                        end_node = predecessor
                                    
                                    
                                    composed_sdg_copy =  self.get_composed_sdg_without_varnodes(composed_sdg)
                                    has_path = self.is_reachable_destination(start_node, end_node, var_node, composed_sdg_copy)
                                
                                except:
                                    traceback.print_exc()
                                    sys.exit(1)
                                
                                if has_path:
                                    composed_graph = self.output_paths(matched_function, start_node, primary_function, end_node, call_node, all_predecessors)
                                    tuple_pair = (primary_function, matched_function, composed_graph)
                                    self.generate_symex_json(var_node, tuple_pair, 'dao')
                                    self.dao_count += 1

                                    #if var_node not in self.dao_feasible_paths.keys():
                                        #self.dao_feasible_paths[var_node] = []
                                    
                                    #self.dao_feasible_paths[var_node].append((primary_function, matched_function, composed_graph))

                                    matched_dependency = {}
                                    matched_dependency['path'] = (str(start_node), str(end_node))
                                    #print(str(edges_1[1]))
                                    matched_dependency['state_variable'] = str(edges_1[1])
                                    dependencies['dependencies'].append(matched_dependency)
                                    edges_1 = (str(edges_1[0]), str(edges_1[1]))
                                    edges_2 = (str(edges_2[0]), str(edges_2[1]))
                                    edge_list.append(edges_1)
                                    edge_list.append(edges_2)

        if len(dependencies['dependencies']) != 0:
            self.global_detection[self._contract_name].append(dependencies)
            self._log.info("DAO dependency detected in file %s in contract %s in by composing functions %s and %s" % (self._contract_name, primary_function.contract.name, primary_function.name, matched_function.name))
            
            name = "_dependency" + "_" + count 
            if self._dump_graph == True:
                self.print_dependency(self._graph_dir, primary_function, matched_function, composed_sdg, edge_list, name)

    def generate_symex_json(self, varnode, tuple_pair, dao_or_tod):
        if dao_or_tod == 'tod_transfer':
            output_tod_paths(self._slither, self._contract_name, self._graph_dir, self._log, self.global_vars,
                             self.global_constant_vars, self.range_vars,
                             self.global_blocks, self.range_blocks, self.total_range_instructions, varnode, tuple_pair,
                             self.tod_count, self.tod_per_function_paths, self.tod_symex_paths)

        if dao_or_tod == 'tod_amount_or_receiver':
            output_tod_amount_or_receiver_paths(self._slither, self._contract_name, self._graph_dir, self._log, self.global_vars,
                             self.global_constant_vars, self.range_vars,
                             self.global_blocks, self.range_blocks, self.total_range_instructions, varnode, tuple_pair,
                             self.tod_count, self.tod_per_function_paths, self.tod_symex_paths, dao_or_tod)

        if dao_or_tod == 'dao':
            output_dao_paths(self._slither, self._contract_name, self._graph_dir, self._log, self.global_vars, self.global_constant_vars,
                             self.range_vars, self.global_blocks, self.range_blocks, self.total_range_instructions, varnode, tuple_pair, self.dao_count,
                             self.dao_per_function_paths, self.dao_symex_paths)


    def get_composed_sdg_without_varnodes(self, composed_sdg):
        composed_sdg_copy = composed_sdg.copy(as_view=False)
        
        for node in composed_sdg.nodes:
            if not isinstance(node, InstrBlock):
                composed_sdg_copy.remove_node(node)
        
        return composed_sdg_copy

    def print_dependency(self, graph_dir, function_1, function_2, graph, edge_list, name=None):
        
        content = ''
        colors = ['red']
        styles = ['dashed','dotted, bold']
        
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
            edge.set_label(edge.get('key'))
            src = edge.get_source()
            dest = edge.get_destination()
            pydot_edge = (src, dest)

            if key == 'D' or key == 'W':
                edge.set_style(styles[0])
            
            if pydot_edge in edge_list:
                edge.set_color(colors[0])
            
            edge.set_label(edge.get('key'))

        png_file_name = function_1.name + "_" + function_2.name + name + ".png"
        png_file_path = os.path.join(graph_dir, png_file_name)
        dot_graph.write_png(png_file_path)