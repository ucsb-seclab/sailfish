import json
import ujson
import slither
import copy
from config import *
from itertools import cycle, islice, dropwhile
import networkx as nx
import imp

CONSTANT_TYPES = ['int', 'str', 'Constant']
call_list = []


def get_imported_module(module_name):
    fp, pathname, description = imp.find_module(module_name)
    target_package = imp.load_module(module_name, fp, pathname, description)
    return target_package

def populate_dataset(contracts_list):
    list_path = os.path.join(SMART_ABSTRACT, "dataset", contracts_list)
    fp = open(list_path, "r")
    for line in fp:
        call_list.append(line.strip()) 

    fp.close()

def dump_json(result_dir, output_dict, name=None):
    outfile = os.path.join(result_dir, name)
    
    with open(outfile, 'w') as json_file:
        ujson.dump(output_dict, json_file, indent=4)

def dump_exceptions(exceptions):
    outfile = os.path.join(RESULT_DIR, "exceptions.json")
    with open(outfile, 'w') as json_file:
        ujson.dump(exceptions, json_file, indent=4)

def is_tainted_destination(call_dest, node, is_protected=False):
    taint_contract_context = slither.analyses.data_dependency.data_dependency.is_tainted(call_dest, node.function.contract, is_protected) 
    taint_function_context = slither.analyses.data_dependency.data_dependency.is_tainted(call_dest, node.function.contract, is_protected)

    if taint_contract_context or taint_function_context:
        return True
    else:
        return False

def read_text_file(file_path):
    file_content = None
    with open(file_path, 'r') as file:
        file_content = file.readlines()

    contracts_addr_to_name = {}
    for content in file_content:
        file_name = content.strip().split(",")[0]
        contracts_addr_to_name[content.strip().split(",")[1].lower()] = file_name
    return contracts_addr_to_name

def copy_graph(self, graph):
    target_graph = nx.MultiDiGraph()

    for edge in graph.edges:
        
        src_node = tuple(list(edge[0]))
        dest_node = tuple(list(edge[1]))
        target_graph.add_edge(src_node, dest_node, shape='box')
    
    return target_graph

def add_edge_from_nodes(graph, src_nodes, dest_node, key='N', ref='N'):
    for node in src_nodes:
        graph.add_edge(node, dest_node, key=key, ref=ref)

def add_edge_from_node(graph, src_node, dest_nodes, key='N', ref='N'):
    for node in dest_nodes:
        graph.add_edge(src_node, node, key=key, ref=ref)

def add_edges_from_node(graph, src_nodes, dest_nodes, key='N', ref='N'):
    for node in dest_nodes:
        for src_node in src_nodes:
            graph.add_edge(src_node, node, key=key, ref=ref)

def is_ir_call(ir):
    if type(ir).__name__ == 'LowLevelCall':
        return True
    elif type(ir).__name__ == 'HighLevelCall':
        return True
    elif type(ir).__name__ == 'InternalCall':
        return True
    elif type(ir).__name__ == 'LibraryCall':
        return True
    elif type(ir).__name__ == 'EventCall':
        return True
    elif type(ir).__name__ == 'Send':
        return True
    elif type(ir).__name__ == 'Transfer':
        return True
    else:
        return False

def is_ext_call(ir):
    if type(ir).__name__ == 'LowLevelCall':
        return True
    elif type(ir).__name__ == 'HighLevelCall':
        return True
    elif type(ir).__name__ == 'Send':
        return True
    elif type(ir).__name__ == 'Transfer':
        return True
    else:
        return False

def get_predecessors_copy(graph, node):
    predecessors = graph.predecessors(node)
    predecessors_copy = []
    
    for predecessor in predecessors:
        predecessors_copy.append(predecessor)
    
    return predecessors_copy

def get_successors_copy(graph, node):
    successors = graph.successors(node)
    successors_copy = []
    
    for successor in successors:
        successors_copy.append(successor)
    
    return successors_copy

def compute_ancesters_decendents(graph, leaf_nodes, root_nodes, all_predecessors, all_successors):
    scc_dict = {}
    scc_list = {}
    has_scc = False
    stronly_connected_components = nx.strongly_connected_components(graph)

    i = 0
    for component in stronly_connected_components:
        scc = list(component)
        if len(scc) > 1:
            has_scc = True
            basic_block = "SCC_" + str(i)
            i = i + 1

            if scc_list.get(basic_block) is None:
                scc_list[basic_block] = []

            scc_list[basic_block] = scc
            for node in scc:
                scc_dict[node] = basic_block

    if has_scc is True:
        converted_graph = nx.MultiDiGraph()
        for edge in graph.edges:
            src_node = edge[0]
            target_node = edge[1]

            if all_predecessors.get(src_node) is None:
                all_successors[src_node] = set()
                all_predecessors[src_node] = set()

            if all_predecessors.get(target_node) is None:
                all_successors[target_node] = set()
                all_predecessors[target_node] = set()

            if scc_dict.get(src_node) is None:
                new_src_node = src_node
            else:
                new_src_node = scc_dict[src_node]

            if scc_dict.get(target_node) is None:
                new_target_node = target_node
            else:
                new_target_node = scc_dict[target_node]

            if not converted_graph.has_node(new_src_node):
                converted_graph.add_node(new_src_node)

            if not converted_graph.has_node(new_target_node):
                converted_graph.add_node(new_target_node)

            if not nx.has_path(converted_graph, new_src_node, new_target_node):
                converted_graph.add_edge(new_src_node, new_target_node)

        leaf_nodes = [x for x in converted_graph.nodes if converted_graph.out_degree(x) == 0]
        all_preds = {}
        all_succs = {}
        get_all_predecessors_per_node(converted_graph, leaf_nodes, all_preds)
        get_all_successors_per_node(converted_graph, root_nodes, all_succs)

        for node in all_predecessors:
            if scc_dict.get(node) is None:
                for pred in all_preds[node]:
                    if scc_list.get(pred) is None:
                        all_predecessors[node].add(pred)
                    else:
                        all_predecessors[node].update(scc_list[pred])

                if len(all_succs) != 0:
                    for succ in all_succs[node]:
                        if scc_list.get(succ) is None:
                            all_successors[node].add(succ)
                        else:
                            all_successors[node].update(scc_list[succ])

            else:
                scc_bb = scc_dict[node]

                # Compute all predecessors
                for pred in all_preds[scc_bb]:
                    # if the predecessor does not belong to any scc, simply add it
                    if scc_list.get(pred) is None:
                        all_predecessors[node].add(pred)

                    # if the predecessor belongs to some scc, add all the nodes of scc into
                    # the predecessors
                    else:
                        all_predecessors[node].update(scc_list[pred])

                    # since the node itself belongs to some scc, and in an scc all the nodes
                    # are predecessor to each other, hence we should all of them into the list
                    all_predecessors[node].update(scc_list[scc_dict[node]])

                if len(all_succs) != 0:
                    # Compute all successors
                    for succ in all_succs[scc_bb]:
                        if scc_list.get(succ) is None:
                            all_successors[node].add(succ)

                        else:
                            all_successors[node].update(scc_list[succ])

                    all_successors[node].update(scc_list[scc_dict[node]])
    else:
        get_all_predecessors_per_node(graph, leaf_nodes, all_predecessors)
        get_all_successors_per_node(graph, root_nodes, all_successors)


def get_nodes_between_src_dest_old(graph, src_nodes, dest_nodes):
    all_nodes = []
    bfs_queue = []

    for src_node in src_nodes:
        for dest_node in dest_nodes:
            if nx.algorithms.has_path(graph, src_node, dest_node):
                bfs_queue.append(src_node)
                
                while len(bfs_queue) != 0:
                    node = bfs_queue.pop(0)
                    all_nodes.append(node)
                    successors = list(graph.successors(node))

                    for successor in successors:
                        if nx.algorithms.has_path(graph, successor, dest_node) and successor not in all_nodes:
                            bfs_queue.append(successor)

    return all_nodes


def get_all_successors_per_node(graph, nodes, all_successors):
    for node in nodes:
        successors = list(graph.successors(node))

        if all_successors.get(node) is None:
            all_successors[node] = set()
        
        for successor in successors:
            if all_successors.get(successor) is None:
                get_all_successors_per_node(graph, [successor], all_successors)
                all_successors[node].add(successor)
                all_successors[node] = all_successors[node].union(all_successors[successor])

            else:
                old_len = len(all_successors[node])
                all_successors[node].add(successor)
                new_len = len(all_successors[node])

                if old_len < new_len:
                    get_all_successors_per_node(graph, [successor], all_successors)
                all_successors[node] = all_successors[node].union(all_successors[successor])

def convert_set_to_list(source_dict):
    for key in source_dict.keys():
        source_dict[key] = list(source_dict[key])

def get_all_predecessors_per_node(graph, nodes, all_predecessors):
    for node in nodes:
        predecessors = list(graph.predecessors(node))

        if all_predecessors.get(node) is None:
            all_predecessors[node] = set()
        
        for predecessor in predecessors:
            if all_predecessors.get(predecessor) is None:
                get_all_predecessors_per_node(graph, [predecessor], all_predecessors)
                all_predecessors[node] = all_predecessors[node].union(all_predecessors[predecessor])
                all_predecessors[node].add(predecessor)
            
            else:
                prev_len = len(all_predecessors[node])
                all_predecessors[node].add(predecessor)
                current_len = len(all_predecessors[node])

                if prev_len < current_len:
                    get_all_predecessors_per_node(graph, [predecessor], all_predecessors)
                all_predecessors[node] = all_predecessors[node].union(all_predecessors[predecessor])


def get_nodes_between_src_dest(icfg_obj, src_nodes, dest_nodes):
    all_nodes = []
    
    for src_node in src_nodes:
        all_successors = copy.copy(icfg_obj._all_successors[src_node])
        all_successors.append(src_node)
        
        for dest_node in dest_nodes:
            all_predecessors = copy.copy(icfg_obj._all_predecessors[dest_node])
            all_predecessors.append(dest_node)
            common_nodes = list(set(all_predecessors).intersection(set(all_successors)))
            all_nodes.extend(common_nodes)

    all_nodes = list(set(all_nodes))
    return all_nodes

def get_source_variable(log, CFG, function, instruction, variable, values, visited_instrs):
    if type(variable).__name__ in CONSTANT_TYPES:
        if variable.value not in values:
            values.append(variable.value)

    elif variable in function.parameters:
        if 'U' not in values:
            values.append('U')

    else:
        cfg_obj = CFG.function_cfg[function]
        containing_bb = cfg_obj._ir_to_block[instruction]
        all_predecessor_bbs = cfg_obj._all_predecessors[containing_bb]


        if CFG.lvalue_vars.get(variable) is not None:
            for lvalue_instr in CFG.lvalue_vars[variable]:
                if lvalue_instr in visited_instrs:
                    continue

                else:
                    visited_instrs.append(lvalue_instr)

                if cfg_obj._ir_to_block.get(lvalue_instr) is not None:
                    lvalue_bb = cfg_obj._ir_to_block[lvalue_instr]

                    if lvalue_bb == containing_bb:
                        bb_instructions = lvalue_bb._instructions

                        if bb_instructions.index(lvalue_instr) < bb_instructions.index(instruction):
                            if type(lvalue_instr).__name__ == 'TypeConversion':
                                source_variable = lvalue_instr.read[0]
                                get_source_variable(log, CFG, function, lvalue_instr, source_variable, values, visited_instrs)

                            elif type(lvalue_instr).__name__ == 'Assignment':
                                source_variable = lvalue_instr.rvalue
                                get_source_variable(log, CFG, function, lvalue_instr, source_variable, values, visited_instrs)

                            else:
                                values.append('U')

                    elif lvalue_bb in all_predecessor_bbs:
                        if type(lvalue_instr).__name__ == 'TypeConversion':
                            source_variable = lvalue_instr.read[0]
                            get_source_variable(log, CFG, function, lvalue_instr, source_variable, values, visited_instrs)

                        elif type(lvalue_instr).__name__ == 'Assignment':
                            source_variable = lvalue_instr.rvalue
                            get_source_variable(log, CFG, function, lvalue_instr, source_variable, values, visited_instrs)

                        else:
                            if 'U' not in values:
                                values.append('U')

                    else:
                        if 'U' not in values:
                            values.append('U')
                else:
                    if type(lvalue_instr).__name__ == 'TypeConversion':
                        source_variable = lvalue_instr.read[0]
                        get_source_variable(log, CFG, lvalue_instr.function, lvalue_instr, source_variable, values, visited_instrs)

                    elif type(lvalue_instr).__name__ == 'Assignment':
                        source_variable = lvalue_instr.rvalue
                        get_source_variable(log, CFG, lvalue_instr.function, lvalue_instr, source_variable, values, visited_instrs)

                    else:
                        if 'U' not in values:
                            values.append('U')
        else:
            if 'U' not in values:
                values.append('U')