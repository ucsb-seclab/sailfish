import slither
import shutil
import os
import sys
import pydot
import glob
import traceback
from util import *
import networkx as nx
from collections import defaultdict
import matplotlib.pyplot as plt
from varnode import *
from collections import defaultdict
from slither.slithir.operations.assignment import Assignment
from slither.core.declarations.solidity_variables import SolidityFunction
from slither.core.declarations.function import Function
from slither.core.variables.variable import Variable
from slither.slithir.variables.temporary import TemporaryVariable
from slither.printers.call.call_graph import *
from slither.core.cfg.node import NodeType
from collections import OrderedDict
from basic_block import *
from slither.visitors.expression.export_values import ExportValues
from slither.slithir.operations.nop import Nop
import copy

class CFG:
    """
        Builds a per function cfg
    """
    function_cfg = {}
    lvalue_vars = {}
    member_ir_var_left = []
    refvar_names = {}
    contract_enums = {}
    

    def __init__(self, slither_obj, contract, function, graph_dir, dump_graph, log, icfg_objs=None):
        self._slither = slither_obj
        self._return_values = {}
        self._modifier_ir_calls = []
        self._icfg_objs = icfg_objs
        self._pre_dominators = {}
        self._conditional_pre_dominators = {}
        self._all_predecessors = {}
        self._ir_to_block = {}
        self._node_to_block_mapping = defaultdict(list)
        self._function_basic_blocks = None
        self._next_block_to_node = {}
        self._match_ENDIF_to_IF = {}
        self._root_basic_block = None
        self._dump_graph = dump_graph
        self._log = log
        self._modifier_call_bb = {}
        self._cfg = None
        self.state_vars_written = OrderedDict()
        self._ircall_to_bb = {}
        self._function = function
        self._contract = contract
        self.blockid = {}
        self._condition_to_sons = defaultdict(dict)
        self.leaf_nodes = []
        self._result_dir = graph_dir
        self._return_to_phi = {}
        self._phi_return_variable = None
        self._new_phi_return = []
        self._returns_irs = []
        self._return_summary = {}
        self._modifier_formal_params = {}
        self.build_cfg()

    
    def get_root_node(self):
        nodes = [x for x in self._cfg.nodes if self._cfg.in_degree(x) == 0]
        for node in nodes:
            basic_block = list(node)[0]
            if node.NodeType == 0x0:
                self._root_basic_block = node

    def get_leaf_basic_blocks(self):
        self.leaf_nodes = [x for x in self._cfg.nodes if self._cfg.out_degree(x)== 0 and self._cfg.in_degree(x) >= 1]

    # Builds CFG for every function in the contract
    def build_cfg(self):
        self.get_enums(self._function)
        self._cfg = nx.MultiDiGraph()
        self.generate_graph_nodes()
        self.connect_modifiers()
        self.get_pre_dominators()
        self.get_conditional_pre_dominators()
        self.generate_phi_var_for_return(self._function)
        get_all_predecessors_per_node(self._cfg, self.leaf_nodes, self._all_predecessors)
        compute_ancesters_decendents(self._cfg, self.leaf_nodes, [], self._all_predecessors, {})
        convert_set_to_list(self._all_predecessors)


        if self._dump_graph == True:
            self.print_cfg_dot(self._result_dir, self._function, self._cfg)

    def get_enums(self, function):
        for enum in function.contract.enums:
            CFG.contract_enums[enum] = enum.values

    def generate_graph_nodes(self):
        all_nodes = self._function.nodes

        if len(all_nodes) > 0:
            root_node = all_nodes[0]
            visited_nodes = self.get_basic_blocks(root_node, self._function, self._contract)
            self.connect_all_basic_blocks(self._contract, self._function, visited_nodes, self._cfg)

            # This stores the modifier IR calls into a list, which is later be needed in process_ir
            # during predecessor argument tracking
            remaining_nodes = [node for node in all_nodes if node not in visited_nodes]
            #remaining_nodes = list(set(all_nodes) - set(visited_nodes))
            father_nodes = []

            node_to_modifier = {}
            for rnode in remaining_nodes:
                if len(rnode.fathers) == 0:
                    father_nodes.append(rnode)

                for ir in rnode.irs:
                    if type(ir).__name__ == 'InternalCall' and ir.type_call == 'Modifier':
                        if self._modifier_formal_params.get(ir.function) == None:
                            self._modifier_ir_calls.append(ir)
                            node_to_modifier[ir.node] = ir

            for node in father_nodes:
                visited_nodes = self.get_basic_blocks(node, self._function, self._contract)
                modifier_graph = nx.MultiDiGraph()
                self.connect_all_basic_blocks(self._contract, self._function, visited_nodes, modifier_graph)

                for mod_node in node_to_modifier.keys():
                    if mod_node in visited_nodes:
                        self._modifier_formal_params[node_to_modifier[mod_node]] = modifier_graph


    def generate_phi_var_for_return(self, function):
        if len(function.nodes) != 0:
            phi_var = TemporaryVariable(function.nodes[0])
            self._phi_return_variable = phi_var
            return_values = []
            return_values.extend(function.returns)
            return_values.extend(function.return_values)
            return_values = list(set(return_values))
            effective_values = []
            
            for return_value in return_values:
                if return_value in CFG.lvalue_vars.keys():
                    effective_values.append(return_value)

            vars_used = []
            for return_ir in self._returns_irs:
                variable = return_ir.used[0]
                vars_used.append(variable)
                new_ir = Assignment(phi_var, variable, variable.type)
                self._return_to_phi[return_ir] = new_ir
            
            values_notin_rtnirs = []
            for effective_value in effective_values:
                if effective_value not in vars_used:
                    values_notin_rtnirs.append(effective_value)
            
            for value in values_notin_rtnirs:
                new_ir = Assignment(phi_var, value, value.type)
                self._new_phi_return.append(new_ir)

    def connect_constructor_calls(self, modifier_cfg):
        cfg_root = self._root_basic_block
        cfg_root_succ = list(self._cfg.successors(cfg_root))

        modifier_root = [x for x in modifier_cfg.nodes if modifier_cfg.in_degree(x) == 0][0]
        modifier_root_succ = list(modifier_cfg.successors(modifier_root))

        composed_cfg = nx.compose(self._cfg, modifier_cfg)
        composed_cfg.remove_node(cfg_root)
        composed_cfg.add_edge(cfg_root, modifier_root)

        if len(modifier_root_succ) > 0:
            if len(cfg_root_succ) > 0:
                composed_cfg.add_edge(modifier_root_succ[0], cfg_root_succ[0])

        else:
            if len(cfg_root_succ) > 0:
                composed_cfg.add_edge(modifier_root, cfg_root_succ[0])

        self._cfg = composed_cfg

    def connect_modifiers(self):
        modifier_ir_calls = list(self._modifier_formal_params.keys())
        to_inlines = None
        composed_cfg = nx.MultiDiGraph()
        end_if_stack = []

        for ir_call in modifier_ir_calls:
            modifier = ir_call.function

            if type(modifier).__name__ == 'FunctionSolc' and modifier.is_constructor is False:
                continue

            if modifier.is_constructor is True:
                modifier_cfg = self._modifier_formal_params[ir_call]
                self.connect_constructor_calls(modifier_cfg)
                continue

            modifier_obj = self._icfg_objs[modifier]
            modifier_svar_assignments = list(CFG.function_cfg[modifier].state_vars_written.keys())
            #self.state_vars_written.update(modifier_svar_assignments)
            
            modifier_cfg = copy.deepcopy(modifier_obj._function_icfg) #.copy(as_view=False) #self._icfgs[self._contract][modifier]
            #assert len(modifier_obj._root_nodes) == 1, "Error root nodes of the modifier is other than 1!"

            leaf_nodes = []
            for node in modifier_cfg.nodes:
                for instr in node._instructions:
                    self._ir_to_block[instr] = node
                    
                    if instr in modifier_svar_assignments:
                        self.state_vars_written[instr] = node
                
                if modifier_cfg.in_degree(node) == 0:
                    root_basic_block = node
                if modifier_cfg.out_degree(node) == 0:
                    leaf_nodes.append(node)

            # Get the cfg generated for modifier calls
            pre_modifier_cfg = self._modifier_formal_params[ir_call]

            # Get the exact basic block containing the modifier call
            modifier_call_bbs = self._modifier_call_bb[ir_call]

            # Get the root node for the cfg containing modifier call
            root_node = [x for x in pre_modifier_cfg.nodes if pre_modifier_cfg.in_degree(x) == 0][0]

            # Get the successor of root basic block for modifier cfg
            succ_node = list(modifier_cfg.successors(root_basic_block))[0]

            # Remove the edge between root basic block and its successor in the modifier cfg
            modifier_cfg.remove_edge(root_basic_block, succ_node)

            # Get a combined cfg using premodifier and modifier cfg
            modifier_cfg  = nx.compose(pre_modifier_cfg, modifier_cfg)

            # Add an edge from the root block of modifier cfg to the root of pre modifier cfg
            modifier_cfg.add_edge(root_basic_block, root_node)


            succs = []
            # Iterate over the call basic blocks of pre modifier cfgs and inline
            # the modifier cfg by replacing those basic blocks
            for call_bb in modifier_call_bbs:
                # Get the successor of the call basic block of pre modifier cfg
                succs = list(pre_modifier_cfg.successors(call_bb))

                # Remove edge between successor and call bb
                if len(succs) > 0:
                    modifier_cfg.remove_edge(call_bb, succs[0])

                # Extract the call instruction from call bb
                call_instr = call_bb._instructions[-1]
                del self._ircall_to_bb[call_instr]
                call_bb._instructions = call_bb._instructions[:-1]

                # If the modifier has parameters we need a call copy block
                if len(modifier.parameters) != 0:
                    call_copy_bb = modifier_obj.interprocedural_call_copy_block(call_instr, modifier)
                    call_bb._instructions.extend(call_copy_bb._instructions)
                    call_bb._ir_to_node_map.update(call_copy_bb._ir_to_node_map)

                    # Add an edge from the call basic block to the successor of root node of
                    # modifier cfg
                    modifier_cfg.add_edge(call_bb, succ_node)

                else:
                    if len(call_bb._instructions) > 0:
                        modifier_cfg.add_edge(call_bb, succ_node)
                    else:
                        modifier_cfg.add_edge(call_bb, succ_node)
                        modifier_cfg = nx.contracted_nodes(modifier_cfg, succ_node, call_bb, self_loops=False)

            if len(succs) > 0:
                for leaf_node in leaf_nodes:
                    modifier_cfg.add_edge(leaf_node, succs[0])

                leaf_nodes = succs

            composed_cfg = nx.compose(composed_cfg, modifier_cfg)
            bfs_queue = []
            visited_nodes = []
            bfs_queue.append(root_basic_block)
            basic_blocks = list(modifier_cfg.nodes)

            while len(bfs_queue) != 0:
                basic_block = bfs_queue.pop()
                visited_nodes.append(basic_block)
                
                next_blocks = list(modifier_cfg.successors(basic_block))
                for block in next_blocks:
                    if block not in visited_nodes:
                        bfs_queue.append(block)

                last_instruction = basic_block._instructions[-1]

                
                if type(last_instruction).__name__ == 'NodeSolc' and last_instruction.type == 0x0 and composed_cfg.in_degree(basic_block) == 0:
                    new_modifier = False
                    
                    if to_inlines != None:
                        for to_inline in to_inlines:
                            #if to_inline[1] != modifier:
                            new_modifier = True
                            succs = list(composed_cfg.successors(to_inline[0]))
                            preds = list(composed_cfg.predecessors(to_inline[0]))
                            composed_cfg.remove_node(to_inline[0])
                            #to_inline[0]._instructions = to_inline[0]._instructions[:-1]

                            root_node = basic_block
                            if len(to_inline[0]._instructions) != 0:
                                #to_inline[0]._instructions = copy.copy(to_inline[0]._instructions)
                                to_inline[0]._instructions[-1] = Nop()
                                add_edge_from_nodes(composed_cfg, [to_inline[0]], basic_block)
                                root_node = to_inline[0]

                            add_edge_from_nodes(composed_cfg, preds, root_node)
                            assert len(succs) <= 1, "Debug number of successors are more than 1!"

                            add_edges_from_node(composed_cfg, leaf_nodes, succs)
                            root_node._is_True = to_inline[0]._is_True
                        
                        if new_modifier == True:
                            to_inlines = None
                            new_modifier = False

                if type(last_instruction).__name__ == 'Condition':
                    end_if_stack.append(basic_block)
                    self._condition_to_sons[basic_block]['true'] = next_blocks[0]
                    self._condition_to_sons[basic_block]['false'] = next_blocks[1]
                
                if type(last_instruction).__name__ == 'NodeSolc' and (last_instruction.type == 0x50 or last_instruction.type == 0x52):
                    if self._match_ENDIF_to_IF.get(basic_block) == None:
                        assert len(end_if_stack) != 0, "Debug, this can not happen"
                        
                        if_basic_block = end_if_stack.pop()
                        self._match_ENDIF_to_IF[basic_block] = if_basic_block
                
                if type(last_instruction).__name__ == 'NodeSolc' and last_instruction.type == 0x40:
                    if to_inlines == None:
                        to_inlines = []
                    to_inlines.append((basic_block, modifier))

        if to_inlines != None:
            composed_cfg = nx.compose(self._cfg, composed_cfg)
            for to_inline in to_inlines:
                try:
                    
                    succs = list(composed_cfg.successors(to_inline[0]))
                    preds = list(composed_cfg.predecessors(to_inline[0]))
                    composed_cfg.remove_node(to_inline[0])
                    #to_inline[0]._instructions = to_inline[0]._instructions[:-1]

                    root_node = self._root_basic_block
                    if len(to_inline[0]._instructions) != 0:
                        #to_inline[0]._instructions = copy.copy(to_inline[0]._instructions)
                        to_inline[0]._instructions[-1] = Nop()
                        add_edge_from_nodes(composed_cfg, [to_inline[0]], self._root_basic_block)
                        root_node = to_inline[0]
                    
                    self.get_leaf_basic_blocks()
                    add_edge_from_nodes(composed_cfg, preds, root_node)
                    assert len(succs) <= 1, "Debug number of successors are more than 1!"
                    add_edges_from_node(composed_cfg, self.leaf_nodes, succs)
            
                except:
                    traceback.print_exc()
                    sys.exit(1)
            self._cfg = composed_cfg

        # The argument to the modifier is a return value of
        # another function call, then find out the function and
        # inline that before the modifier
        #self.args_function_with_modifiers(self._function)

    def args_function_with_modifiers(self, function):
        modifier_expressions = function._expression_modifiers
        modifiers_args_calls = {}

        for expr in modifier_expressions:
            arguments = ExportValues(expr).result()
            function_calls = []
            modifier = None

            for argument in arguments:
                if type(argument).__name__ == 'FunctionSolc':
                    function_calls.append(argument)

                if type(argument).__name__ == 'ModifierSolc':
                    modifier = argument

            if modifier != None:
                modifiers_args_calls[modifier] = function_calls

        for modifier in modifiers_args_calls.keys():
            functions = modifiers_args_calls[modifier]    
            
            for func in functions:
                ir_call = self._modifier_formal_params[func]
                root_block = [x for x in self._cfg.nodes if self._cfg.in_degree(x) == 0][0]
                self._root_basic_block = root_block
                basic_block = BasicBlock([ir_call])
                basic_block._ir_to_node_map[ir_call] = ir_call.node
                successors = list(self._cfg.successors(root_block))
                self._cfg.remove_node(root_block)
                self._cfg.add_edge(root_block, basic_block)
                self._cfg.add_edge(basic_block, successors[0])

    # Checks to see whether the ir is an conditional instruction
    def is_conditional_ir(self, ir):
        if type(ir).__name__ == 'Condition' :
            return True
        if type(ir).__name__ == 'SolidityCall' and (ir.function.name.startswith('require') or ir.function.name.startswith('assert')):
            return True

        return False
    
    # Conditional predominators are those which are necessary conditions that need to be satisfied
    # in order to reach this block, they are the strong constraints. i.e, if a conditional IF is present
    # in its predominators but the matching END-IF is not present, then that conditional IF is a strong contraint
    def get_conditional_pre_dominators(self):
        end_if_blocks = set(self._match_ENDIF_to_IF.keys())
        
        for block in self._pre_dominators.keys():
            self._conditional_pre_dominators[block] = [x for x in self._pre_dominators[block] if self.is_conditional_ir(x._instructions[-1])]
            common_end_ifs = end_if_blocks.intersection(set(self._pre_dominators[block]))
            matching_ifs = [self._match_ENDIF_to_IF[x] for x in common_end_ifs if len(list(self._cfg.predecessors(x))) == 2]
            self._conditional_pre_dominators[block] = list(set(self._conditional_pre_dominators[block]) - set(matching_ifs))



    # Get all predominators (by definition) of every basic block 
    def get_pre_dominators(self):
        root_nodes = []

        for x in self._cfg.nodes:
            if self._cfg.in_degree(x) == 0:
                root_nodes.append(x)
            
            if self._cfg.out_degree(x) == 0:
                self.leaf_nodes.append(x)

            self._pre_dominators[x] = []
            self._conditional_pre_dominators[x] = []

        bfs_stack = []
        visited_blocks = []

        for root_node in root_nodes:
            bfs_stack.append(root_node)

            while len(bfs_stack) != 0:
                node = bfs_stack.pop(0)
                
                successors = list(self._cfg.successors(node))
                if node not in visited_blocks:
                    visited_blocks.append(node)
                    
                    for successor in successors:
                        ir = successor._instructions[-1]
                        pre_dominator = node
                        
                        if type(ir).__name__ == 'NodeSolc':
                            
                            if ir.type == 0x50:
                                if self._match_ENDIF_to_IF.get(successor) != None:
                                    predecessors = list(self._cfg.predecessors(successor))
                                
                                    if len(predecessors) > 1:
                                        pre_dominator  = self._match_ENDIF_to_IF[successor]
                                    
                                    else:
                                        del self._match_ENDIF_to_IF[successor]
                            
                            if ir.type == 0x52:
                                if self._match_ENDIF_to_IF.get(successor) != None:
                                    predecessors = list(self._cfg.predecessors(successor))
                                
                                    if len(predecessors) > 1:
                                        pre_dominator  = self._match_ENDIF_to_IF[successor]
                                    
                                    else:
                                        del self._match_ENDIF_to_IF[successor]
                        
                        self._pre_dominators[successor].append(pre_dominator)
                        
                        if len(self._pre_dominators[pre_dominator]) != 0:                      
                            self._pre_dominators[successor].extend(self._pre_dominators[pre_dominator])
                            self._pre_dominators[successor] = list(set(self._pre_dominators[successor]))

                        bfs_stack.append(successor)
                else:
                    for successor in successors:
                        ir = successor._instructions[-1]
                        pre_dominator = node
                        
                        if type(ir).__name__ == 'NodeSolc':
                            if ir.type == 0x50:
                                predecessors = list(self._cfg.predecessors(successor))
                                if self._match_ENDIF_to_IF.get(successor) != None:
                                    if len(predecessors) > 1:
                                        pre_dominator  = self._match_ENDIF_to_IF[successor]
                                    
                                    else:
                                        del self._match_ENDIF_to_IF[successor]
                            
                            if ir.type == 0x52:
                                if self._match_ENDIF_to_IF.get(successor) != None:
                                    predecessors = list(self._cfg.predecessors(successor))
                                
                                    if len(predecessors) > 1:
                                        pre_dominator  = self._match_ENDIF_to_IF[successor]
                                    
                                    else:
                                        del self._match_ENDIF_to_IF[successor]

                        old_len = len(self._pre_dominators[successor])
                        
                        self._pre_dominators[successor].append(pre_dominator)
                        
                        if len(self._pre_dominators[pre_dominator]) != 0:                      
                            self._pre_dominators[successor].extend(self._pre_dominators[pre_dominator])
                            self._pre_dominators[successor] = list(set(self._pre_dominators[successor]))

                        new_len = len(self._pre_dominators[successor])
                        
                        if old_len < new_len and successor not in bfs_stack:
                             bfs_stack.append(successor)           


    # Check whether a particular instruction is a call instruction.
    # Returns True if Yes, False otherwise
    def is_ir_call(self, ir):
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

    def is_call_present(self, node):
        if node.internal_calls:
            return True
        elif node.solidity_calls:
            return True
        elif node.low_level_calls:
            return True
        elif node.high_level_calls:
            return True
        elif node.library_calls:
            return True
        else:
            return False
    
    def is_lvalue_storage(self, lvalue):
        if type(lvalue).__name__ == 'StateVariableSolc':
            return True
        
        else:
            if type(lvalue).__name__ == 'ReferenceVariable':
                origin_var = lvalue.points_to_origin
                
                if type(origin_var).__name__ == 'StateVariableSolc':
                    return True
                else:
                    return False
            else:
                return False


    def get_refvar_names(self, instr):
        str_instr = str(instr)
        instr_tokens = str_instr.split(" ")
        
        if instr_tokens[0].startswith('REF_') and instr_tokens[1] == '->':
            CFG.refvar_names[instr_tokens[0]] = instr_tokens[2]
    
    # This function adds the IR instructions to the current basic block.
    # If the instruction is a call instruction, it ends the basic block there
    # and start a new one for the next instruction to be added.
    # It inserts the newly created basic block after the previous one
    # in the list. It returns the running basic block.
    def node_to_irssa(self, function, node, basic_block):
        if node.type != 0x0:
            if node.irs:
                for ir in node.irs:
                    self.get_refvar_names(ir)
                    
                    if hasattr(ir, 'lvalue'):
                        if ir.lvalue not in CFG.lvalue_vars.keys():
                            CFG.lvalue_vars[ir.lvalue] = []
                        
                        if self.is_lvalue_storage(ir.lvalue):
                            self.state_vars_written[ir] = basic_block

                        if ir not in CFG.lvalue_vars[ir.lvalue]:
                            CFG.lvalue_vars[ir.lvalue].append(ir)

                        if type(ir).__name__ == 'Member' or type(ir).__name__ == 'Index':
                            if type(ir.variable_left).__name__ == 'ReferenceVariable':
                                CFG.member_ir_var_left.append(ir.variable_left)
                            
                            if type(ir.variable_right).__name__ == 'ReferenceVariable':
                                CFG.member_ir_var_left.append(ir.variable_right)

                    if type(ir).__name__ == 'Return':
                        self._returns_irs.append(ir)

                    # If the basic block is not added already to the node -> basic block list, add it now.
                    # This situation can arise if a new basic block is created in the previous iteration 
                    # and it has not been added to the node -> basic block list
                    if basic_block not in self._node_to_block_mapping[node]:
                        self._node_to_block_mapping[node].append(basic_block)
                    
                    # If the IR is a call instruction, end the running basic block and create a new one,
                    # add it to the function block list
                    if self.is_ir_call(ir) or type(ir).__name__ == 'NewContract':
                        if type(ir).__name__ == 'InternalCall' or type(ir).__name__ == 'HighLevelCall' or type(ir).__name__ == 'LibraryCall':
                            self._ircall_to_bb[ir] = basic_block
                            if type(ir.function).__name__ == 'ModifierSolc':
                                if self._modifier_call_bb.get(ir) == None:
                                    self._modifier_call_bb[ir] = []

                                self._modifier_call_bb[ir].append(basic_block)

                        basic_block._instructions.append(ir)
                        self._ir_to_block[ir] = basic_block
                        basic_block._ir_to_node_map[ir] = node
                        
                        if basic_block not in self._function_basic_blocks:
                            self._function_basic_blocks.append(basic_block)

                        # Get the index of the previous basic block  
                        next_index = self._function_basic_blocks.index(basic_block) + 1
                        basic_block = BasicBlock([])
                        # Adds the newly created basic block after the previous one
                        self._function_basic_blocks.insert(next_index, basic_block)
                    
                    else:
                        self._ir_to_block[ir] = basic_block
                        basic_block._instructions.append(ir)
                        basic_block._ir_to_node_map[ir] = node
            else:
                # If the node is a placeholder we should end the basic block
                # here and start a new from the next instruction because the execution
                # will start from the different function instead of executinf the immediate 
                # next instruction
                if node.type == 0x40:
                    basic_block._instructions.append(node)
                    self._ir_to_block[node] = basic_block
                    basic_block._ir_to_node_map[node] = node
                    
                    if basic_block not in self._function_basic_blocks:
                        self._function_basic_blocks.append(basic_block)

                    # Get the index of the previous basic block  
                    next_index = self._function_basic_blocks.index(basic_block) + 1
                    basic_block = BasicBlock([])
                    # Adds the newly created basic block after the previous one
                    self._function_basic_blocks.insert(next_index, basic_block)                    
                
                else:
                    self._ir_to_block[node] = basic_block
                    basic_block._instructions.append(node)
                    basic_block._ir_to_node_map[node] = node
        else:
            basic_block._instructions.append(node)
            basic_block._ir_to_node_map[node] = node
            self._ir_to_block[node] = basic_block
        
        return basic_block
    

    def remove_empty_basic_blocks(self):

        node_to_blocks = copy.copy(self._function_basic_blocks)

        for block in node_to_blocks:
            if len(block._instructions) == 0:
                self._function_basic_blocks.remove(block)
        
        '''
        for node, blocks in node_to_blocks.items():
            for block in blocks:
                if len(block._instructions) == 0:
                    self._node_to_block_mapping[node].remove(block)
                    self._function_basic_blocks.remove(block)
        '''
        

    # Adds an edge between two blocks
    def connect_blocks(self, graph, src_block, dest_block):
        graph.add_edge(src_block, dest_block)
    
    '''
        This function builds the CFG given all the basic blocks. It adds two types of edges:
            1. Adds an edge between every two basic blocks originating from the same node.
            2. Adds an edge from the last basic block of the father node to the first basic block of the son node
    '''
    def connect_all_basic_blocks(self, contract, function, cfg_nodes, cfg):

        for node in cfg_nodes:
            if self._node_to_block_mapping.get(node) != None:
            # Get the first basic block originating from a node
                start_block = self._node_to_block_mapping[node][0]
            
            else:
                continue
            
            # Get the id of the basic block
            block_id = self.blockid[start_block]
            #if block_id == 23:

            # Get all the basic blocks for that node
            blocks = self._node_to_block_mapping[node]

            for block in blocks:
                # Adds the basic block as a node in the graph if not added already
                if not cfg.has_node(block):
                    cfg.add_node(block, shape='box')

                # Adds an edge between every two basic blocks originating from the same node.
                if start_block != block:
                    self.connect_blocks(cfg, start_block, block)
                start_block = block
            
            # Adds an edge from the last basic block of the father node 
            # to the first basic block of the son node
            for son in node.sons:
                # If the function is revert then do not add any edge from that basic block, since revert() means 
                # that the transaction should be reverted and execution should not continue to the next basic block
                if type(self._node_to_block_mapping[node][-1]._instructions[-1]).__name__ == 'SolidityCall' \
                        and self._node_to_block_mapping[node][-1]._instructions[-1].function.name == 'revert()':
                    continue
                
                son_block = self._node_to_block_mapping[son][0]
                end_block = self._node_to_block_mapping[node][-1]

                index = self.blockid[end_block]

                if son_block != end_block:
                    self.connect_blocks(cfg, end_block, son_block)
    
    '''
        This function extracts the basic blocks from the function node and Slither IR.
        Every basic block should end after either a conditional statement or a call instruction.
        A Slither entry node should always be in a separate basic block.
    '''
    def get_basic_blocks(self, root_node, function, contract):
        self._function_basic_blocks = []
        if_stack = []
        node_stack = []
        if_loop_stack = []
        visited_nodes = []
        
        block = []
        basic_block = BasicBlock(block)
            #import ipdb; ipdb.set_trace()

        if len(function.nodes) > 0:
            node = root_node
            node_stack.append(node)
            
            while len(node_stack) > 0:
                node = node_stack.pop()
                visited_nodes.append(node)
                
                for son in node.sons:
                    if son not in visited_nodes:
                        node_stack.append(son)
            
            #for node in function.nodes:    

                #print(node)
                # If this is an entry node, start a fresh basic block
                # from the next node onwards
                if node.type == 0x0:
                    # Add the corresponding ir to the basic block
                    basic_block = self.node_to_irssa(function, node, basic_block)

                    self._root_basic_block = basic_block

                    # Add this block to the list of function basic blocks
                    self._function_basic_blocks.append(basic_block)

                    # Add this block to the list of all basic blocks for this node
                    self._node_to_block_mapping[node] = [basic_block]

                    # Mark this node as the running basic block for the node
                    self._next_block_to_node[node] = basic_block

                    # Start a fresh block for the next node
                    block = []
                    basic_block = BasicBlock(block)

                
                # If the node is conditional we know that the current basic block should end at this node
                # and a ne should start from the next node onwards
                elif node.is_conditional():
                    
                    # If the node is already present in the node to mapping list, this can happend due to sons
                    # block getting created a priori
                    if node in self._node_to_block_mapping.keys():
                        basic_block = self._next_block_to_node[node]
                    
                    # Otherwise add this block to the list of all basic blocks for this node
                    # Add the corresponding ir to the basic block
                    # Mark this node as the running basic block for the node
                    else:
                        self._node_to_block_mapping[node].append(basic_block)
                        basic_block = self.node_to_irssa(function, node, basic_block)
                        self._next_block_to_node[node] = basic_block
                    
                    # Add the block to the list of function basic blocks if not already added
                    if basic_block not in self._function_basic_blocks:
                        self._function_basic_blocks.append(basic_block)

                    
                    if node.type == 0x15:
                        if_loop_stack.append(basic_block)
                    
                    # This is to track IF-ENDIF
                    elif len(node.sons) > 1:
                        if_stack.append(basic_block)
                    
                    condition = "true"
                    parent_basic_block = basic_block

                    # For every sons of the node start a fresh basic block , add irs to the block,
                    # add that block to the list of basic blocks
                    # map the running basic block to that node
                    for son in node.sons:
                        # If son is alread added as a basic block, just retrieve it, it may happene
                        # if say require() is the last statement of if/else block
                        if son in self._node_to_block_mapping.keys():
                            basic_block = self._next_block_to_node[son]

                            # This is to track whether a path constraint need to true or false to reach the son block
                            if condition == "true":
                                basic_block._is_True = True
                                self._condition_to_sons[parent_basic_block][condition] = basic_block
                                condition = "false"
                            
                            else:
                                self._condition_to_sons[parent_basic_block][condition] = basic_block
                                basic_block._is_True = False
                        else:
                            block = []
                            basic_block = BasicBlock(block)
                            self._node_to_block_mapping[son].append(basic_block)
                            
                            # This is to track whether a path constraint need to true or false to reach the son block
                            if condition == "true":
                                basic_block._is_True = True
                                self._condition_to_sons[parent_basic_block][condition] = basic_block
                                condition = "false"
                            
                            else:
                                basic_block._is_True = False
                                self._condition_to_sons[parent_basic_block][condition] = basic_block
                            
                            basic_block = self.node_to_irssa(function, son, basic_block)
                            self._next_block_to_node[son] = basic_block

                        if basic_block not in self._function_basic_blocks:
                            self._function_basic_blocks.append(basic_block)
                        
                elif node.type == 0x51:
                    
                    if node in self._node_to_block_mapping.keys():
                        basic_block = self._next_block_to_node[node]
                    
                    else:
                        block = []
                        basic_block = BasicBlock(block)
                        self._node_to_block_mapping[node].append(basic_block)
                        basic_block = self.node_to_irssa(function, node, basic_block)
                        self._next_block_to_node[node] = basic_block
                    
                    if basic_block not in self._function_basic_blocks:
                        self._function_basic_blocks.append(basic_block)
                
                else:
                    # If it is a phi node , that is it has more than one father either start a fresh block or
                    # extract the block from the node to block mapping if present.
                    # add that block to the list of basic blocks
                    # map the running basic block to that node
                    if len(node.fathers) > 1 or (len(node.fathers) == 1 and node.type == 0x50) or (len(node.fathers) == 1 and node.type == 0x52):
                        
                        if node in self._node_to_block_mapping.keys():
                            basic_block = self._next_block_to_node[node]
                        
                        else:
                            block = []
                            basic_block = BasicBlock(block)
                            self._node_to_block_mapping[node].append(basic_block)
                            basic_block = self.node_to_irssa(function, node, basic_block)
                            self._next_block_to_node[node] = basic_block
                        
                        if basic_block not in self._function_basic_blocks:
                            self._function_basic_blocks.append(basic_block)
                        
                        if len(if_stack) != 0 and (node.type == 0x50):
                            if_basic_block = if_stack.pop()
                            self._match_ENDIF_to_IF[basic_block] = if_basic_block
                        
                        if node.type == 0x52:
                            if len(if_loop_stack) != 0:
                                if_loop = if_loop_stack.pop()
                                self._match_ENDIF_to_IF[basic_block] = if_loop
                        
                        # The node which has more than one father should be a phi node and
                        # next node should start from a seprate basic block
                        block = []
                        basic_block = BasicBlock(block)

                    # Otherwise add the instruction to the running basic block for that node 
                    # add that block to the list of basic blocks
                    # map the running basic block to that node
                    elif len(node.fathers) == 1:
                        
                        if node in self._node_to_block_mapping.keys():
                            basic_block = self._next_block_to_node[node]
                        else:
                            self._node_to_block_mapping[node].append(basic_block)
                            basic_block = self.node_to_irssa(function, node, basic_block)
                            self._next_block_to_node[node] = basic_block
                        
                        if len(if_stack) != 0 and (node.type == 0x50):
                            if_basic_block = if_stack.pop()
                            self._match_ENDIF_to_IF[basic_block] = if_basic_block 

                        if node.type == 0x52:
                            if len(if_loop_stack) != 0:
                                if_loop = if_loop_stack.pop()
                                self._match_ENDIF_to_IF[basic_block] = if_loop
                        
                        if basic_block not in self._function_basic_blocks:
                            self._function_basic_blocks.append(basic_block)
                    else:
                        # This is mainly for modifiers, which do not have any fathers, they should
                        # not be connected why any basic blocks
                        if len(basic_block._instructions) != 0:
                            block = []
                            basic_block = BasicBlock(block)
                        
                        if node in self._node_to_block_mapping.keys():
                            basic_block = self._next_block_to_node[node]
                        else:
                            self._node_to_block_mapping[node].append(basic_block)
                            basic_block = self.node_to_irssa(function, node, basic_block)
                            self._next_block_to_node[node] = basic_block
                            
                        if basic_block not in self._function_basic_blocks:
                            self._function_basic_blocks.append(basic_block)
                        

            self.remove_empty_basic_blocks()
            # Get the block id's from the function blocks
            for basic_block in self._function_basic_blocks:
                self.blockid[basic_block] = self._function_basic_blocks.index(basic_block)
            
        return visited_nodes
            
    # Print the CFG in a dot file
    def print_cfg_dot(self, graph_dir, function, graph):
        content = ''
        # Ref: https://stackoverflow.com/questions/33722809/nx-write-dot-generates-redundant-nodes-when-input-nodes-have-a-colon
        dot_file_name = function.name + "_cfg.dot"
        dot_file_path = os.path.join(graph_dir, dot_file_name)
        with open(dot_file_path, 'w', encoding='utf8') as fp:
            nx.drawing.nx_pydot.write_dot(graph, fp)

        (graph, ) = pydot.graph_from_dot_file(dot_file_path)

        png_file_name = function.name + "_cfg.png"
        png_file_path = os.path.join(graph_dir, png_file_name)
        graph.write_png(png_file_path)

