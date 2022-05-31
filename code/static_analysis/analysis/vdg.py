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


class VDG:
    varnode_list = []
    contract_vars = {}
    map_svars_to_struct = {}
    map_svars_to_sobj = {}

    def __init__(self, slither_obj, icfg_objects, sdg_objects, graph_dir):
        self.slither_obj = slither_obj
        self.icfg_objects = icfg_objects
        self.sdg_objects = sdg_objects
        self.graph_dir = graph_dir
        self.vdgs = {}
        self.instr_block_to_sdg_obj = {}
        self.varnode_to_instrnode = {}
        self.bblock_to_icfg = {}
        self.initialize()
        self.setup()
    
    def initialize(self):
        VDG.varnode_list = SDG.var_node_list
        VDG.contract_vars = SDG.contract_vars
        VDG.map_svars_to_struct = SDG.map_svars_to_struct
        VDG.map_svars_to_sobj = SDG.map_svars_to_sobj
    
    def setup(self):
        self.get_statevars_written()
        self.populate_vdg_with_statevar_writes()

    def get_all_variable_nodes(self, graph):
        varnodes = [x for x in graph.nodes if not isinstance(x, InstrBlock) and graph.in_degree(x) != 0]
        return varnodes

    def get_statevars_written(self):
        for function in self.sdg_objects.keys():
            sdg_obj = self.sdg_objects[function]
            icfg_obj = self.icfg_objects[function]
            sdg_graph = sdg_obj._sdg
            varnodes_written = self.get_all_variable_nodes(sdg_graph)

            for varnode in varnodes_written:
                if varnode not in self.varnode_to_instrnode.keys():
                    self.varnode_to_instrnode[varnode] = []
                
                predecessors = sdg_graph.predecessors(varnode)
                for predecessor in predecessors:
                    self.instr_block_to_sdg_obj[predecessor] = sdg_obj
                    self.varnode_to_instrnode[varnode].append(predecessor)

    def analyze_use_def(self, value, sdg_obj):
        icfg = sdg_obj._icfg
        
        for def_block in sdg_obj._vars_written[value]:
            for instruction in def_block._instructions: 
                if hasattr(instruction, 'lvalue') and instruction.lvalue == value:
                    pass

        '''
        for instruction in basic_block._instructions:
            if type(instruction).__name__ == 'Assignment':
                if instruction.lvalue == value:
                    return basic_block
    

        predecessors = icfg.predecessors(basic_block)
        for predecessor in predecessors:
            return self.analyze_use_def(value, predecessor, icfg)
        '''

    def process_instr_block(self, varnode, instr_block, value_graph):
        instruction = instr_block._instruction
        container_node = instr_block._instr_to_node
        assigned_value = instruction.rvalue
        
        if type(assigned_value).__name__ != 'Constant':
            is_tainted = slither.analyses.data_dependency.data_dependency.is_tainted(instruction.rvalue, container_node.function)
            
            if is_tainted:
                value_node = ValueNode(varnode, instr_block, "U", "=")
            else:
                value_node = ValueNode(varnode, instr_block, assigned_value, "=")
                
                '''
                if type(assigned_value).__name__ == 'LocalVariableSolc':
                    sdg_obj = self.instr_block_to_sdg_obj[instr_block]
                    self.analyze_use_def(assigned_value, sdg_obj)
                
                else:
                    print("Not Locals")
                '''
        else:
            value_node = ValueNode(varnode, instr_block, assigned_value, "=")
        
        value_graph.add_node(value_node)
    
    def populate_vdg_with_statevar_writes(self):
        for varnode in self.varnode_to_instrnode.keys():
            self.vdgs[varnode] = []
            
            instr_blocks = self.varnode_to_instrnode[varnode]
            for instr_block in instr_blocks:
                value_graph = nx.MultiDiGraph()
                self.process_instr_block(varnode, instr_block, value_graph)
                self.vdgs[varnode].append(value_graph)


