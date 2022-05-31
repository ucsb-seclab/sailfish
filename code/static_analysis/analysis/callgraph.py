import slither
import traceback
import networkx as nx
from collections import defaultdict
import matplotlib.pyplot as plt
from varnode import *
from collections import defaultdict
from slither.core.declarations.solidity_variables import SolidityFunction
from slither.core.declarations.function import Function
from slither.core.variables.variable import Variable
from callgraph_node import *
import os
import pydot

class CallGraph:
    """
        TOWRITE
    """
    def __init__(self, slither_obj, graph_dir, dump_graph, log):
        self._slither = slither_obj
        self._slither_special_functions = {}
        self._graph_dir = graph_dir
        self._callgraph = nx.MultiDiGraph()
        self._contract_callgraph = {}
        self._dump_graph = dump_graph
        self._log = log
        self._all_contracts = set()
        self._callgraph_nodes_mapping = {}
        self._nodelevels = {}
        self._edgelevels = {}
        self.setup()

    # It maps the graph with the function and the contract
    # Also it maps the nodes with their function
    def setup(self):
        for contract in self._slither.contracts:
            self._contract_callgraph[contract] = nx.MultiDiGraph()
            for function in contract.functions:
                self.add_function_node(self._contract_callgraph[contract], contract, function)
                self._all_contracts.add(function.contract)

        for contract in self._slither.contracts:
            for function in contract.functions:
                if function.name == 'slitherConstructorConstantVariables':
                    if self._slither_special_functions.get(function.name) is None:
                        self._slither_special_functions[function.name] = []
                    if function not in self._slither_special_functions[function.name]:
                        self._slither_special_functions[function.name].append(function)
                self._process_functions(contract, function)
        
        self.compose_all_callgraphs()

        if self._dump_graph == True:
            self.dump_graph(self._callgraph, self._graph_dir)
    
    # Outputs the callgraph
    def dump_graph(self, graph, graph_dir):
        pass
        #self.print_cfg_dot(graph, graph_dir)
    
    def compose_all_callgraphs(self):
        for contract in self._contract_callgraph.keys():
            contract_graph = self._contract_callgraph[contract]
            self._callgraph = nx.compose(self._callgraph, contract_graph)

    def _process_functions(self, contract, function):
        for internal_call in function.internal_calls:
            self._process_internal_call(function, internal_call)
        
        for external_call in function.high_level_calls:
            self._process_external_call(function, external_call)

    def _process_internal_call(self, function, internal_call):
        if isinstance(internal_call, (Function)):
            src_node_to_add = (function.contract, function)
            dest_node_to_add = (internal_call.contract, internal_call)
            
            if dest_node_to_add not in self._contract_callgraph[function.contract].nodes:
                self.add_function_node(self._contract_callgraph[internal_call.contract], internal_call.contract, internal_call)
            
            self.add_function_edge(self._contract_callgraph[function.contract], src_node_to_add, dest_node_to_add)

        '''
        elif isinstance(internal_call, (SolidityFunction)):
            src_node_to_add = (function.contract, function)
            dest_node_to_add = (internal_call, internal_call)
            self.add_solidity_function_node(self._contract_callgraph[function.contract], dest_node_to_add)
            self.add_solidity_function_edge(self._contract_callgraph[function.contract], src_node_to_add, dest_node_to_add)
        '''
            
    def _process_external_call(self, function, external_call):
        external_contract, external_function = external_call

        if external_contract not in self._all_contracts:
            return
        else:
            # add variable as node to respective contract
            if isinstance(external_function, (Variable)):
                self.add_function_node(self._contract_callgraph[external_contract], external_contract, external_function)
            
            if (external_contract, external_function) not in self._contract_callgraph[external_contract].nodes:
                self.add_function_node(self._contract_callgraph[external_contract], external_contract, external_function)
            
            self.add_function_edge(self._contract_callgraph[function.contract], (function.contract, function), (external_contract, external_function))

    def add_function_node(self, graph, contract, function):
        node_to_add = (contract, function)
        
        if node_to_add not in self._callgraph_nodes_mapping.keys():
            cg_node = CallGraphNode(contract, function)
            self._callgraph_nodes_mapping[node_to_add] = cg_node
        else:
            cg_node = self._callgraph_nodes_mapping[node_to_add]
        
        graph.add_node(cg_node)
    
    def add_solidity_function_node(self, graph, node_to_add):
        graph.add_node(node_to_add)
        self._nodelevels[node_to_add] = node_to_add[0].name + "." + node_to_add[1].name

    def add_solidity_function_edge(self, graph, src_node, dest_node):
        graph.add_edge(src_node, dest_node)
        self._edgelevels[(src_node, dest_node)] = ''

    def add_function_edge(self, graph, src_node, dest_node):
        if src_node not in self._callgraph_nodes_mapping.keys():
            cg_src_node = CallGraphNode(src_node[0], src_node[1])
            self._callgraph_nodes_mapping[src_node] = cg_src_node
        else:
            cg_src_node = self._callgraph_nodes_mapping[src_node]        
        
        if dest_node not in self._callgraph_nodes_mapping.keys():
            cg_dest_node = CallGraphNode(dest_node[0], dest_node[1])
            self._callgraph_nodes_mapping[dest_node] = cg_dest_node
        
        else:
            cg_dest_node = self._callgraph_nodes_mapping[dest_node]  
        
        graph.add_edge(cg_src_node, cg_dest_node)

    def print_cfg_dot(self, graph, graph_dir):
        content = ''
        
        #if function.name == 'mul':
        # Ref: https://stackoverflow.com/questions/33722809/nx-write-dot-generates-redundant-nodes-when-input-nodes-have-a-colon
        dot_file_name = "callgraph" + ".dot"
        dot_file_path = os.path.join(graph_dir, dot_file_name)
        with open(dot_file_path, 'w', encoding='utf8') as fp:
            nx.drawing.nx_pydot.write_dot(graph, fp)

        (graph, ) = pydot.graph_from_dot_file(dot_file_path)

        png_file_name = "callgraph"+ ".png"
        png_file_path = os.path.join(graph_dir, png_file_name)
        graph.write_png(png_file_path)
    
    '''
    def print_graph(self, graph_dir, contract, callgraph):
        #graph_dir = os.path.join(RESULT_DIR, os.path.splitext(file_name)[0])
        if len(callgraph.nodes()) > 0:
            nodelabels = {}
            edgelabels = {}
            for node in callgraph.nodes:
                nodelabels[node] = self._nodelevels[node]
            
            for edge in callgraph.edges:
                edgelabels[edge] = self._edgelevels[edge]
            plt.clf()
            nx.draw_networkx(callgraph, pos=nx.circular_layout(callgraph), node_size = 30, labels=nodelabels, hold=False, with_labels=True, font_size=4, font_color='k', font_family='sans-serif')
            nx.draw_networkx_edge_labels(callgraph, pos=nx.circular_layout(callgraph), edge_labels=edgelabels, font_color='red')
            f_path = graph_dir + "/" + contract.name + "_callgraph"+ ".svg"
            plt.savefig(f_path, format="svg")
    '''