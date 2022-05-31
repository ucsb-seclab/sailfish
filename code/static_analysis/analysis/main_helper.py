import os
import sys
sys.path.append("..")

import glob
import copy
import time
import datetime
import json
import logging
import traceback
import multiprocessing
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
from instr_block import *
from shutil import rmtree
from state_var import *
import networkx as nx
from vdg import *
import subprocess
from range_graph import *
from symex_helper import output_ir_paths_new
from slither.visitors.expression.export_values import ExportValues
from slither.slithir.operations.low_level_call import LowLevelCall
from slither.core.declarations.solidity_variables import SolidityVariableComposed


function_visibility = ['public', 'external']
SYMDIR = "../../symbolic_execution"
racket_executable = os.path.join(SYMDIR, "reentrancy")
racket_tod_executable = os.path.join(SYMDIR, "tod")
racket_tod_executable_comp = os.path.join(SYMDIR, "tod-complement")

## class states copy ##

class State:
    ## CFG
    function_cfg = {}
    lvalue_vars = {}
    member_ir_var_left = []
    refvar_names = {}
    contract_enums = {}


    ## ICFG

    icfg_generated = {}
    locals_to_declare = {}
    icfg_objects = {}
    function_to_graph = []
    uid = 1

    ## SDG

    sdg_generated = {}
    contract_vars = {}
    map_svars_to_struct = {}
    map_svars_to_sobj = {}
    var_node_list = []
    inter_contract_analysis = {}


def test_call_context(function_cfg, graph_dir):
    for contract in ICFG.icfg_generated.keys():
        for function in ICFG.icfg_generated[contract].keys():
            icfg = ICFG.icfg_generated[contract][function]
            if type(icfg).__name__ != 'NoneType':
                function_cfg.print_icfg_dot(graph_dir, function, icfg)

def invoke_symbolic_executor(graph_dir, file_path, results, range_type, solver_type, bug_type, functions_to_symexec):
    from_function = results['from_function']
    final_results = {}

    if functions_to_symexec.get(from_function) is not None:
        # print('INFO: %s has already been found SAT, returning early' % from_function)
        return

    try:
        if bug_type == 'dao_':
            proc = subprocess.Popen(
                ["timeout", "60s", racket_executable, "--file", file_path, '--attack', range_type, '--beb', '10',
                 '--solver', solver_type], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            output, error = proc.communicate()

            last_line = output.splitlines()[-1].decode()
            return_code = proc.returncode
            file_name = os.path.basename(file_path)
            final_results = {}
            final_results[file_name] = results
            final_results[file_name]['file_name'] = str(file_name)

            if return_code == 124:
                if 'result' not in final_results[file_name].keys():
                    final_results[file_name]['result'] = None

                final_results[file_name]['result'] = 'SAT'
                functions_to_symexec[from_function] = True

            if len(error.decode()) == 0:
                if last_line[-1] == 't':
                    if 'result' not in final_results[file_name].keys():
                        final_results[file_name]['result'] = None

                    final_results[file_name]['result'] = 'SAT'
                    functions_to_symexec[from_function] = True
                    # print('INFO: %s is SAT' % from_function)

                elif last_line[-1] == 'f':
                    if 'result' not in final_results[file_name].keys():
                        final_results[file_name]['result'] = None

                    final_results[file_name]['result'] = 'UNSAT'

                else:
                    ## If this is a solver error, we just assume it is SAT
                    if 'error' not in final_results[file_name].keys():
                        final_results[file_name]['error'] = None

                    '''
                    if 'result' not in final_results[file_name].keys():
                        final_results[file_name]['result'] = None

                    final_results[file_name]['result'] = 'SAT'
                    functions_to_symexec[from_function] = True
                    '''
                    final_results[file_name]['error'] = output.decode()
            else:
                ## If this is a solver error, we just assume it is SAT
                if 'error' not in final_results[file_name].keys():
                    final_results[file_name]['error'] = None

                '''
                if 'result' not in final_results[file_name].keys():
                    final_results[file_name]['result'] = None

                final_results[file_name]['result'] = 'SAT'
                functions_to_symexec[from_function] = True
                '''
                final_results[file_name]['error'] = error.decode()

            if 'execution_details' not in final_results[file_name].keys():
                final_results[file_name]['execution_details'] = None

            final_results[file_name]['execution_details'] = output.decode()

            file_base_name = os.path.basename(file_path)
            file_id = file_base_name.split(".")[0].split("_")[-1]
            outfile_name = bug_type + "sympath_" + str(file_id) + ".json"
            dump_json(graph_dir, final_results[file_name], outfile_name)

        if bug_type == 'tod_':
            file_name = os.path.basename(file_path)
            final_results = {}
            final_results[file_name] = results
            final_results[file_name]['file_name'] = str(file_name)

            tod_type = final_results[file_name]['bug_type']
            result_1 = None
            result_2 = None
            result_comp = None

            if tod_type == 'tod_transfer':
                ## First execution without value summary
                proc_1 = subprocess.Popen(
                    ["timeout", "60s", racket_tod_executable, "--file", file_path, '--attack', 'none', '--beb', '10',
                     '--solver', solver_type], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                output, error = proc_1.communicate()

                last_line = output.splitlines()[-1].decode()
                return_code = proc_1.returncode

                if return_code == 124:
                    result_1 = 'SAT'

                if len(error.decode()) == 0:
                    if last_line[-1] == 't':
                        result_1 = 'SAT'

                    elif last_line[-1] == 'f':
                        result_1 = 'UNSAT'

                    else:
                        if 'error' not in final_results[file_name].keys():
                            final_results[file_name]['error'] = None

                        final_results[file_name]['error'] = output.decode()

                else:
                    if 'error' not in final_results[file_name].keys():
                        final_results[file_name]['error'] = None

                    final_results[file_name]['error'] = error.decode().strip()

            ## Second execution with value summary
            if tod_type != 'tod_transfer' or (tod_type == 'tod_transfer' and result_1 != 'SAT'):
                proc_2 = subprocess.Popen(
                    ["timeout", "60s", racket_tod_executable, "--file", file_path, '--attack', range_type, '--beb',
                     '10',
                     '--solver', solver_type], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                output, error = proc_2.communicate()

                last_line = output.splitlines()[-1].decode()
                return_code = proc_2.returncode

                if return_code == 124:
                    result_2 = 'SAT'

                if len(error.decode()) == 0:
                    if last_line[-1] == 't':
                        result_2 = 'SAT'

                    elif last_line[-1] == 'f':
                        result_2 = 'UNSAT'

                    else:
                        if 'error' not in final_results[file_name].keys():
                            final_results[file_name]['error'] = None

                        final_results[file_name]['error'] = output.decode()
                else:
                    if 'error' not in final_results[file_name].keys():
                        final_results[file_name]['error'] = None

                    final_results[file_name]['error'] = error.decode()

            else:
                ## This is to check whether there exist any model for P which is UNSAT. So, we check whether there exist any model for P_complement which is SAT
                proc_2 = subprocess.Popen(
                    ["timeout", "60s", racket_tod_executable_comp, "--file", file_path, '--attack', range_type, '--beb',
                     '10',
                     '--solver', solver_type], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                output, error = proc_2.communicate()

                last_line = output.splitlines()[-1].decode()
                return_code = proc_2.returncode

                if return_code == 124:
                    result_2 = 'SAT'

                if len(error.decode()) == 0:
                    ## This is complement model, hence if P_complement is t actual P is UNSAT
                    ## If P_complement is f actual P is SAT
                    if last_line[-1] == 't':
                        result_2 = 'UNSAT'

                    elif last_line[-1] == 'f':
                        result_2 = 'SAT'

                    else:
                        if 'error' not in final_results[file_name].keys():
                            final_results[file_name]['error'] = None

                        final_results[file_name]['error'] = output.decode()
                else:
                    if 'error' not in final_results[file_name].keys():
                        final_results[file_name]['error'] = None

                    final_results[file_name]['error'] = error.decode()

            # print("%s in File %s " % (result_1, file_name))
            # print("%s in File %s " % (result_2, file_name))

            ## Handle tod transfer and tod amount or tod receiver separately
            if tod_type == 'tod_transfer':
                if result_1 is not None and result_2 is not None:
                    if 'result' not in final_results[file_name].keys():
                        final_results[file_name]['result'] = None

                    if result_1 == result_2:
                        final_results[file_name]['result'] = 'UNSAT'

                    else:
                        final_results[file_name]['result'] = 'SAT'
                        functions_to_symexec[from_function] = True
            else:
                if result_2 is not None:
                    if 'result' not in final_results[file_name].keys():
                        final_results[file_name]['result'] = None

                if result_2 == 'UNSAT':
                    final_results[file_name]['result'] = 'UNSAT'

                else:
                    final_results[file_name]['result'] = 'SAT'
                    functions_to_symexec[from_function] = True

            '''
            ## If one of the result_1 and result_2 is null, it means that the solver errored out
            ## so, we just set it as SAT instead.
            else:
                if 'result' not in final_results[file_name].keys():
                    final_results[file_name]['result'] = None

                final_results[file_name]['result'] = 'SAT'
                functions_to_symexec[from_function] = True
            '''

            if 'execution_details' not in final_results[file_name].keys():
                final_results[file_name]['execution_details'] = None

            final_results[file_name]['execution_details'] = output.decode()
            file_base_name = os.path.basename(file_path)
            file_id = file_base_name.split(".")[0].split("_")[-1]
            outfile_name = bug_type + "sympath_" + str(file_id) + ".json"
            dump_json(graph_dir, final_results[file_name], outfile_name)

    except:
        traceback.print_exc()
        sys.exit(1)

    return final_results


def find_feasible_paths(graph_dir, dao_symex_paths, dao_per_function_paths, tod_symex_paths, tod_per_function_paths,
                        range_type, solver_type, default=None):
    # : need to add the path probably using some enviornment variable

    outfiles_pattern = os.path.join(graph_dir, "dao_symex_path_*.json")
    output = {}
    all_path_files = glob.glob(outfiles_pattern)

    # This is for DAO
    if len(all_path_files) != 0:
        functions_to_symexec = multiprocessing.Manager().dict()
        final_results = dict()
        final_results.update(dao_symex_paths)
        arguments = list(map(lambda e: (
        graph_dir, e, final_results[os.path.basename(e)], range_type, solver_type, 'dao_', functions_to_symexec),
                             all_path_files))

        if default is None:
            concurrency = int(multiprocessing.cpu_count() / 2)
            concurrency = 4
            with multiprocessing.Pool(concurrency) as pool:
                res = pool.starmap(invoke_symbolic_executor, arguments)
                # output.update(res)

            pool.join()
            output['warning_details'] = {}
            output['warning_details'] = res
        else:
            final_results['init-test-0.json'] = {}
            # final_results['symex_path_1.json'] = {}
            file_path = os.path.join(SYMDIR, 'tests/example-test-1.json')
            res = invoke_symbolic_executor(graph_dir, file_path, final_results, range_type)
            output['warning_details'] = [res]

    ### This is for TOD
    outfiles_pattern = os.path.join(graph_dir, "tod_symex_path_*.json")
    output = {}
    all_path_files = glob.glob(outfiles_pattern)
    if len(all_path_files) != 0:
        functions_to_symexec = multiprocessing.Manager().dict()
        final_results = dict()
        final_results.update(tod_symex_paths)
        arguments = list(map(lambda e: (
        graph_dir, e, final_results[os.path.basename(e)], range_type, solver_type, 'tod_', functions_to_symexec),
                             all_path_files))

        if default is None:
            concurrency = int(multiprocessing.cpu_count() / 2)
            concurrency = 8
            with multiprocessing.Pool(concurrency) as pool:
                res = pool.starmap(invoke_symbolic_executor, arguments)
                # output.update(res)

            pool.join()
            output['warning_details'] = {}
            output['warning_details'] = res
        else:
            final_results['init-test-0.json'] = {}
            # final_results['symex_path_1.json'] = {}
            file_path = os.path.join(SYMDIR, 'tests/example-test-1.json')
            res = invoke_symbolic_executor(graph_dir, file_path, final_results, range_type)
            output['warning_details'] = [res]


def generate_icfg(slither_obj, callgraph, graph_dir, dump_graph, log):
    icfg_objects = {}
    # Initialize icfg
    ICFG.initialize_icfg(slither_obj.contracts)

    for contract in slither_obj.contracts:
        for modifier in contract.modifiers:
            info('Interprocedural CFG generation started for modifier %s' % modifier.name)
            modifier_cfg = ICFG(slither_obj, contract, modifier, callgraph, graph_dir, dump_graph, log)
            info('Interprocedural CFG generated for modifer %s' % modifier.name)
            icfg_objects[modifier] = modifier_cfg

    for contract in slither_obj.contracts:
        for function in contract.functions:
            cfg_obj = CFG(slither_obj, contract, function, graph_dir, dump_graph, log, ICFG.icfg_objects)
            CFG.function_cfg[function] = cfg_obj

    # This builds the ICFG for every public or external functions in the
    # contract
    for contract in slither_obj.contracts:
        for function in contract.functions:

            if function.visibility in function_visibility:
                # if function.name == 'withdrawEarnings':
                # function_icfg = ICFG(slither_obj, contract, function, callgraph, graph_dir)
                info('Interprocedural CFG generation started for %s' % function.name)
                function_cfg = ICFG(slither_obj, contract, function, callgraph, graph_dir, dump_graph, log)
                info('Interprocedural CFG generated for %s' % function.name)
                icfg_objects[function] = function_cfg

    return ICFG.icfg_generated, icfg_objects


def is_owner_only_modifier(modifier, sdg_objects):
    if sdg_objects[modifier]._is_msg_sender is True:
        return True

    else:
        return False


def get_owner_only_functions(slither_obj, owner_only_modifiers, call_heuristic):
    owner_only_functions = []
    for contract in slither_obj.contracts:
        for function in contract.functions:
            if is_owner_only_function(function, contract, call_heuristic, owner_only_modifiers) is True:
                owner_only_functions.append(function)

    return owner_only_functions


def is_owner_only_function(function, contract, call_heuristic, owner_only_modifers):
    if function.name == 'slitherConstructorVariables' or function.name == 'slitherConstructorConstantVariables' \
            or function.is_constructor is True:
        return True

    else:
        # If call heuristic is on, we apply the msg.sender rule for conditional statements in modifiers
        if call_heuristic:
            modifiers = function.modifiers
            common_modifiers = list(set(modifiers).intersection(set(owner_only_modifers)))
            if len(common_modifiers) != 0:
                return True

            else:
                return False
        else:
            return False


def get_state_var_obj(state_variables):
    map_svar_to_sobj = {}

    for state_var in state_variables:
        s_obj = StateVar(state_var)
        map_svar_to_sobj[state_var] = s_obj

    return map_svar_to_sobj

'''
 --------------------------------------------------
 Start of inter-contract analysis related functions
 --------------------------------------------------
'''

def check_for_tainted_call(sdg_objects, generated_sdg, owner_only_modifiers, call_instr, destination_function):
    for function in sdg_objects.keys():
        if destination_function.name == function.name and sdg_objects[function]._is_ext_call is True \
            and len(call_instr.arguments) == len(function.parameters):
            for actual_parameter in call_instr.arguments:
                position = call_instr.arguments.index(actual_parameter)
                if not slither.analyses.data_dependency.data_dependency.is_tainted(actual_parameter, call_instr.node.function):
                    function.slither.context['DATA_DEPENDENCY_INPUT'].remove(function.parameters[position])

            for ext_call in sdg_objects[function]._ext_calls.keys():
                if slither.analyses.data_dependency.data_dependency.is_tainted(ext_call.destination, function.contract):
                    return True
    return False

def do_inter_contract_analysis(contract_path, call_instr, destination_function, log, result_dir):
    #contract_path = "/home/cinderella/research/creame_finance_incident/modified_cream.sol"
    contract_name = os.path.basename(contract_path)

    if SDG.inter_contract_analysis.get(contract_name) is None:
        SDG.inter_contract_analysis[contract_name] = True
    else:
        return

    _, solc_path = get_solc_path(contract_path, log)

    # Initialize Slither
    slither_obj = Slither(contract_path, solc=solc_path)

    # Build interprocedural cfg for all public functions
    log.info('Interprocedural CFG generation started!')
    generated_icfg, icfg_objects = generate_icfg(slither_obj, None, result_dir, False, log)
    log.info('Interprocedural CFG generation finished!')

    # Build storage dependency graph
    log.info('Storage dependency graph generation started!')
    generated_sdg, sdg_objects, owner_only_modifiers = generate_sdg(slither_obj, generated_icfg, result_dir, False, log)
    log.info('Storage dependency graph generation finished!')
    is_ext_tainted = check_for_tainted_call(sdg_objects, generated_sdg, owner_only_modifiers, call_instr, destination_function)
    return is_ext_tainted


def process_inter_contract_calls_if_exists(sdg_objects, contract_mapping_path, contract_dir, graph_dir, log):
    contracts_addr_to_names = read_text_file(contract_mapping_path)
    for function in sdg_objects.keys():
        for inter_contract_call in sdg_objects[function].inter_contract_calls:
            contract_address_in_hex = hex(inter_contract_call[0])
            if contracts_addr_to_names.get(contract_address_in_hex) is not None:
                contract_path = os.path.join(contract_dir, contracts_addr_to_names[contract_address_in_hex])
                is_inter_contract_tainted = do_inter_contract_analysis(contract_path, inter_contract_call[1], inter_contract_call[1].function, log, graph_dir)

                if is_inter_contract_tainted:
                    sdg_objects[function]._is_ext_call = True
                    sdg_objects[function]._ext_calls[inter_contract_call[1]] = True

def store_static_state():
    ## CFG
    State.function_cfg = copy.copy(CFG.function_cfg)
    State.lvalue_vars = copy.copy(CFG.lvalue_vars)
    State.member_ir_var_left = copy.copy(CFG.member_ir_var_left)
    State.refvar_names = copy.copy(CFG.refvar_names)
    State.contract_enums = copy.copy(CFG.contract_enums)

    ## ICFG

    State.icfg_generated = copy.copy(ICFG.icfg_generated)
    State.locals_to_declare = copy.copy(ICFG.locals_to_declare)
    State.icfg_objects = copy.copy(ICFG.icfg_objects)
    State.function_to_graph = copy.copy(ICFG.function_to_graph)
    State.uid = ICFG.uid

    ## SDG
    State.sdg_generated = copy.copy(SDG.sdg_generated)
    State.contract_vars = copy.copy(SDG.contract_vars)
    State.map_svars_to_struct = copy.copy(SDG.map_svars_to_struct)
    State.map_svars_to_sobj = copy.copy(SDG.map_svars_to_sobj)
    State.var_node_list = copy.copy(SDG.var_node_list)
    State.inter_contract_analysis = copy.copy(SDG.inter_contract_analysis)

def load_static_state():
    ## CFG
    CFG.function_cfg = copy.copy(State.function_cfg)
    CFG.lvalue_vars = copy.copy(State.lvalue_vars)
    CFG.member_ir_var_left = copy.copy(State.member_ir_var_left)
    CFG.refvar_names = copy.copy(State.refvar_names)
    CFG.contract_enums = copy.copy(State.contract_enums)

    ## ICFG

    ICFG.icfg_generated = copy.copy(State.icfg_generated)
    ICFG.locals_to_declare = copy.copy(State.locals_to_declare)
    ICFG.icfg_objects = copy.copy(State.icfg_objects)
    ICFG.function_to_graph = copy.copy(State.function_to_graph)
    ICFG.uid = State.uid

    ## SDG
    SDG.sdg_generated = copy.copy(State.sdg_generated)
    SDG.contract_vars = copy.copy(State.contract_vars)
    SDG.map_svars_to_struct = copy.copy(State.map_svars_to_struct)
    SDG.map_svars_to_sobj = copy.copy(State.map_svars_to_sobj)
    SDG.var_node_list = copy.copy(State.var_node_list)
    SDG.inter_contract_analysis = copy.copy(State.inter_contract_analysis)

'''
 ------------------------------------------------
 End of inter-contract analysis related functions
 ------------------------------------------------
'''

def generate_sdg(slither_obj, generated_icfg, graph_dir, dump_graph, log):
    contract_vars = {}
    sdg_objects = {}
    map_svars_to_sobj = {}
    map_svars_to_struct = {}
    owner_only_modifiers = []

    for contract in slither_obj.contracts:
        contract_vars[contract] = contract.state_variables
        map_svars_to_struct.update(get_structure_vars(contract_vars[contract]))

        for state_var in contract_vars[contract]:
            if state_var not in map_svars_to_sobj.keys():
                s_obj = StateVar(state_var)
                map_svars_to_sobj[state_var] = s_obj

    SDG.initialize_sdg(contract_vars, map_svars_to_struct, map_svars_to_sobj)

    for contract in slither_obj.contracts:
        for function in contract.functions:
            if function.visibility in function_visibility:
                # if function.name == 'withdrawEarnings':
                info('SDG generation started for %s' % function.name)
                function_sdg = SDG(slither_obj, contract, function, generated_icfg[contract][function], graph_dir,
                                   dump_graph, log)
                info('SDG generated for %s' % function.name)
                sdg_objects[function] = function_sdg

        for modifier in contract.modifiers:
            info('SDG generation started for modifier %s' % modifier.name)
            modifier_sdg = SDG(slither_obj, contract, modifier, generated_icfg[contract][modifier], graph_dir,
                               dump_graph, log)
            info('SDG generated for modifier %s' % modifier.name)
            sdg_objects[modifier] = modifier_sdg

            if modifier_sdg._is_msg_sender is True:
                owner_only_modifiers.append(modifier)

    return SDG.sdg_generated, sdg_objects, owner_only_modifiers


def generate_vdg(slither_obj, icfg_objects, sdg_objects, graph_dir):
    vdg_objects = {}
    function_vdgs = VDG(slither_obj, icfg_objects, sdg_objects, graph_dir)


def get_common_variable_functions(sdg_objects, composed_obj, graph_dir, contract_path, percentage):
    matching_func_info = defaultdict(dict)
    external_func = []
    total_functions = 0
    matching_sdgs = defaultdict(list)
    matching_functions = {}

    with open(contract_path, 'r') as fp:
        lines = len(fp.readlines())

    for function in sdg_objects.keys():
        sdg_obj = sdg_objects[function]

        if sdg_obj._is_ext_call == True:
            external_func.append(sdg_obj)

    for ext_sdg in external_func:
        temp_sdgs = composed_obj.get_matching_sdgs(ext_sdg)
        all_sdgs = []
        all_sdgs.extend(temp_sdgs)

        while len(temp_sdgs) != 0:
            target_sdg = temp_sdgs.pop()
            results = composed_obj.get_matching_sdgs(target_sdg)

            for sdg in results:
                if sdg not in all_sdgs:
                    all_sdgs.append(sdg)
                    temp_sdgs.append(sdg)

        all_sdgs = list(set(all_sdgs))
        matching_sdgs[ext_sdg] = all_sdgs

    for sdg, m_sdgs in matching_sdgs.items():
        contract_functions_info = {}
        target_functions = {}
        matching_functions = {}
        target_functions['Functions name'] = []

        for target in m_sdgs:
            target_functions['Functions name'].append(target._function.name)
            function_modifiers = target._function.modifiers

            for modifier in function_modifiers:
                if modifier.name not in target_functions['Functions name']:
                    target_functions['Functions name'].append(modifier.name)

        matching_functions[sdg._function.name] = []
        count_info = {}
        count_info['Total common variable functions'] = len(target_functions['Functions name'])
        matching_functions[sdg._function.name].append(count_info)
        matching_functions[sdg._function.name].append(target_functions)

        contract = sdg._function.contract

        total_functions = 0
        for func in contract.functions:
            if func.visibility in function_visibility:
                total_functions += 1

        contract_functions_info['Total public functions'] = total_functions
        contract_functions_info['LoC'] = lines
        contract_functions_info['Percentage checks'] = percentage

        if contract.name not in matching_func_info.keys():
            matching_func_info[contract.name] = contract_functions_info
            matching_func_info[contract.name]['Matching function info'] = []

        matching_func_info[contract.name]['Matching function info'].append(matching_functions)
    json_dir = os.path.join(graph_dir, "matching_functions.json")
    with open(json_dir, 'w') as jsonf:
        json.dump(matching_func_info, jsonf, indent=4)


def get_dependent_state_vars(graph):
    state_vars = []
    for node in graph.nodes:
        if not isinstance(node, InstrBlock):
            state_vars.append(node)

    return state_vars


def get_blacklisted_modifiers(slither_obj, sdg_objects, vrg, owner_only_functions, owner_only_modifiers, graph_dir):
    modifiers = []
    owner_only_state_vars = []
    owner_only_modifiers = []

    for state_var in vrg._state_var_written.keys():
        functions = vrg._state_var_written[state_var]
        flag = True
        for function in functions:
            if function not in owner_only_functions:
                flag = False
                break
        if flag:
            owner_only_state_vars.append(state_var)

    owner_only = True
    for contract in slither_obj.contracts:
        for modifier in contract.modifiers:
            sdg_obj = sdg_objects[modifier]
            sdg_graph = sdg_obj._sdg
            state_vars = get_dependent_state_vars(sdg_graph)
            for state_var in state_vars:
                if state_var in owner_only_state_vars:
                    modifiers.append(modifier)
                    break

    return owner_only_modifiers, owner_only_state_vars


def generate_composed_sdg(slither_obj, generated_sdg, vrg, graph_dir, sdg_objects, call_heuristic, owner_only_modifiers,
                          target_contracts, contract_path, dump_graph, dao, tod, log):
    sdg_with_ext_call = {}
    sdg_with_ether_sending_function = {}
    composed_sdg = {}

    owner_only_functions = get_owner_only_functions(slither_obj, owner_only_modifiers, call_heuristic)
    blacklisted_modifiers, owner_only_state_vars = get_blacklisted_modifiers(slither_obj, sdg_objects, vrg,
                                                                             owner_only_functions, owner_only_modifiers,
                                                                             graph_dir)
    functions_to_be_analyzed = {}

    for function in sdg_objects.keys():
        if type(function).__name__ == 'ModifierSolc':
            continue

        sdg_obj = sdg_objects[function]
        if function not in owner_only_functions and function.contract in target_contracts \
                and function.is_constructor is False:

            functions_to_be_analyzed[function] = sdg_obj

            if len(sdg_obj._is_ether_sending_functions.keys()) > 0:
                sdg_with_ether_sending_function[function] = sdg_obj

            if sdg_obj._is_ext_call == True:
                analyze_external_call(sdg_obj, vrg, function, owner_only_state_vars, owner_only_functions)
                sdg_with_ext_call[function] = sdg_obj

    for function in functions_to_be_analyzed.keys():
        key = function
        is_ext_call = False
        is_ether_sending = False

        if sdg_with_ext_call.get(function) is not None:
            is_ext_call = True

        if sdg_with_ether_sending_function.get(function) is not None:
            is_ether_sending = True

        if is_ether_sending is True or is_ext_call is True:
            composed_sdg[function] = Compose(slither_obj, functions_to_be_analyzed[function], sdg_objects, is_ext_call,
                                             is_ether_sending, owner_only_functions, target_contracts, graph_dir,
                                             dump_graph, dao, tod, log)

    return composed_sdg


def analyze_external_call(sdg_obj, vrg_obj, function, owner_only_vars, blacklisted_functions):
    copy_sdg_ext_calls = copy.copy(sdg_obj._ext_calls)

    for ir_instr in copy_sdg_ext_calls.keys():
        if type(ir_instr).__name__ == 'NewContract':
            solidity_var = SolidityVariableComposed('msg.sender')
            lowlevelcall = LowLevelCall(solidity_var, ir_instr.contract_name, ir_instr.arguments, ir_instr.lvalue,
                                        ir_instr.call_value)
            lowlevelcall.arguments = ir_instr.arguments
            sdg_obj._ir_to_irb[ir_instr]._instruction = lowlevelcall
            index = sdg_obj._ir_to_irb[ir_instr]._origin_bb._instructions.index(ir_instr)
            sdg_obj._ir_to_irb[ir_instr]._origin_bb._instructions[index] = lowlevelcall
            sdg_obj._ext_calls.pop(ir_instr)
            sdg_obj._ext_calls[lowlevelcall] = True

        else:
            analyze_call_destination(sdg_obj, vrg_obj, ir_instr, function, owner_only_vars, blacklisted_functions)
            analyze_lowlevelcall_gas(sdg_obj, vrg_obj, ir_instr, function, blacklisted_functions)


def analyze_call_destination(sdg_obj, vrg_obj, ir_instr, function, owner_only_vars, blacklisted_functions):
    call_destination = ir_instr.destination
    if type(call_destination).__name__ == 'StateVariableSolc':
        state_var_obj = SDG.map_svars_to_sobj[call_destination]

        if state_var_obj in owner_only_vars:
            sdg_obj._ext_calls[ir_instr] = False

    else:
        if type(call_destination).__name__ == 'Constant':
            sdg_obj._ext_calls[ir_instr] = False

        elif type(call_destination).__name__ == 'SoldityVariableComposed':
            sdg_obj._ext_calls[ir_instr] = True

        else:
            depentdent_vars = list(
                slither.analyses.data_dependency.data_dependency.get_dependencies(call_destination, function.contract))
            non_tainted = False

            for var in depentdent_vars:
                if type(var).__name__ == 'StateVariableSolc':
                    non_tainted = True
                    state_var_obj = SDG.map_svars_to_sobj[var]

                    if state_var_obj not in owner_only_vars:
                        non_tainted = False
                        break

            if non_tainted is True:
                sdg_obj._ext_calls[ir_instr] = False


def analyze_lowlevelcall_gas(sdg_obj, vrg_obj, ir_instr, function, blacklisted_functions):
    if type(ir_instr).__name__ == 'LowLevelCall':
        call_gas = ir_instr.call_gas

        if type(call_gas).__name__ == 'Constant':
            call_gas = str(call_gas)

            if int(call_gas) > 2700:
                sdg_obj._ext_calls[ir_instr] = True

            else:
                sdg_obj._ext_calls[ir_instr] = False


        elif type(call_gas).__name__ == 'SolidityVariable' or type(call_gas).__name__ == 'SolidityVariableComposed':
            sdg_obj._ext_calls[ir_instr] = True

        elif call_gas is None:
            sdg_obj._ext_calls[ir_instr] = True

        else:
            if slither.analyses.data_dependency.data_dependency.is_tainted(call_gas, function.contract):
                sdg_obj._ext_calls[ir_instr] = True

            else:
                # if it is a constant or something else
                sdg_obj._ext_calls[ir_instr] = True

            '''
            elif type(call_gas).__name__ == 'StateVariableSolc':
                svar_obj = SDG.map_svars_to_sobj[call_gas]
                writing_functions = vrg_obj._state_var_written[svar_obj]

                for target_function in writing_functions:
                    cfg_obj
                sdg_obj._ext_calls[ir_instr] = False
            '''


# Extract the nested types of a MappingType. Check until we get a type which is not
# a MappingType
def get_vartypes_from_mappingtype(type_to, type_from):
    while type(type_to).__name__ == 'MappingType' or type(type_from).__name__ == 'MappingType':

        if type(type_to).__name__ == 'MappingType':
            current_type = type_to
            type_to = current_type.type_to
            type_from = current_type.type_from

        else:
            current_type = type_from
            type_to = current_type.type_to
            type_from = current_type.type_from

    return type_to, type_from


'''
    This function extracts the state variables which are structures.
    It checks the type of a variable. A variable is of type structure if it is of
    type  `UserDefinedType`. If a variable is of 'MappingType' we need to check further what is the
    type of `type_to` and type of `type_from`. And, we should check the nested types until we get a 
    `type_to` or `type_from` other than a `MappingType`.
'''


def get_structure_vars(state_variables):
    map_svars_to_struct = dict()

    for var in state_variables:
        if type(var.type).__name__ == 'UserDefinedType':
            if type(var.type.type).__name__ == 'StructureSolc':
                map_svars_to_struct[var] = var.type.type

        if type(var.type).__name__ == 'MappingType':
            # Check nested type until we get a non MappingType
            type_to, type_from = get_vartypes_from_mappingtype(var.type.type_to, var.type.type_from)

            if type(type_to).__name__ == 'UserDefinedType':
                if type(type_to.type).__name__ == 'StructureSolc':
                    map_svars_to_struct[var] = type_to.type

            if type(type_from).__name__ == 'UserDefinedType':
                if type(type_from.type).__name__ == 'StructureSolc':
                    structure_vars[var] = type_from.type.elems
                    map_svars_to_struct[var] = type_from.type

        if type(var.type).__name__ == 'ArrayType':
            if type(var.type.type).__name__ == 'UserDefinedType':
                if type(var.type.type.type).__name__ == 'StructureSolc':
                    map_svars_to_struct[var] = var.type.type.type

    return map_svars_to_struct


def count_checks_on_svars(slither_obj, callgraph):
    total_conditions = 0
    svar_conditions = 0

    composed_graph = nx.DiGraph()
    root_nodes = []

    for contract in callgraph._contract_callgraph.keys():
        graph = callgraph._contract_callgraph[contract]
        composed_graph = nx.compose(composed_graph, graph)

    for x in composed_graph.nodes:
        if graph.in_degree(x) == 0:
            root_nodes.append(x)

    public_functions = []
    for root_node in root_nodes:
        function = root_node[1]
        if function.visibility in function_visibility:
            public_functions.append(root_node)

    worklist = []
    worklist.extend(public_functions)

    while len(worklist) != 0:
        function_pair = worklist.pop(0)
        successors = composed_graph.successors(function_pair)
        successors_copy = []

        for successor in successors:
            successors_copy.append(successor)

        caller = function_pair[1]
        for node in caller.nodes:
            internal_calls = node.internal_calls

            for library_call in node.library_calls:
                internal_calls.append(library_call[1])

            for internal_call in internal_calls:
                if type(internal_call).__name__ != 'SolidityFunction' and type(
                        internal_call).__name__ != 'ModifierSolc':
                    if len(node.local_variables_read) == 0:
                        if (internal_call.contract, internal_call) not in public_functions:
                            public_functions.append((internal_call.contract, internal_call))
                            worklist.append((internal_call.contract, internal_call))
                    else:
                        l_read = set([x.canonical_name for x in node.local_variables_read])
                        c_params = set([x.canonical_name for x in caller.parameters])

                        if c_params.issuperset(l_read):
                            if (internal_call.contract, internal_call) not in public_functions:
                                public_functions.append((internal_call.contract, internal_call))
                                worklist.append((internal_call.contract, internal_call))

    for contract in slither_obj.contracts:
        for function in contract.functions:
            for node in function.nodes:
                if node.is_conditional():
                    total_conditions += 1

                    local_vars = node.local_variables_read
                    if len(local_vars) == 0:
                        svar_conditions += 1
                    else:
                        # if function.visibility in function_visibility:
                        function_pair = (contract, function)
                        vars = set(local_vars)
                        f_params = set(function.parameters)

                        if f_params.issuperset(vars):
                            if function_pair in public_functions:
                                svar_conditions += 1
                            else:
                                for pair in public_functions:
                                    if function_pair[1].name == pair[1].name:
                                        svar_conditions += 1
                                        break
                        else:
                            pass

    percentage = svar_conditions / total_conditions
    return percentage


def process_modfiers(slither_obj, graph_dir):
    modifiers_cfgs = {}
    for contract in slither_obj.contracts:
        for modifier in contract.modifiers:
            modifiers_cfgs[modifier] = CFG(slither_obj, contract, modifier, modifiers_cfgs, graph_dir)

    return modifiers_cfgs


def get_child_contracts(slither_obj):
    child_contracts = []
    for contract in slither_obj.contracts:
        if len(contract.derived_contracts) == 0 and contract.fullyImplemented is True and contract.contract_kind != 'library':
            child_contracts.append(contract)

    child_contracts = list(set(child_contracts))

    return child_contracts