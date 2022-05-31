import sys
sys.path.append("..")

import argparse
import os
import logging
import sys
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
from lib import *
from shutil import rmtree
from state_var import *
import subprocess
from range_graph import *
from main_helper import *

# Slither tip: 3e1f0d0a2fe8a8beb01121a6d3fc35b7bf033283

def analyze_contracts(contract_path, patterns, output_dir, range_type, dump_graph, static_only, call_heuristic, icc, contract_mapping_path, solver_type, solc_path=None):
    try:
        dao = False
        tod = False

        if 'DAO' in patterns:
            dao = True

        if 'TOD' in patterns:
            tod = True

        if dao is True or tod is True:
            contract_name = os.path.basename(contract_path)
            info("Analysing started: %s" % contract_name)
            contract_name_without_ext = os.path.splitext(contract_name)[0]
            graph_dir = os.path.join(output_dir, contract_name_without_ext)

            if os.path.exists(graph_dir):
                rmtree(graph_dir)

            if not os.path.exists(graph_dir):
                os.mkdir(graph_dir)
            log_path = os.path.join(graph_dir, 'contractlint.log')
            log = init_logging('analyzer.%s' % contract_name_without_ext, log_path, file_mode='w', console=True)

            # Record analysis start time
            now = datetime.datetime.now()
            analysis_start_time = now.strftime(DATE_FORMAT)
            log.info('Analysis started at: %s' % analysis_start_time)
            start_time = time.time()


            # Get solc binary path
            if not solc_path:
                _, solc_path = get_solc_path(contract_path, log)


            # Initialize Slither
            slither_obj = Slither(contract_path, solc=solc_path)
            target_contracts = get_child_contracts(slither_obj)

            # Generate callgraph
            log.info('Callgraph generation started!')
            callgraph = CallGraph(slither_obj, graph_dir, dump_graph, log)
            log.info('Callgraph generation finished!')

            # Build interprocedural cfg for all public functions
            log.info('Interprocedural CFG generation started!')
            generated_icfg, icfg_objects = generate_icfg(slither_obj, callgraph, graph_dir, dump_graph, log)
            log.info('Interprocedural CFG generation finished!')

            # Build storage dependency graph
            log.info('Storage dependency graph generation started!')
            generated_sdg, sdg_objects, owner_only_modifiers = generate_sdg(slither_obj, generated_icfg, graph_dir, dump_graph, log)
            log.info('Storage dependency graph generation finished!')

            # Do inter-contract analysis if application if icc is set to true
            if icc:
                store_static_state()
                try:
                    process_inter_contract_calls_if_exists(sdg_objects, contract_mapping_path, os.path.dirname(contract_path), graph_dir, log)
                except:
                    log.warning("Some error occured during inter-contract analysis!")
                load_static_state()

            log.info('Value Range Analysis started')
            vstart_time = time.time()
            generated_vrg = VRG(slither_obj, callgraph, sdg_objects, target_contracts, graph_dir, dump_graph, log)
            end_time = time.time()
            analysis_duration = end_time - vstart_time
            log.info('Value Range Analysis took %f seconds' % analysis_duration)
            log.info('Value Range Analysis finished')


            # Compose 2 sdgs to detect either TOD or DAO, from here we start incorporating the tod with dao
            log.info('Storage dependency graph compostion started!')
            composed_sdg = generate_composed_sdg(slither_obj, generated_sdg, generated_vrg, graph_dir, sdg_objects, call_heuristic, owner_only_modifiers, target_contracts, contract_path, dump_graph, dao, tod, log)
            log.info('Storage dependency graph compostion finished!')


            # Run re-entrancy detection
            log.info('Dependency detection started!')
            detection = Detection(slither_obj, contract_name, composed_sdg, sdg_objects, icfg_objects, graph_dir, dump_graph, dao, tod, generated_vrg, log)
            log.info('Dependency detection finished!')
            # Write the dependency analysis report
            dump_json(graph_dir, detection.global_detection, 'dependency_info.json')

            # This generates the necessary output files required for symbolic execution
            #dao_symex_paths, dao_per_function_paths, tod_symex_paths, tod_per_function_paths = output_ir_paths_new(slither_obj, generated_vrg, detection.dao_feasible_paths, detection.tod_feasible_paths, contract_name, graph_dir, log)
            dump_json(graph_dir, detection.dao_symex_paths, 'dao_path_info.json')
            dump_json(graph_dir, detection.tod_symex_paths, 'tod_path_info.json')

            # Record analysis duration
            end_time = time.time()
            analysis_duration = end_time - start_time
            log.info('Static Analysis took %f seconds' % analysis_duration)

            if len(detection.global_detection) == 0:
                log.info('Dependency does not exist')
                log.info('Symbolic execution is not needed!')
            else:
                log.info('Dependency exists')

                if static_only == False:
                    if range_type is None:
                        log.warning("Range type should be given")
                        sys.exit(1)

                    if solver_type is None:
                        err('Solver type is not mentioned ..')
                        sys.exit(1)

                    log.info('Invoking symbolic executor!')
                    sstart_time = time.time()
                    #find_feasible_paths(graph_dir, symex_paths, range_type, 'default')
                    find_feasible_paths(graph_dir, detection.dao_symex_paths, detection.dao_per_function_paths, detection.tod_symex_paths, detection.tod_per_function_paths, range_type, solver_type)
                    end_time = time.time()
                    analysis_duration = end_time - sstart_time
                    log.info('Symbolic execution took %f seconds' % analysis_duration)
                    log.info('Symbolic execution finished!')

            log.info('Analysis finished!')

            # Record analysis duration
            end_time = time.time()
            analysis_duration = end_time - start_time
            info('Analysis took %f seconds' % analysis_duration)
            log.info('Analysis took %f seconds' % analysis_duration)

            # Record analysis end time
            now = datetime.datetime.now()
            analysis_end_time = now.strftime(DATE_FORMAT)
            log.info('Analysis finished at: %s' % analysis_end_time)
            
            info("Analysis completed: %s " % (contract_name))
        
        else:
            err("Wrong input pattern, only TOD and DAO supported!")    

    except Exception as e:
        traceback.print_exc()
        sys.exit(1)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Analyzes smart contracts for state variable inconsistancy issues")
    parser.add_argument("--contract-dir", "-c", dest="contract", help="path to the smart contract or the directory containing multiple contracts")
    parser.add_argument("--output-dir", "-o", dest="output", help="path to the output directory")
    parser.add_argument("--inter-contract-call", "-icc", dest="icc", action='store_true', help="Consider inter-contract analysis")
    parser.add_argument("--contracts-mapping-file-path", "-mappingfpath", dest="mappingfpath", help="Path to the contract name to address mapping file")
    parser.add_argument("--dump-graphs", "-dg", dest="graph", action='store_true', help="Dumps all the generated graphs")
    parser.add_argument("--range-type", "-r", dest="range", help="Types of range analysis can be either range, havoc or none")
    parser.add_argument("--solver", "-sv", dest="solver", help="The name of the solver either z3 or cvc4")
    parser.add_argument("--patterns", "-p", type=str, help="comma separated patterns for running the analysis e.g DAO, TOD etc")
    parser.add_argument("--static-only", "-s", dest="static", action='store_true', help="executes only the static analysis")
    parser.add_argument("--owner-only", "-oo", dest="owner_only", action='store_true', help="Applies external call heuristic")
    parser.add_argument("--solc-path", "-sc", dest="solc_path", help="Path to the solc binary to compile the contract")
    args = parser.parse_args()

    # If it's a directory, analyze all the contracts in it
    if os.path.isdir(args.contract):
        path = os.path.join(args.contract, "*.sol")
        contracts = glob.glob(path)
    
    # If it's a single contract, analyze it
    elif os.path.isfile(args.contract):
        contracts = [args.contract]
    
    else:
        err('Non existent contract or directory: %s' % args.contract)
        sys.exit(1)

    patterns = args.patterns.split(",")
    solver = None
    dump_graph = False
    only_static = False
    call_heuristic = False
    icc = False
    
    if args.graph:
        dump_graph = True

    if args.static:
        only_static = True
    
    if args.owner_only:
        call_heuristic = True

    if args.icc and args.mappingfpath is not None:
        icc = True

    contracts_to_be_analyzed = []

    if len(contracts) > 1:
        for contract_path in contracts:
            contract_name = os.path.basename(contract_path)
            contracts_to_be_analyzed.append((contract_path, patterns, args.output, args.range, dump_graph, only_static, call_heuristic, icc, args.mappingfpath,
                                             args.solver, args.solc_path))
    else:
        contract_path = contracts[0]


    # Analyze the contracts using mutiprocessing pool if number of contracts
    # is more than one
    if len(contracts) > 1:
        with multiprocessing.Pool(multiprocessing.cpu_count()) as pool:
            pool.starmap(analyze_contracts, contracts_to_be_analyzed)
        
        pool.join()
    
    else:
        analyze_contracts(contract_path, patterns, args.output, args.range, dump_graph, only_static, call_heuristic, icc, args.mappingfpath,
                          args.solver, args.solc_path)
