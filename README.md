# Sailfish
This repository contains the code and the experimental data for the IEEE S&P'22 paper: [SAILFISH: Vetting Smart Contract State-Inconsistency Bugs in Seconds](https://www.computer.org/csdl/proceedings-article/sp/2022/131600b235/1A4Q46YLRrq)

# Installing Sailfish
The easiest way to get started is to use our pre-built docker image: `docker pull holmessherlock/sailfish:latest`.
However, if you want to build the tool yourself, follow the steps in `docker/Dockerfile`.

# Running Sailfish

If you are using the docker image, spawn a container: `docker run -it holmessherlock/sailfish:latest bash`.
Navigate to the `sailfish/code/static_analysis/analysis` directory.

## Get help
```bash
python contractlint.py --help
```

## Run test-cases
```bash
python contractlint.py -c ../../test_cases/reentrancy/mutex_fp_prunning_non_reentrant.sol -o <path/to/output-dir> -r range -p DAO,TOD -oo -sv cvc4
```

```bash
python contractlint.py -c ../../test_cases/reentrancy/mutex_fp_prunning_non_reentrant.sol -o <path/to/output-dir> -r havoc -p DAO,TOD -oo -sv cvc4
```

# Symbolic executor

## Run the symbolic executor standalone
To run the symbolic executor, you need a compatible JSON file.
Check the input JSON specifications for detailed syntax.
If your JSON file comes from range analysis, run the translator to get a compatible JSON file before you run the tool.

```bash
./reentrancy | tod | tod-complement \
	<--file "/path/to/file.json"|--raw "json string"> \
	[--attack none|havoc|range|path] \
	[--solver z3|cvc4|yices] \
	[--beb <non-negative integer>] \
	[--verbose] \
	[--debug]
```

***--file***: specify the json file path to read in

***--raw***: specify the json raw string to read in

***--attack*** (default: `none`): specify the attack mode

***--solver*** (default: `cvc4`): specify the backend solver to use, you may need to configure the solver (see [here](https://docs.racket-lang.org/rosette-guide/sec_solvers-and-solutions.html); for `cvc4`, the `1.7` version is recommended)

***--beb*** (default: `0`/strict mode, `10`/tolerant mode): specify the block execution bound (maximum number of times a block can be executed), if set to integer <=0, no bound will be applied. <u>For tolerant mode, `10` is recommended to eliminate potential soundness problem (see known issues).</u>

# Publication
Find the paper [here](https://arxiv.org/abs/2104.08638).

```
@InProceedings{sailfish-2022,
  author = {Priyanka Bose, Dipanjan Das, Yanju Chen, Yu Feng, Christopher Kruegel},
  title = {SAILFISH: Vetting Smart Contract State-Inconsistency Bugs in Seconds},
  booktitle = {IEEE Symposium on Security & Privacy, May 2022},
  year = {2022}
```
