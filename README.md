# A Datalog Rewriting Algorithm for Warded Ontologies

This repository collects the source code and the benchmarks used for the experimental evaluation of the paper:

"A Datalog Rewriting Algorithm for Warded Ontologies"

## OVERVIEW

The repository is organized as follows:

- The directory `src` contains the source code of the following projects:
    - `warded-rewriter`: implements the WardedRewrite algorithm presented in the paper. This is used by the scripts in the root of this repository, and is not meant to be executed on its own.
    - `reasoners-runner`: a convenient tool that is able to run the different Datalog-base engines considered in the paper. This is used by the scripts in the root of this repository, and is not meant to be executed on its own.
- The directory `generatedPrograms` contains the all the scenarios used for the experimental evaluation, where:
    - directories `ontology0`,...,`ontology440` contain the test scenarios (The README.md inside the `generatePrograms` directory provides additional details on how they have been generated).
    - directories `synthA`,...,`synthH` contain the structural scenarios.
- The directory `results` is empty and will contain the logs and results when reproducing our experimental evaluation.
- The directory `tools` contains the compiled version of the projects of the src directory, plus the binaries of the Datalog-based engines we use (only dlv and dlvExists, since VLog and Integraal are Java-based and have been embedded in our reasoners-runner). These are used by the scripts in the root of this repository, and are not meant to be executed on their own.
    - *Note on Vadalog*: Since Vadalog is available only under a license, we cannot share it here, but it can be made available upon request.
- The root of this repository contains the different scripts needed to run each phase of our experimental evaluation:
    - `rewrite_structural.sh`: when executed from the terminal, it will run warded-rewriter over all OMQs from the structural scenarios.
    - `rewrite_test_scenarios.sh`: when executed from the terminal, it will run warded-rewriter over all OMQs from the test scenarios.
    - `run_engine_structural.py`: runs the specified Datalog-based engine over the original or the rewriting of all structural scenarios, for the given database size. Run the script without arguments for more details on how to execute it.
    - `run_engine_test_scenarios.py`: runs the specified Datalog-based engine over the original or the rewriting of all test scenarios. Run the script without arguments for more details on how to execute it.

## Setup    
To reproduce our experiments, a Linux-based system is required, and Java 22, as well as Python 3, must be installed. Then, we need to make the .sh files in this repo executable with:

`sudo chmod +x script_name.sh`

Make the `dlv` and `dlvExists` binaries in the tools directory executable as well.

## Running warded-rewriter over test and structural scenarios

To rewrite the OMQs of the test scenarios, run:

`./rewrite_test_scenarios.sh`

To rewrite the OMQs of the structural scenarios, run:

`./rewrite_structural.sh`

all the logs related to the running time and other statistics can be found in the results directory, while the rewritten OMQs can be found in each directory inside `generatedPrograms` corresponding to the rewritten OMQ.

## Running the Datalog-based engines

To run, e.g., `vlog`, over the original OMQs of all structural scenarios, over the database with `30k` facts per relation, run:

`python run_engine_structural.py vlog 30k original`

To do the same, but over the rewriting of the OMQs:

`python run_engine_structural.py vlog 30k rew`

Other options for the engines are `dlv`, `dlvExists`, `integraal`.

To run, e.g., `vlog` over the original OMQs of all test scenarios, run:

`python run_engine_test_scenarios.py vlog original`

Use `rew` instead of `original` to run the engine over the rewritten version.

*Note:* There is no need to run `rewrite_structural.sh` or `rewrite_test_scenarios.sh` in order to execute the engines over the rewritten versions, as we already provide, for convenience, the rewritings in the directory of each scenario.


All the logs with running times will be found in the `results` directory.