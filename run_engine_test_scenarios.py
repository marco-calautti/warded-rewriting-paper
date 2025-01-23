import json
import reasoners_wrapper
import shutil
import sys


ENGINES = ["vlog","dlv","dlvExists","integraal"] 
NUM_ONTOLOGIES = 121

if len(sys.argv) != 3:
     print("Usage: <engine name in [vlog,dlv,dlvExists,integraal]> <rew|original>")
     sys.exit(0)

engine = sys.argv[1]
mode = sys.argv[2]

if engine not in ENGINES:
     print("Wrong engine name: ", engine)
     sys.exit(-1)

if mode not in ("rew","original"):
     print("Wrong mode: ",mode)
     sys.exit(-1)

reasoner = reasoners_wrapper.ReasonersWrapper("tools/reasoners-runner.jar")

with open(f"results/{engine}_{mode}_test_scenarios_results.json","w") as f:
        f.write("[\n")

for i in range(NUM_ONTOLOGIES):
    rew_mode = "_qout_1" if mode == "rew" else ""
    ontology_path = f"generatedPrograms/ontology{i}/ontology{i}{rew_mode}.dtg"
    annotations_path = f"generatedPrograms/ontology{i}/ontology{i}.annotations"

    status, time = reasoner.reason(ontology_path,annotations_path, timeout = 300, reasoner = engine)
    
    to_save = {"status" : status, "elapsed": time, "ontology": f"{i}"}

    print(to_save)
    print()

    with open(f"results/{engine}_{mode}_test_scenarios_results.json","a") as f:
        json.dump(to_save,f)
        if i < NUM_ONTOLOGIES - 1:
            f.write(",\n\n")
        else:
            f.write("\n]\n")
        
