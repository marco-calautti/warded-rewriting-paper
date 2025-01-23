import json
import reasoners_wrapper
import shutil
import sys


ENGINES = ["vlog","dlv","dlvExists","integraal"] 
ONTOLOGY_NAMES = ['A','B','C','D','E','F','G','H']
NUM_ONTOLOGIES = len(ONTOLOGY_NAMES)
DATABASE_SIZES = ['10k','30k','50k','70k','90k']

if len(sys.argv) != 4:
     print("Usage: <engine name in [vlog,dlv,dlvExists,integraal]> <db size in [10k,30k,50k,70k,90k]> <rew|original>")
     sys.exit(0)

engine = sys.argv[1]
db_size = sys.argv[2]
mode = sys.argv[3]

if engine not in ENGINES:
     print("Wrong engine name: ", engine)
     sys.exit(-1)

if db_size not in DATABASE_SIZES:
     print("Wrong database size: ", db_size)
     sys.exit(-1)
    
if mode not in ("rew","original"):
     print("Wrong mode: ", mode)
     sys.exit(-1)

reasoner = reasoners_wrapper.ReasonersWrapper("tools/reasoners-runner.jar")

with open(f"results/{engine}_{mode}_structural_results_{db_size}.json","w") as f:
        f.write("[\n")

for i,name in enumerate(ONTOLOGY_NAMES):
    bulk = "_bulk" if mode == "rew" else ""
    ontology_path = f"generatedPrograms/synth{name}/synth{name}{bulk}.dtg"
    annotations_path = f"generatedPrograms/synth{name}/synth{name}.annotations"
    database_path = f"generatedPrograms/synth{name}/inputCsv/{db_size}/"
    shutil.copytree(database_path, f"generatedPrograms/synth{name}/inputCsv/",dirs_exist_ok=True)

    status, time = reasoner.reason(ontology_path,annotations_path, timeout = 300, reasoner = engine)
    
    to_save = {"status" : status, "elapsed": time, "ontology": f"synth{name}", "database_size": f"{db_size}"}

    print(to_save)
    print()

    with open(f"results/{engine}_{mode}_structural_results_{db_size}.json","a") as f:
        json.dump(to_save,f)
        if i < NUM_ONTOLOGIES - 1:
            f.write(",\n\n")
        else:
            f.write("\n]\n")
        
