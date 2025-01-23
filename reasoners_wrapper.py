import subprocess
import os
import json

keywords = ["SUCCESS","TIMEOUT","INTERRUPTED","NONTERMINATING","EXCEPTION"]

class ReasonersWrapper:
    def __init__(self, jar_path):
        #os.environ['JAVA_HOME'] = "/notebooks/shared/experiments/tools/java"
        self.jar_path = jar_path
        
    def reason(self,dtg_path,annotations_path,*,timeout = 0, reasoner = "vlog"):
        #java_home = os.environ['JAVA_HOME']
        result = subprocess.run(['java', '-Xmx14g', '-jar', self.jar_path, reasoner, dtg_path, annotations_path, str(timeout)], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        decoded_result = result.stdout.decode('utf-8')
        decoded_result = next(x for x in decoded_result.split('\n') if any(y in x for y in keywords))
        return decoded_result.strip().split()
    
