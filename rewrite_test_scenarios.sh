#!/bin/bash

for i in $(seq 0 1 440); do
    file="generatedPrograms/ontology${i}/ontology${i}.dtg"
    echo "Processing $file"
    base_name=$(basename "$file" .dtg)
    output_file="results/${base_name}_rew_results.txt"
    echo "Output will be written to $output_file"
    java -jar tools/warded-rewriter.jar $file > $output_file
done
