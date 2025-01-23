#!/bin/bash

for i in A B C D E F G H; do
    file="generatedPrograms/synth${i}/synth${i}.dtg"
    echo "Processing $file"
    base_name=$(basename "$file" .dtg)
    output_file="results/${base_name}_rew_results.txt"
    echo "Output will be written to $output_file"
    java -jar tools/warded-rewriter.jar $file --bulk > $output_file
done
