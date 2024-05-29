#!/bin/bash

# Input and output directories
input_dir="/home/zhaorui/Desktop/remove"
output_dir="/home/zhaorui/Desktop/remove/after"

# Create the output directory if it doesn't exist
mkdir -p "$output_dir"

# Collect all C file names in the input directory
c_files=$(find "$input_dir" -maxdepth 1 -type f -name "*.c")

# Iterate over each C file
for c_file in $c_files; do
    # Get the file name without extension
    filename=$(basename -- "$c_file")
    filename_noext="${filename%.*}"

    # Run the Python script to process the C file
    python3 removeProcess.py "$c_file" "$output_dir/${filename_noext}_m.c"

    echo "Processed $filename and saved to $output_dir/${filename_noext}_m.c"
done

echo "All C files processed."

