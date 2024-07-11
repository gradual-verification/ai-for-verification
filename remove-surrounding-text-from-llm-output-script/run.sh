#!/bin/bash

# Create the output directory
output_dir="remove_output"
mkdir -p "$output_dir"

# Iterate over each .c file in the current directory
for file in *.c; do
    # Run the Python script and place the output in the output directory
    python3 clean_code.py "$file"

    # Get the base name of the file without the extension
    base_name=$(basename "$file" .c)
    # Move the output file to the output directory
    mv "${base_name}_clean.c" "$output_dir/"
done

echo "Cleaning completed. Output files are in the $output_dir directory."

