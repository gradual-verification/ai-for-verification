#!/bin/bash

# Check if folder path is provided
if [ -z "$1" ]; then
  echo "Please provide the folder path as an argument."
  exit 1
fi

# Get the folder path from the first argument
FOLDER_PATH="$1"

# Check if the provided path is a directory
if [ ! -d "$FOLDER_PATH" ]; then
  echo "The provided path is not a directory."
  exit 1
fi

# Create a folder to store the output files
OUTPUT_FOLDER="${FOLDER_PATH}/verifast_results"
mkdir -p "$OUTPUT_FOLDER"

# Loop through each file in the directory
for file in "$FOLDER_PATH"/*; do
  # Check if the file is non-empty and is a regular file
  if [ -s "$file" ] && [ -f "$file" ]; then
    echo "Running ./verifast on $file"
    output_file="${OUTPUT_FOLDER}/$(basename "$file")_verifast_result"
    ./verifast "$file" > "$output_file"
    echo "Output written to $output_file"
  fi
done

