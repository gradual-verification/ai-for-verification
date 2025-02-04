#!/usr/bin/env bash

# Exit immediately on error, treat unset variables as an error
set -euo pipefail

# Loop over all .c files in the current directory
for f in *.c; do
  # If there are no .c files, the glob might return '*.c' literally,
  # so check if the file actually exists.
  [ -e "$f" ] || continue
  
  # Strip the .c extension to get the directory name
  dir="${f%.c}"
  
  # Create the subdirectory (if it doesn’t already exist)
  mkdir -p "$dir"
  
  # Move the .c file into the new subdirectory
  mv "$f" "$dir"
done
