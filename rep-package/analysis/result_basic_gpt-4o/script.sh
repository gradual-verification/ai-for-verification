#!/bin/bash

# Find all files in subdirectories with "_n.c" in their name
find . -type f -name "*_m.c*" | while read -r file; do
    # Extract directory path and base name
    dir=$(dirname "$file")
    base=$(basename "$file")
    # Replace "_n.c" with "_nl.c"
    new_name=$(echo "$base" | sed 's/_m\.c/_fb+.c/g')
    # Rename the file
    mv "$file" "$dir/$new_name"
    echo "Renamed: $file -> $dir/$new_name"
done

