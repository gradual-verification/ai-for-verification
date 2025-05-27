#!/usr/bin/env bash
set -euo pipefail

for base in ./DIY ./examples; do
  # skip if base dir doesn’t exist
  [[ -d $base ]] || continue

  # iterate sorted subdirs
  for dir in "$base"/*/; do
    # strip trailing slash and leading path
    name=$(basename "${dir%/}")
    c_file="$dir$name.c"

    if [[ -f $c_file ]]; then
      count=$(ctags -x --c-kinds=fp "$c_file" 2>/dev/null | wc -l)
      echo "$base/$name.c: $count functions"
    else
      echo "$base/$name.c not found"
    fi
  done
done