#!/bin/bash

for name in $(ls -1d */ | sort); do
    name="${name%/}"  # remove trailing slash
    if [[ -d "$name" ]]; then
        c_file="$name/$name.c"
        if [[ -f "$c_file" ]]; then
            count=$(ctags -x --c-kinds=f "$c_file" 2>/dev/null | wc -l)
            echo "$name.c: $count functions"
        else
            echo "$name.c not found"
        fi
    fi
done