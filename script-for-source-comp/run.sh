#!/bin/bash

output_path="../ai_suite/output/full_study"
input_path="../input-output-pairs/full/split"
cleaned_path="./modified"
funcs=60
changed=0
modified=0

mkdir -p "$cleaned_path"

# get all output paths
models=()
while read -r dir; do
    models+=("$dir")
done < <(find "$output_path" -maxdepth 1 -type d -not -path "$output_path")

for model in "${models[@]}"; do
    model_base_name=$(basename "$model")
    model_prefix="${model_base_name%%_*}"
    cleaned_model="$cleaned_path/$model_prefix"
    mkdir -p "$cleaned_model"
    
    diy="${model}/DIY_split"
    examples="${model}/examples_split"

    outputs_unsorted=()
    while read -r dir; do
        outputs_unsorted+=("$dir")
    done < <(find "$diy" "$examples" -maxdepth 1 -type d -not -path "$diy" -not -path "$examples")

    outputs=()
    while read -r item; do
        outputs+=("$item")
    done < <(printf '%s\n' "${outputs_unsorted[@]}" | sort)

    for (( i=0; i<funcs; i++ )); do
        outs=${outputs[$i]}
        func=$(basename "$outs")
        mkdir -p "$cleaned_model/$func/${func}_fb"
        mkdir -p "$cleaned_model/$func/${func}_fbp"
        mkdir -p "$cleaned_model/$func/${func}_nl"

        while read -r out; do

            prompt=$(basename "$out" | sed -E 's/.*_([^.]*)\..*/\1/')
            temp_out="$cleaned_model/$func/${func}_$prompt/$(basename "$out")_out"
            in=$(find $input_path -type f -name "$(basename "$out")")

            temp_in="$cleaned_model/$func/${func}_$prompt/$(basename "$out")_in"

            # clean output file to remove comments
            sed -E -e '/^[[:space:]]*\/\*/,/[[:space:]]*\*\//d' \
                   -e 's/[[:space:]]*\/\/.*$//' \
                   -e '/^[[:space:]]*#.*$/d' \
                   -e 's/^[[:space:]]*//' \
                   -e 's/[[:space:]]*$//' "$out" | awk 'NF' > "$temp_out"

            # clean input file to remove comments
            sed -E -e '/^[[:space:]]*\/\*/,/[[:space:]]*\*\//d' \
                   -e 's/[[:space:]]*\/\/.*$//' \
                   -e '/^[[:space:]]*#.*$/d' \
                   -e 's/^[[:space:]]*//' \
                   -e 's/[[:space:]]*$//' "$in" | awk 'NF' > "$temp_in"

            # diff comparison
            if diff -q "$temp_in" "$temp_out" >/dev/null; then
                align=true
            else
                align=false
            fi

            if [ "$align" = true ]; then
                ((changed++))    
                rm -f "$temp_out"             
                rm -f "$temp_in"
            else
                ((modified++))
                echo $temp_out >> "modified.txt"
            fi
                            
        done < <(find "$outs" -type f)
    done
done

echo $changed
echo $modified
