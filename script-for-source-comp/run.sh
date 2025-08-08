#!/bin/bash

output_path="../ai_suite/output/full_study"
input_path="../input-output-pairs/full/split"
cleaned_path="./modified"
input_diy="${input_path}/DIY_split"
input_examples="${input_path}/examples_split"
funcs=60
changed=0
modified=0

mkdir -p "$cleaned_path"

# get all input paths
inputs_unsorted=()
while read -r dir; do
    if [[ "$dir" =~ \.c$  ]]; then
        inputs_unsorted+=("$dir")
    fi
done < <(find "$input_diy" "$input_examples" -maxdepth 2 -type f)

# sort
inputs=()
while read -r item; do
    inputs+=("$item")
done < <(printf '%s\n' "${inputs_unsorted[@]}" | sort)

# get all output paths
models=()
while read -r dir; do
    models+=("$dir")
done < <(find "$output_path" -maxdepth 1 -type d -not -path "$output_path")

for model in "${models[@]}"; do
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
        in=${inputs[$i]}
        outs=${outputs[$i]}
        while read -r out; do
            #echo $out

            # approach: check lines in outfile if they occur in infile
            # clean outfile to remove comments 

            cleaned="$(basename "$model")_$(basename "$out")"
            temp="$cleaned_path/$cleaned"

            sed '/^[[:space:]]*\/\*/,/[[:space:]]*\*\//d' "$out" | grep -v '^[[:space:]]*//' | grep -v '^#' > "$temp"

            align=true
            while read -r line; do
                [ -z "$line" ] && continue

                grep -q -F -- "$line" "$in"  

                if [ $? -ne 0 ]; then
                    align=false
                    break
                fi
            done < "$temp"

            if [ "$align" = true ]; then
                ((changed++))    
                rm -f "$temp" 
            else
                ((modified++))
            fi
                            
        done < <(find "$outs" -type f)
    done
done


echo $changed
echo $modified



