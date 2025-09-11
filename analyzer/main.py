import csv
import sys

from clang.cindex import Config

from check_verifiability import *
from check_pre_and_post_FB import *


def main():
    if len(sys.argv) < 4:
        # llm: anthropic:claude-3-7-sonnet-20250219_RAG_SPARSE_split, google:gemini-2.5-pro_RAG_SPARSE_split, openai:gpt-4o_RAG_SPARSE_split
        print("please add <input type> (nl, fb or fbp) and <llm> and <option> (-v for verifiability, -p for pre&post FB, -c for src code FB")
        exit()


    input_type = sys.argv[1]
    llm = sys.argv[2]
    option = sys.argv[3]
    input_suffixes = (input_type + ".c",)

    Config.set_library_file("/usr/lib/llvm-19/lib/libclang-19.so")

    input_root_dir = "../input-output-pairs/full/split/"
    output_root_dir = "../ai_suite/output/full_study/"
    processed_root_dir = "../ai_suite/output/full_study_processed/"
    output = input_type + "_" + llm + "_result.csv"
    metric = "FB_spec"

    output_subdir_names = get_subdir_names(output_root_dir, llm)

    rel_input_files = get_rel_input_files(input_root_dir, input_suffixes)

    with open(output, "w", newline="") as f:
        writer = csv.writer(f)
        writer.writerow(["benchmark", metric])

        for output_subdir_name in output_subdir_names:
            output_subdir = os.path.join(output_root_dir, output_subdir_name)
            processed_subdir = os.path.join(processed_root_dir, output_subdir_name)

            for rel_input_file in rel_input_files:
                target_func_name = get_target_func_name(rel_input_file, input_suffixes)
                input_file = os.path.join(input_root_dir, rel_input_file)

                input_dir = os.path.dirname(input_file)
                lib_files = get_lib_files(input_dir)

                output_file = os.path.join(output_subdir, rel_input_file)
                processed_file = os.path.join(processed_subdir, rel_input_file)

                if option == "-v":
                    check_verifiability(input_file, target_func_name, output_file, processed_file, lib_files, writer)
                elif option == "-p":
                    check_pre_and_post_FB(input_file, target_func_name, output_file, processed_file, lib_files, writer)



if __name__ == "__main__":
    main()
