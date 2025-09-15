from _csv import writer
from helper import *
from extractor import *
from check_verifiability import run_verifast


# check whether the predicate, pre and postcondition in the output file can be compiled by verifast,
# by removing the definition inside the function and running verifast.
def check_output_pre_and_post_compile(output_file: str, processed_file: str,
                                      lib_files: list[str], writer: writer) -> None:
    output_file_name = os.path.basename(output_file)
    output_functions = extract_funcs(output_file)
    processed_file_dir = os.path.dirname(processed_file)

    copy_lib_files(lib_files, processed_file_dir)
    remove_other_func_bodies("", output_functions, output_file, processed_file)
    result = run_verifast(processed_file)
    writer.writerow([output_file_name, result])