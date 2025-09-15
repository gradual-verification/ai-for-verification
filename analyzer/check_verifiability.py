from subprocess import run, PIPE, STDOUT
from extractor import *
from helper import *
from _csv import writer

# run VeriFast on the given file path and show whether it passes the verification, and return the result
def run_verifast(file: str) -> str:
    try:
        proc = run(["verifast", file], stdout=PIPE,
                   stderr=STDOUT, text=True)
        if "0 errors found" in proc.stdout:
            return "yes"
        else:
            return "no"

    except Exception as e:
        return f"exception {e}"


# check whether the output file is verifiable and write the result in a csv file
# also put the processed outputs into another folder to double check
def check_verifiability(input_file: str, target_func_name: str,
                        output_file: str, processed_file: str, lib_files: list[str], writer: writer) -> None:
    output_file_name = os.path.basename(output_file)
    output_file_dir = os.path.dirname(output_file)
    processed_file_dir = os.path.dirname(processed_file)

    input_functions = extract_funcs(input_file)
    output_functions = extract_funcs(output_file)

    # remove the body of other functions and put the new content into processed file,
    # and verify the processed file
    if any(getattr(func, "name", None) == target_func_name for func in input_functions) \
            and any(getattr(func, "name", None) == target_func_name for func in output_functions):
        copy_lib_files(lib_files, processed_file_dir)
        remove_other_func_bodies(target_func_name, output_functions, output_file, processed_file)
        result = run_verifast(processed_file)
    else:
        result = "unknown"

    writer.writerow([output_file_name, result])


