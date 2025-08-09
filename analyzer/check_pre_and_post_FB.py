from extractor import *
from _csv import writer
from subprocess import run, STDOUT, PIPE

from helper import *


# get the ast of cfile in verifast by running verifast with -dump_ast option
# note that we delete the temporary output_file at the end
def get_verifast_ast(cfile: str, output_file: str) -> str:
    try:
        run(["verifast", "-dump_ast", output_file, cfile], stdout=PIPE,
                   stderr=STDOUT, text=True)

        if os.path.exists(output_file):
            with open(output_file) as f:
                ast = f.readlines()

            Path(output_file).unlink(missing_ok=True)
            return "".join(ast)
        else:
            return ""

    except Exception as e:
        Path(output_file).unlink(missing_ok=True)
        return ""


# check whether precondition, postcondition and definitions of struct and predicates in two functions are equivalent in AST
# done by writing the definitions into temporary files, running verifast to get the ast and deleting the temp files.
def check_pre_and_post_and_def_equivalence(func1: Function, def1: str,
                                           func2: Function, def2: str) -> bool:
    func1_temp_file = "func1_temp_file.c"
    func1_ast_temp_file = "func1_ast_temp_file.c"
    func2_temp_file = "func2_temp_file.c"
    func2_ast_temp_file = "func2_ast_temp_file.c"

    func1_decl = get_func_decl(func1)
    func2_decl = get_func_decl(func2)

    with open(func1_temp_file, "w") as f:
        f.write(def1 + "\n\n" + func1_decl)

    with open(func2_temp_file, "w") as f:
        f.write(def2 + "\n\n" + func2_decl)

    func1_ast = get_verifast_ast(func1_temp_file, func1_ast_temp_file)
    func2_ast = get_verifast_ast(func2_temp_file, func2_ast_temp_file)

    Path(func1_temp_file).unlink(missing_ok=True)
    Path(func2_temp_file).unlink(missing_ok=True)

    return func1_ast == func2_ast and func1_ast != ""


# check whether the FB of precondition and postcondition of target function
# between the input file and the output file is equivalent or not.
# write the result into a csv file,
# also put the unsured-outputs into another folder to double-check
def check_pre_and_post_FB(input_file: str, target_func_name: str, output_file: str,
                          processed_file: str, writer: writer) -> None:
    output_file_name = os.path.basename(output_file)

    input_functions = extract_funcs(input_file)
    input_other_definitions = extract_other_def(input_file, input_functions)
    output_functions = extract_funcs(output_file)
    output_other_definitions = extract_other_def(output_file, output_functions)

    input_target_func = next((f for f in input_functions if f.name == target_func_name), None)
    output_target_func = next((f for f in output_functions if f.name == target_func_name), None)

    # the FB of pre&post are equivalent, if they (pre, post and definition) are exactly the same
    if input_target_func and output_target_func and \
        check_pre_and_post_and_def_equivalence(input_target_func, input_other_definitions,
                                               output_target_func, output_other_definitions):
        result = "equivalent"
    # otherwise, copy into another folder for a double check
    else:
        result = "unknown"
        copy_content(output_file, processed_file)

    writer.writerow([output_file_name, result])
