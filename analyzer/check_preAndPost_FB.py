from extractor import *
from _csv import writer

from helper import *


# check whether the FB of precondition and postcondition of target function
# between the input file and the output file is equivalent or not.
# write the result into a csv file,
# also put the unsured-outputs into another folder to double check
def check_preAndPost_FB(input_file: str, target_func_name: str, output_file: str,
                        processed_file: str, writer: writer) -> None:
    output_file_name = os.path.basename(output_file)

    input_functions = extract_functions(input_file)
    input_other_definitions = extract_other_definition(input_file, input_functions)
    output_functions = extract_functions(output_file)
    output_other_definitions = extract_other_definition(output_file, output_functions)

    input_target_func = next((f for f in input_functions if f.name == target_func_name), None)
    output_target_func = next((f for f in output_functions if f.name == target_func_name), None)

    result = ""

    # the FB of pre&post are equivalent, if they are exactly the same
    if input_other_definitions == output_other_definitions and \
            input_target_func and output_target_func and \
            input_target_func.pre_and_post == output_target_func.pre_and_post:
        result = "equivalent"
    # otherwise, copy into another folder for a double check
    else:
        result = "unknown"
        copy_content(output_file, processed_file)

    writer.writerow([output_file_name, result])
