import os
import sys
from typing import Tuple, List

from components.function_info import FunctionInfo
from utils.LLM_handler import annotate_lemma, verify_and_fix_lemma
from utils.extractor import split
from utils.lemma_creator import create_lemmas
from utils.standardizer import standardize
from utils.renamer import rename_predicates
from utils.validator import validate

# Given a name to a program and a suffix,
# this function preprocesses and extracts its non-functions and function (after renaming).
# Here, non-functions is a list of text of such components.
def preprocess_and_extract(c_file: str, suffix: str) -> Tuple[List[str], FunctionInfo]:
    # standardize get the ast of the program
    standard_c_file = standardize(c_file)

    # rename the predicates in the original file
    renamed_c_file = rename_predicates(standard_c_file, suffix)

    # extract the definition of non-functions and functions of the renamed program
    return split(renamed_c_file)


# Given the name of a folder that stores the helper lemmas and the max number of fixes,
# this function leverages LLM and VeriFast to prove each lemma.
def prove_lemma(folder_name: str, example_file_name: str, max_fix_iter: int):
    with open(example_file_name, 'r') as file:
        examples = file.read()

    for file_name in os.listdir(folder_name):
        file_path = os.path.join(folder_name, file_name)
        # 1. add auxiliary specs using LLM with few-shot examples
        annotate_lemma(file_path, examples)
        # 2. verify and fix until successful or max_fix_iter is reached
        result = verify_and_fix_lemma(file_path, max_fix_iter)
        print(file_path + ': verified ' + str(result))


def main():
    c_file_1 = 'stack_fbp.c'
    suffix_1 = 'gt'
    c_file_2 = 'stack_fbp.c'
    suffix_2 = 'fbp'
    folder_name = 'lemmas'
    max_fix_iter = 2
    example_file_name = 'examples.txt'

    # 1. extract the components of two programs
    renamed_non_funcs_1, renamed_func_1 = preprocess_and_extract(c_file_1, suffix_1)
    renamed_non_funcs_2, renamed_func_2 = preprocess_and_extract(c_file_2, suffix_2)

    # 2. check whether those components are equivalent
    is_eq = validate(renamed_non_funcs_1, renamed_func_1, renamed_non_funcs_2, renamed_func_2)
    if not is_eq:
        sys.exit('components are not equivalent.\n')

    # 3. create helper lemmas for 4 directions
    create_lemmas(renamed_non_funcs_1, renamed_func_1, suffix_1,
                  renamed_func_2, suffix_2, folder_name)

    # 4. leverage LLM to annotate and fix each lemma, and leverage VeriFast to verify the lemma
    prove_lemma(folder_name, example_file_name, max_fix_iter)


if __name__ == '__main__':
    main()
