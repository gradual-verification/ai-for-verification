import sys
from typing import Tuple, List

from components.function_info import FunctionInfo
from utils.extractor import split
from utils.lemma_creator import create_lemmas
from utils.preprocessor import preprocess
from utils.renamer import rename_predicates
from utils.validator import validate

# Given a name to a program and a suffix,
# this function extracts its non-functions and function (after renaming).
# Here, non-functions is a list of text of such components.
def extract(c_file: str, suffix: str) -> Tuple[List[str], FunctionInfo]:
    # standardize get the ast of the program
    standard_c_file = preprocess(c_file)

    # rename the predicates in the original file
    renamed_c_file = rename_predicates(standard_c_file, suffix)

    # extract the definition of non-functions and functions of the renamed program
    return split(renamed_c_file)


def main():
    c_file_1 = 'stack_fbp.c'
    suffix_1 = 'gt'
    c_file_2 = 'stack_fbp.c'
    suffix_2 = 'fbp'

    # 1. extract the components of two programs
    renamed_non_funcs_1, renamed_func_1 = extract(c_file_1, suffix_1)
    renamed_non_funcs_2, renamed_func_2 = extract(c_file_2, suffix_2)

    # 2. check whether those components are equivalent
    is_eq = validate(renamed_non_funcs_1, renamed_func_1, renamed_non_funcs_2, renamed_func_2)
    if not is_eq:
        sys.exit("components are not equivalent.\n")

    # 3. create helper lemmas for 4 directions
    create_lemmas(renamed_non_funcs_1, renamed_func_1, suffix_1, renamed_func_2, suffix_2)


if __name__ == "__main__":
    main()
