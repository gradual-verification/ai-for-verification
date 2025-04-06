from typing import Tuple, List
from components.function_info import FunctionInfo
from utils.preprocessor import preprocess
from utils.parser import split
from utils.renamer import rename_predicates

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