from typing import List
from components.function_info import FunctionInfo

# Given the non-function and function components of two programs
# this function validates whether those programs are equivalent.
def validate(non_funcs_1: List[str], func_1: FunctionInfo,
             non_funcs_2: List[str], func_2: FunctionInfo) -> bool:
    return validate_non_funcs_equivalence(non_funcs_1, non_funcs_2) and \
            validate_funcs_equivalence(func_1, func_2)


# Given two lists of text format of non-function components,
# this function strictly validates whether their contents (except predicates) are exactly the same.
def validate_non_funcs_equivalence(non_funcs_1: List[str], non_funcs_2: List[str]) -> bool:
    # todo: fix it
    return True

# Given two functions,
# this function check equivalence by checking their name
def validate_funcs_equivalence(func1: FunctionInfo, func2: FunctionInfo) -> bool:
    return func1.name == func2.name