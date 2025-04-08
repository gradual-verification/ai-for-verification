import os
from typing import Tuple, List

from components.function_info import FunctionInfo
from utils.LLM_handler import annotate_lemma, verify_and_fix_lemma
from utils.extractor import split
from utils.standardizer import standardize
from utils.lemma_creator import create_lemma
from utils.renamer import rename_predicates

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


# Given the non-function text, the basic info of 2 functions, the suffixes of 2 files, and the folder for new lemmas,
# this function create 4 lemmas for 4 directions and write them into the folder
def create_lemmas(non_funcs: List[str], func_1: FunctionInfo, suffix_1: str,
                  func_2: FunctionInfo, suffix_2: str, folder_name: str):
    # pre: 1 => 2
    lemma_name = 'pre_' + suffix_1 + '_to_' + suffix_2
    lemma_pre = func_1.precond
    lemma_post = func_2.precond
    create_lemma(lemma_name, non_funcs, func_1.signature, lemma_pre, lemma_post, folder_name)

    # pre: 2 => 1
    lemma_name = 'pre_' + suffix_2 + '_to_' + suffix_1
    lemma_pre = func_2.precond
    lemma_post = func_1.precond
    create_lemma(lemma_name, non_funcs, func_2.signature, lemma_pre, lemma_post, folder_name)

    # post: 1 => 2
    lemma_name = 'post_' + suffix_1 + '_to_' + suffix_2
    lemma_pre = func_1.postcond
    lemma_post = func_2.postcond
    create_lemma(lemma_name, non_funcs, func_1.signature, lemma_pre, lemma_post, folder_name)

    # post: 2 => 1
    lemma_name = 'post_' + suffix_2 + '_to_' + suffix_1
    lemma_pre = func_2.postcond
    lemma_post = func_1.postcond
    create_lemma(lemma_name, non_funcs, func_2.signature, lemma_pre, lemma_post, folder_name)


# Given the name of a folder that stores the helper lemmas and the max number of fixes,
# this function leverages LLM and VeriFast to prove each lemma.
def prove_lemmas(folder_name: str, example_file_name: str, max_fix_iter: int):
    with open(example_file_name, 'r') as file:
        examples = file.read()

    for file_name in os.listdir(folder_name):
        file_path = os.path.join(folder_name, file_name)
        # 1. add auxiliary specs using LLM with few-shot examples
        annotate_lemma(file_path, examples)
        # 2. verify and fix until successful or max_fix_iter is reached
        result = verify_and_fix_lemma(file_path, max_fix_iter)
        print(file_path + ': verified ' + str(result))
