import os
from typing import List

# Given two list of non-function components,
# this function merges them by getting the distinct ones (not sure whether the order matters).
def merge_non_funcs(non_funcs_1: List[str], non_funcs_2: List[str]) -> List[str]:
    merged_non_funcs = non_funcs_1.copy()

    for non_func_2 in non_funcs_2:
        if non_func_2 not in non_funcs_1:
            merged_non_funcs.append(non_func_2)

    return merged_non_funcs


# Given the name of a lemma, its non-function text, signature,
# precondition, postcondition and the folder name of created lemma file,
# this function creates a helper lemma and writes it into the folder.
def create_lemma(lemma_name: str, non_funcs: List[str], signature: str,
                 cond1: str, cond2: str, folder_name: str):
    lemma_text = '\n'.join(non_funcs)
    lemma_text += '\n\n/*@\nvoid lemma '
    lemma_text += signature + '\n'
    lemma_text += 'requires ' + cond1 + '\n'
    lemma_text += 'ensures ' + cond2 + '\n'
    lemma_text += '{\n\n}\n@*/\n'

    os.makedirs(folder_name, exist_ok=True)
    lemma_file_path = os.path.join(folder_name, lemma_name + '.c')
    with open(lemma_file_path, 'w') as file:
        file.write(lemma_text)