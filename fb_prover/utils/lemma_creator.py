import os
from typing import List
from components.function_info import FunctionInfo

def create_lemmas(non_funcs: List[str], func_1: FunctionInfo, suffix_1: str,
                  func_2: FunctionInfo, suffix_2: str):
    # pre: 1 => 2
    lemma_name = 'pre_' + suffix_1 + '_to_' + suffix_2
    lemma_pre = func_1.precond
    lemma_post = func_2.precond
    create_lemma(lemma_name, non_funcs, func_1.signature, lemma_pre, lemma_post)

    # pre: 2 => 1
    lemma_name = 'pre_' + suffix_2 + '_to_' + suffix_1
    lemma_pre = func_2.precond
    lemma_post = func_1.precond
    create_lemma(lemma_name, non_funcs, func_2.signature, lemma_pre, lemma_post)

    # post: 1 => 2
    lemma_name = 'post_' + suffix_1 + '_to_' + suffix_2
    lemma_pre = func_1.postcond
    lemma_post = func_2.postcond
    create_lemma(lemma_name, non_funcs, func_1.signature, lemma_pre, lemma_post)

    # post: 2 => 1
    lemma_name = 'post_' + suffix_2 + '_to_' + suffix_1
    lemma_pre = func_2.postcond
    lemma_post = func_1.postcond
    create_lemma(lemma_name, non_funcs, func_2.signature, lemma_pre, lemma_post)



def create_lemma(name: str, non_funcs: List[str], signature: str, cond1: str, cond2: str):
    lemma_text = '\n'.join(non_funcs)
    lemma_text += '\n\n/*@\nvoid lemma '
    lemma_text += signature + '\n'
    lemma_text += 'requires ' + cond1 + '\n'
    lemma_text += 'ensures ' + cond2 + '\n'
    lemma_text += '{\n\n}\n@*/\n'

    folder = "helper_lemmas"
    os.makedirs(folder, exist_ok=True)
    lemma_file = os.path.join(folder, name + '.c')
    with open(lemma_file, 'w') as file:
        file.write(lemma_text)