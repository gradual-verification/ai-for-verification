import sys
from utils.validator import validate
from utils.top import preprocess_and_extract, create_lemmas, prove_lemmas


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
    prove_lemmas(folder_name, example_file_name, max_fix_iter)


if __name__ == '__main__':
    main()
