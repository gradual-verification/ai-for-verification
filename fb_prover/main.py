import sys
from utils.extractor import extract
from utils.lemma_creator import create_lemmas
from utils.validator import validate


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
