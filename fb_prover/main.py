from utils.preprocessor import preprocess
from utils.parser import parse, split
from utils.renamer import rename_predicates


def main():
    c_file = 'stack_fbp.c'

    # 1.1 standardize get the ast of the program
    standard_c_file = preprocess(c_file)

    # 1.2 rename the predicates in the original file
    renamed_c_file = rename_predicates(standard_c_file, '_fbp')

    # 1.3 extract the definition of non-functions and functions of the renamed program
    renamed_non_funcs, renamed_func = split(renamed_c_file)

    print('hello')


if __name__ == "__main__":
    main()
