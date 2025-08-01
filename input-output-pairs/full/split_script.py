import subprocess
import re
import argparse
import os

annotation = '// TODO: make this function pass the verification\n'

class Function:
    def __init__(self, name: str, start_line: int):
        self.name = name
        self.start_line = start_line
        self.end_line = -1
        self.code = ''
        self.func_calls = []


# find the line of the function/prototype/typedef declaration using ctags
def get_function_lines(filename):
    # Run ctags and get function name and line number
    result = subprocess.run(
        ['ctags', '-x', '--c-kinds=fpt', filename],
        stdout=subprocess.PIPE,
        universal_newlines=True
    )
    lines = result.stdout.strip().split('\n')

    functions = []
    for line in lines:
        parts = re.split(r'\s+', line)
        if len(parts) >= 3:
            name = parts[0]
            # the lines start from 0
            start_line = int(parts[2]) - 1
            func = Function(name, start_line)
            functions.append(func)

    # Sort by starting line
    functions.sort(key=lambda x: x.start_line)
    return functions


# find the start line for function&comment (starting from 0)
def find_final_start_line(lines, func_start_idx):
    i = func_start_idx - 1  # index in lines
    if i < 0 or '*/' not in lines[i]:
        return func_start_idx  # no comment block

    # Look upward for '/*'
    while i >= 0:
        if '/*' in lines[i]:
            return i
        i -= 1

    return func_start_idx  # fallback if start of comment not found


# extract the functions and their comment before them
def extract_functions_with_comments(filename):
    with open(filename) as f:
        all_lines = f.readlines()

    functions = get_function_lines(filename)

    # Find comment start
    for func in functions:
        comment_start_line = find_final_start_line(all_lines, func.start_line)
        func.start_line = comment_start_line

    # Find the end and code block of a function
    for i, func in enumerate(functions):
        # End line: 1 less than the start of next function, or end of file
        if i + 1 < len(functions):
            end_line = functions[i + 1].start_line - 1
        else:
            end_line = len(all_lines)

        func.end_line = end_line
        # Get function block with comment
        func.code = ''.join(all_lines[func.start_line : end_line + 1])

    # Find the function calls of each function
    for func in functions:
        extract_func_calls(func, functions)

    return functions


# extract the functions called by curr_func
# here I use simple texture search by "func_name("
def extract_func_calls(curr_func, functions):
    curr_func_name = curr_func.name
    curr_func_code = curr_func.code

    for func in functions:
        func_name = func.name
        if curr_func_name != func_name:
            if func_name in curr_func_code:
                curr_func.func_calls.append(func_name)


# extract the struct, predicate or fixpoint definitions before the first function
def extract_other_definition(filename, functions):
    if len(functions) == 0:
        print('No functions found for ' + filename)
        return ''

    with open(filename) as f:
        all_lines = f.readlines()

    first_func = functions[0]
    return ''.join(all_lines[0 : first_func.start_line])


# get the function calls that the curr_func depends on
def get_dependent_func_calls(functions, curr_func):
    dependent_func_calls = curr_func.func_calls.copy()

    while True:
        funcs_to_append = []
        for func_call1 in dependent_func_calls:
            match = next(filter(lambda f: f.name == func_call1, functions), None)
            # suppose the match always succeeds
            func1 = match
            if match is None:
                print("no")
            for func2 in func1.func_calls:
                if func2 not in dependent_func_calls and func2 not in funcs_to_append:
                    funcs_to_append.append(func2)

        if len(funcs_to_append) == 0:
            break
        else:
            dependent_func_calls.extend(funcs_to_append)

    rank = {f.name: f.start_line for f in functions}
    sorted_dependent_func_calls = sorted(dependent_func_calls, key=lambda f: rank.get(f, float('inf')))

    return sorted_dependent_func_calls


# split the functions for the given file in its directory
# and put those functions into new files in a newly created subdirectory.
def split_functions(dirpath, filename):
    base_filename, _ = os.path.splitext(filename)
    file_prefix, file_suffix = base_filename.rsplit('_', 1)

    file_full_path = os.path.join(dirpath, filename)
    subdir_full_path = os.path.join(dirpath, base_filename)

    os.makedirs(subdir_full_path, exist_ok=True)

    functions = extract_functions_with_comments(file_full_path)
    definition = extract_other_definition(file_full_path, functions)

    for func in functions:
        # write the definition, called functions and the function into a new file
        new_file_content = definition + '\n'

        dependent_funcs = get_dependent_func_calls(functions, func)

        for func_call in dependent_funcs:
            match = next(filter(lambda f: f.name == func_call, functions), None)
            if match:
                new_file_content += match.code + '\n'
        new_file_content += annotation + func.code

        new_filename = file_prefix + '_' + func.name + '_' + file_suffix + '.c'
        new_file_full_path = os.path.join(subdir_full_path, new_filename)

        with open(new_file_full_path, 'w') as f:
            f.write(new_file_content)


def main():
    parser = argparse.ArgumentParser(description='Extract functions and preceding comments from (fbp, fb, nl) C files in a directory')
    parser.add_argument('root_dir', help='The root directory of the C files')
    args = parser.parse_args()

    for dirpath, _, filenames in os.walk(args.root_dir):
        for filename in filenames:
            if filename.endswith('fbp.c') or filename.endswith('fb.c') or filename.endswith('nl.c'):
                split_functions(dirpath, filename)


if __name__ == "__main__":
    main()
