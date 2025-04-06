import re
import subprocess

# Given the name of a file (code in C and spec in VeriFast),
# this function standardize its format to make code declaration and spec in one line.
# It writes the new program into a file and returns its filename.
def preprocess(c_file: str) -> str:
    std_c_file = 'standard_' + c_file

    # standardize the format of source code and spec
    standardize_code(c_file, std_c_file)
    standardize_spec(std_c_file, std_c_file)

    return std_c_file


# Given the name of a file and the name of a new file,
# this function uses clang-format to standardize the code in the file and write it into the new file.
def standardize_code(c_file: str, std_c_file: str):
    with open(std_c_file, 'w') as output_file:
        subprocess.run(['clang-format', c_file], stdout = output_file)

# Given the name of a file, and the name of a new file.
# this function uses regex to make its specification in one line, and write the result to the new file.
def standardize_spec(c_file: str, std_c_file: str):
    with open(c_file, 'r') as input_file:
        c_text = input_file.read()

    # extract content within /*@ ... @*/
    matches = re.findall(r'/\*@(.+?)@\*/', c_text, re.DOTALL)

    for match in matches:
        # process each match
        lines = [line.strip() for line in match.strip().split('\n') if line.strip()]
        single_line_spec = '//@ ' + ' '.join(lines)

        # replace the original multi-line block with single-line version
        original = f'/*@{match}@*/'
        c_text = c_text.replace(original, single_line_spec)

    with open(std_c_file, 'w') as output_file:
        output_file.write(c_text)