import re
import sys

def remove_comments_inside_functions(c_program: str) -> str:
    # Define a regular expression to match function bodies
    function_pattern = r'\{(?:[^{}]|(?:\{[^{}]*\}))*\}'

    # Find all function bodies
    function_bodies = re.findall(function_pattern, c_program, flags=re.DOTALL)
    
    # Iterate over function bodies and remove comments
    cleaned_program = c_program
    for body in function_bodies:
        # Remove comments inside the function body
        cleaned_body = re.sub(r'(?<!\\)//.*?(?=\n|$)', '', body, flags=re.DOTALL)
        cleaned_program = cleaned_program.replace(body, cleaned_body)

    return cleaned_program

def main(input_file: str, output_file: str):
    # Read the input file
    with open(input_file, 'r') as file:
        c_program = file.read()

    # Clean the program
    cleaned_program = remove_comments_inside_functions(c_program)

    # Write the cleaned program to the output file
    with open(output_file, 'w') as file:
        file.write(cleaned_program)

if __name__ == '__main__':
    if len(sys.argv) != 3:
        print("Usage: python3 remove_comments.py <input_file> <output_file>")
        sys.exit(1)

    input_file = sys.argv[1]
    output_file = sys.argv[2]
    main(input_file, output_file)

