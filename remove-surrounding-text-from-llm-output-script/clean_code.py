import sys
import os

def remove_annotations(input_text):
    # Split the input text into lines
    lines = input_text.split('\n')

    # Initialize an empty list to store the filtered lines
    filtered_lines = []

    # Flag to track if we are inside a code block
    inside_code_block = False

    for line in lines:
        # Check if the line marks the beginning or end of a code block
        if line.strip() == '```c':
            inside_code_block = True
            continue
        elif line.strip() == '```':
            inside_code_block = False
            continue

        # Only add lines that are inside the code block
        if inside_code_block:
            filtered_lines.append(line)

    # Join the filtered lines back into a single string
    filtered_text = '\n'.join(filtered_lines)
    return filtered_text

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 script.py input_file")
        return

    input_file = sys.argv[1]

    # Generate the output file name
    base_name, ext = os.path.splitext(input_file)
    output_file = f"{base_name}_clean{ext}"

    # Read the input file
    with open(input_file, 'r') as file:
        input_text = file.read()

    # Process the input text
    filtered_text = remove_annotations(input_text)

    # Write the filtered text to the output file
    with open(output_file, 'w') as file:
        file.write(filtered_text)

    print(f"Output written to {output_file}")

if __name__ == "__main__":
    main()

