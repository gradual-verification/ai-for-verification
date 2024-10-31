# Thank Marilyn and Zhaorui for this script

import os
import shutil
#### look at https://github.com/openai/openai-python to install OpenAI Python API library if first time use
from openai import OpenAI

#### DEFAULT SETTINGS, change it to your own setting ###
# APT_KEY is in environmental variable
# the question that you want to ask ChatGPT
# Chain of Thoughts (CoT) may break down the prompt into several steps
GPT_PROMPTs = [f"You are a Verifast expert programmer, do not delete the orginal code and just add accurate Verifast specifications to the C code below according to every function's description.",
               f"1. add the precondition and postcondition set to true to the main function, remove any other specifications added inside the main function",
               f"2. rewrite the code such that for every function and the main function, the precondition and the post condition is only between the function declaration and its contents",
               f"3. the preconditions and postconditions should be preceded by '//@' for all functions.",
               f"Please just show one code block with the complete code and specification to be verified, in the format of ```c CODE and SPEC ```."]
GPT_PROMPT = "\n".join(GPT_PROMPTs)
# chatgpt model, all models are listed here https://platform.openai.com/docs/models
# options: gpt-3.5-turbo, gpt-4o, o1-preview
GPT_MODEL = 'o1-preview'
# the code folder path that you want to ask CHATGPT for generating specification
TEST_FOLDER_PATH = '../../input-output-pairs/correct/'
# the result folder path that stores the output of CHATGPT for analysis
RESULT_FOLDER_PATH = f'../../input-output-pairs/result_CoT_{GPT_MODEL}/'


# Function definitions here (read_files_and_count_lines, analyze_code, etc.)

### In the given base directory for test files, read the information of the input test files and return it.
def read_files_and_count_lines(base_dir):
    # store the info of a test file: subdir name, file name, type, content and lines.
    data = {}
    for root, dirs, files in os.walk(base_dir):
        for file in files:
            if (file.endswith('.c') and
                (file[-4:-2] == "_n" or file[-4:-2] == "_m" or file[-4:-2] == "_w")):

                full_path = os.path.join(root, file)
                sub_dir = full_path.split(os.sep)[-2]
                type = file[-3:-2]

                with open(full_path, 'r', encoding='utf-8') as file_open:
                    content = file_open.read()
                    lines = content.count('\n') + 1  # Counting lines

                data[full_path] = {'subdir': sub_dir, 'file': file, 'type': type, 'content': content, 'lines': lines}
    return data


### Query the LLM by inputting the content, and (perhaps) choose the prompt by the type,
### and return the output from LLM
def query_LLM(content, type):
    client = OpenAI()

    chat_completion = client.chat.completions.create(
        messages=[
            # remove it since some models (e.g., o1-preview) don't support system role
            #{"role": "system", "content": "You are a helpful assistant."},
            {"role": "user", "content": GPT_PROMPT + f"\n\n{content}"}

        ],
        model=GPT_MODEL,
    )
    #print(chat_completion)
    return chat_completion.choices[0].message.content


### Filter the given text and get the verifast code.
def get_verifast_code(input_text):
    # Split the input text into lines
    lines = input_text.split('\n')

    # Initialize an empty list to store the filtered lines
    filtered_lines = []

    # Flag to track if we are inside a code block
    inside_code_block = False

    for line in lines:
        # Check if the line marks the beginning or end of a code block
        if (not inside_code_block) and ('```c' in line.strip()):
            inside_code_block = True
            continue
        elif inside_code_block and ('```' in line.strip()):
            inside_code_block = False
            continue

        # Only add lines that are inside the code block
        if inside_code_block:
            filtered_lines.append(line)

    # Join the filtered lines back into a single string
    filtered_text = '\n'.join(filtered_lines)
    return filtered_text


### Write the output file (both full and filtered) into the proper location in the base directory for output,
### based on the given file_info that contains subdir name, file name, type, content, lines and output.
### It returns the name of output file.
### If LLM doesn't return any code in the output (perhaps because it believes that the input is verified),
### then write the output with the input code.
def write_output(file_info, base_dir):
    sub_dir = file_info['subdir']
    filename = file_info['file']
    content = file_info['content']
    full_output = file_info['full_output']
    filtered_output = get_verifast_code(full_output)
    full_output_file = os.path.join(base_dir, sub_dir, f"full_{filename}.md")
    filtered_output_file = os.path.join(base_dir, sub_dir, f"{filename}")

    # write both the full output and the extracted output
    os.makedirs(os.path.dirname(full_output_file), exist_ok=True)
    with open(full_output_file, 'w', encoding='utf-8') as file_open:
        file_open.write(f"{full_output}\n")

    with open(filtered_output_file, 'w', encoding='utf-8') as file_open:
        if len(filtered_output) == 0:
            file_open.write(f"/*{full_output}*/\n{content}\n")
        else:
            file_open.write(f"{filtered_output}\n")

    return filtered_output_file


def main():
    files_data = read_files_and_count_lines(TEST_FOLDER_PATH)
    if os.path.exists(RESULT_FOLDER_PATH):
        shutil.rmtree(RESULT_FOLDER_PATH)

    # query llm for each input file and store the output file
    for _, info in files_data.items():
        content = info['content']
        type = info['type']

        llm_output = query_LLM(content, type)
        info['full_output'] = llm_output

        output_file = write_output(info, RESULT_FOLDER_PATH)
        print(f"Analysis for {info['file']} written to {output_file}")


if __name__ == "__main__":
    main()