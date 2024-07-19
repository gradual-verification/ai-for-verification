import os
import subprocess
from openai import OpenAI
import stat

# TODO: your API key for ChatGPT
API_KEY = "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"

# The question that you want to ask ChatGPT
GPT_PROMPT = ("You are a verifast expert. Given these files, there are many functions in the files, "
              "for those functions, the precondition and post condition have already been fully verified. "
              "Now I want you to write the inline statement such as the open and close.")
              
GPT_PROMPT_error=("here is the error that after run the verifast, can you please change your code depend on th error message? ")

# ChatGPT model
GPT_MODEL = 'gpt-4o'

# Output folder name
OUTPUT_FOLDER = 'analysis_output'

verifast_binary = '/home/zhaorui/Desktop/verifast/verifast-21.04-328-g328e4c8f/bin/verifast'
verifast_result_folder = 'verifast-result'

def read_files_and_count_lines(directory):
    data = {}
    for root, _, files in os.walk(directory):
        for filename in files:
            if filename.endswith(".c") and "_n" in filename[:-2]:
                path = os.path.join(root, filename)
                with open(path, 'r', encoding='utf-8') as file:
                    content = file.read()
                    lines = content.count('\n') + 1  # Counting lines
                data[filename] = {'content': content, 'lines': lines, 'path': path}
    return data

def analyze_code(content,prompt):    
    client = OpenAI(api_key=API_KEY)
    chat_completion = client.chat.completions.create(
        messages=[
            {"role": "system", "content": "You are a helpful assistant."},
            {"role": "user", "content": GPT_PROMPT + f"\n\n{content}"}
        ],
        model=GPT_MODEL,
    )
    print(chat_completion)
    return chat_completion.choices[0].message.content

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

def write_analysis_to_markdown(file_info, output_dir):
    filepath = file_info['path']
    filename = os.path.basename(filepath)
    base_filename = os.path.splitext(filename)[0]
    markdown_filename = os.path.join(output_dir, f"{base_filename}_modified.c")
    uncleaned = file_info['analysis']
    filtered_analysis = remove_annotations(file_info['analysis'])

    with open(markdown_filename, 'w', encoding='utf-8') as md_file:
        if filtered_analysis:
            md_file.write(f"{filtered_analysis}")
        else:
            md_file.write(f"{uncleaned}")
            file_info['cleaned'] = False
    return markdown_filename, file_info

def run_verifast(verifast_binary, file_path):
    try:
        # Ensure the VeriFast binary has execute permissions
        os.chmod(verifast_binary, stat.S_IRWXU)
        
        result = subprocess.run([verifast_binary, file_path], capture_output=True, text=True)
        return result.stdout
    except Exception as e:
        return str(e)

def main():
    # Get the current working directory
    directory = os.getcwd()
    
    # Create output directory
    output_dir = os.path.join(directory, OUTPUT_FOLDER)
    verifast_dir = os.path.join(directory, verifast_result_folder)
    os.makedirs(output_dir, exist_ok=True)
    os.makedirs(verifast_dir, exist_ok=True)
    
    files_data = read_files_and_count_lines(directory)
    for filename, info in files_data.items():
        content = info['content']
        info['analysis'] = analyze_code(content,GPT_PROMPT)
        
        file_info = {
            'filename': filename,
            'lines': info['lines'],
            'analysis': info['analysis'],
            'path': info['path'],
            'cleaned': True,
            'cleaned_info': info['analysis'],
            'output_dir': output_dir,
            'verifast_result': 'error'
        }

        markdown_file_path, file_info = write_analysis_to_markdown(file_info, output_dir)
        
        # Run VeriFast analysis
        verifast_output = run_verifast(verifast_binary, markdown_file_path)
        verifast_result_path = os.path.join(verifast_dir, f"{file_info['filename']}_verifast_result.txt")
        with open(verifast_result_path, 'w', encoding='utf-8') as vf_file:
            vf_file.write(verifast_output)
        
        print(f"Analysis for {filename} written to {markdown_file_path}")
        print(f"VeriFast result for {filename} written to {verifast_result_path}")
        
        ##send to chat GPT again
        new_code_content=''
        if file_info['cleaned']:
        	new_code_content=file_info['cleaned_info']
        else: 
        	new_code_content=file_info['analysis']
        file_info['analysis'] = analyze_code(new_code_content,GPT_PROMPT_error)
        ##
        markdown_file_path, file_info = write_analysis_to_markdown(file_info, output_dir)
        
        verifast_output = run_verifast(verifast_binary, markdown_file_path)
        verifast_result_path = os.path.join(verifast_dir, f"{file_info['filename']}_verifast_result.txt")
        with open(verifast_result_path, 'w', encoding='utf-8') as vf_file:
            vf_file.write(verifast_output)
        
        print(f"Analysis for {filename} written to {markdown_file_path}")
        print(f"VeriFast result for {filename} written to {verifast_result_path}")
        	

if __name__ == "__main__":
    main()

