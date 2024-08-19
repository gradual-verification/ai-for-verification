import os
#### look at https://github.com/openai/openai-python to install OpenAI Python API library if first time use
from openai import OpenAI
########### this script will read the contents of both .h and SUFFIX_USE file under each subdirectory of FOLDER_PATH, and combine them together
########### to ask CHATGPT

#### DEFAULT SETTINGS, change it to your own setting ###
# TODO: your api key for chatgpt
API_KEY = ""
# the question that you want to ask ChatGPT
GPT_PROMPT = f"I provide .c file and the references .h file for this .c, could you generate the verifast verification only for the .c file for me?"
# the code folder path that you want to ask CHATGPT for analyse, should be full path
FOLDER_PATH = ''
# chatgot model, all models are listed here https://platform.openai.com/docs/models
GPT_MODEL = 'gpt-4-turbo'
# which suffix of c file to read
SUFFIX_USE = '_w.c'
conversation_history = [{"role": "system", "content": "You are a helpful assistant."}]

client = OpenAI(
    api_key=API_KEY,
)
# Function definitions here (read_files_and_count_lines, analyze_code, etc.)
def read_files_and_count_lines(directory):
    data = {}
    for filename in os.listdir(directory):
        if filename.endswith(SUFFIX_USE):
            path = os.path.join(directory, filename)
            with open(path, 'r', encoding='utf-8') as file:
                content = file.read()
                lines = content.count('\n') + 1  # Counting lines
            data[filename] = {'content': content, 'lines': lines}
    return data

def get_header_files_content(directory):
    header_content = ""
    for filename in os.listdir(directory):
        if filename.endswith(".h"):
            path = os.path.join(directory, filename)
            with open(path, 'r', encoding='utf-8') as file:
                header_content += file.read() + "\n"
    return header_content


def analyze_code(header_content, content):
    global conversation_history
    user_message = {
        "role": "user", 
        "content": GPT_PROMPT + f"\n\nthe .h header contents include {header_content} \n\nthe .c contents is: {content}"
    }
    conversation_history.append(user_message)
    
    chat_completion = client.chat.completions.create(
        messages=conversation_history,
        model=GPT_MODEL,
    )
    
    assistant_message = chat_completion.choices[0].message.content
    conversation_history.append({"role": "assistant", "content": assistant_message})
    
    return assistant_message

def write_analysis_to_markdown(file_info, directory):
    filename = file_info['filename']
    base_filename = os.path.splitext(filename)[0]
    markdown_filename = os.path.join(directory, f"{base_filename}.md")

    with open(markdown_filename, 'w', encoding='utf-8') as md_file:
        md_file.write(f"# Analysis for {filename}\n\n")
        md_file.write(f"## Lines of Code\n")
        md_file.write(f"{file_info['lines']}\n\n")
        md_file.write(f"## Analysis Results\n")
        md_file.write(f"```\n{file_info['analysis']}\n```\n")


def analyze_subdirectory(subdirectory):
    header_content = get_header_files_content(subdirectory)
    files_data = read_files_and_count_lines(subdirectory)
    for filename, info in files_data.items():
        info['analysis'] = analyze_code(header_content, info['content'])
        file_info = {
            'filename': filename,
            'lines': info['lines'],
            'analysis': info['analysis']
        }
        write_analysis_to_markdown(file_info, subdirectory)
        print(f"Analysis for {filename} written to {os.path.splitext(filename)[0]}.md")
        
def main(base_directory):
    # If there are subdirectories, process each one
    if any(os.path.isdir(os.path.join(base_directory, entry)) for entry in os.listdir(base_directory)):
        for subdirectory_name in os.listdir(base_directory):
            subdirectory_path = os.path.join(base_directory, subdirectory_name)
            if os.path.isdir(subdirectory_path):
                analyze_subdirectory(subdirectory_path)
    elif (os.path.isdir(base_directory)):
        # If no subdirectories, process the base directory itself
        analyze_subdirectory(base_directory)

if __name__ == "__main__":
    directory = FOLDER_PATH
    main(directory)
