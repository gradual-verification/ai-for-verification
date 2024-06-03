import os
#### look at https://github.com/openai/openai-python to install OpenAI Python API library if first time use
from openai import OpenAI

#### DEFAULT SETTINGS, change it to your own setting ###
# TODO: your api key for chatgpt
API_KEY = ""
# the question that you want to ask ChatGPT
GPT_PROMPT = f"Analyze this C code for concurrency, recursivity, memory safety, and give a summary:"
# the code folder path that you want to ask CHATGPT for analyse
FOLDER_PATH = './verifast_examples_56/'
# chatgot model, all models are listed here https://platform.openai.com/docs/models
GPT_MODEL = 'gpt-3.5-turbo'

# Function definitions here (read_files_and_count_lines, analyze_code, etc.)
def read_files_and_count_lines(directory):
    data = {}
    for filename in os.listdir(directory):
        if filename.endswith(".c"):
            path = os.path.join(directory, filename)
            with open(path, 'r', encoding='utf-8') as file:
                content = file.read()
                lines = content.count('\n') + 1  # Counting lines
            data[filename] = {'content': content, 'lines': lines}
    return data

def analyze_code(content):    
    client = OpenAI(
        api_key=API_KEY,
    )

    chat_completion = client.chat.completions.create(
        messages=[
            {"role": "system", "content": "You are a helpful assistant."},
            {"role": "user", "content": GPT_PROMPT + f"\n\n{content}"}

        ],
        model="gpt-3.5-turbo",
    )
    print(chat_completion)
    return chat_completion.choices[0].message.content

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

def main(directory):
    files_data = read_files_and_count_lines(directory)
    for filename, info in files_data.items():
        content = info['content']
        info['analysis'] = analyze_code(content)
        file_info = {
            'filename': filename,
            'lines': info['lines'],
            'analysis': info['analysis']
        }
        write_analysis_to_markdown(file_info, directory)
        print(f"Analysis for {filename} written to {os.path.splitext(filename)[0]}.md")

if __name__ == "__main__":
    directory = FOLDER_PATH
    main(directory)
