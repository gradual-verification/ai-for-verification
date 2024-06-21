import os
from openai import OpenAI

#### DEFAULT SETTINGS, change it to your own setting ###

# TODO: your api key for chatgpt
API_KEY = ""

# the question that you want to ask ChatGPT
GPT_PROMPT = f"you are an verifast expert, given those files, there are so many functions in the files, for those functions , the precondition and post condition have already been fully verified, now i want you to writ the inline statement such as the open and close"

# chatgpt model, all models are listed here https://platform.openai.com/docs/models
GPT_MODEL = 'gpt-4o'

# Output folder name
OUTPUT_FOLDER = 'analysis_output'


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


def analyze_code(content):    
    client = OpenAI(api_key=API_KEY)
    chat_completion = client.chat.completions.create(
        messages=[
            {"role": "system", "content": "You are a helpful assistant."},
            {"role": "user", "content": GPT_PROMPT + f"\n\n{content}"}
        ],
        model="gpt-4o",
    )
    print(chat_completion)
    return chat_completion.choices[0].message.content


def write_analysis_to_markdown(file_info, output_dir):
    filepath = file_info['path']
    filename = os.path.basename(filepath)
    base_filename = os.path.splitext(filename)[0]
    markdown_filename = os.path.join(output_dir, f"{base_filename}_modified.c")
    with open(markdown_filename, 'w', encoding='utf-8') as md_file:
        md_file.write(f"# Analysis for {filename}\n\n")
        md_file.write(f"## Analysis Results\n")
        md_file.write(f"```\n{file_info['analysis']}\n```\n")


def main():
    # Get the current working directory
    directory = os.getcwd()
    
    # Create output directory
    output_dir = os.path.join(directory, OUTPUT_FOLDER)
    os.makedirs(output_dir, exist_ok=True)
    
    files_data = read_files_and_count_lines(directory)
    for filename, info in files_data.items():
        content = info['content']
        info['analysis'] = analyze_code(content)
        file_info = {
            'filename': filename,
            'lines': info['lines'],
            'analysis': info['analysis'],
            'path': info['path']
        }
        write_analysis_to_markdown(file_info, output_dir)
        print(f"Analysis for {filename} written to {os.path.join(output_dir, f'{os.path.splitext(filename)[0]}_modified.c')}")


if __name__ == "__main__":
    main()

