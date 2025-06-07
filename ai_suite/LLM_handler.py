import aisuite as ai

from RAG import BestRAG
from configs import RAG_TOP_N
from utils import PromptType


# This function interacts with LLM.
# It returns the text of output program from LLM.
def handle_LLM(input_text: str, prompt: str, prompt_type: PromptType, rag: BestRAG, model: str) -> str:
    # retrieve example for RAG
    examples = ""
    if prompt_type.is_RAG():
        rag_type = "sparse" if prompt_type == PromptType.RAG_SPARSE else "dense"
        responses = rag.search(input_text, rag_type, RAG_TOP_N)
        for response in responses:
            results = response[1]
            for result in results:
                examples += result.payload["text"] + "\n\n-------------------------------\n\n"

    full_response = query_LLM(input_text, prompt, examples, model)
    program = get_code(full_response)

    return program


# Given the input text, prompt and model name,
# this function queries LLM and return the output.
def query_LLM(input_text: str, prompt: str, examples: str, model: str) -> str:
    client = ai.Client()
    if examples != "":
        content = prompt + "\n\n" + input_text + "\n\n--------Examples--------\n\n:" + examples
    else:
        content = prompt + "\n\n" + input_text

    messages = [
        {"role": "system", "content": "You are a helpful assistant."},
        {"role": "user", "content": content}
    ]

    response = client.chat.completions.create(
        model=model,
        messages=messages,
        temperature=1
    )

    return response.choices[0].message.content


# Given an output text from LLM,
# this function gets the code and return it.
def get_code(output: str) -> str:
    lines = output.split('\n')
    filtered_lines = []
    inside_code_block = False

    # extract lines that are inside the code block
    for line in lines:
        # check if the line marks the beginning or end of a code block
        if (not inside_code_block) and ('```c' in line.strip()):
            inside_code_block = True
            continue
        elif inside_code_block and ('```' in line.strip()):
            inside_code_block = False
            continue

        if inside_code_block:
            filtered_lines.append(line)

    filtered_text = '\n'.join(filtered_lines)
    return filtered_text