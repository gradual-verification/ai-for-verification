from http.client import responses

import aisuite as ai

from RAG import BestRAG
from configs import RAG_TOP_N, temperature, program_typename, tutorial_typename
from utils import PromptType


# This function interacts with LLM.
# It returns the text of output program from LLM.
def handle_LLM(prompt: str, input_text: str, lib_contents: str, prompt_type: PromptType, rag: BestRAG, model: str) -> str:
    # retrieve example for RAG
    examples = ""
    flag_cutoff = False
    if prompt_type.is_RAG():
        rag_type = "sparse" if prompt_type == PromptType.RAG_SPARSE else "dense"

        program_responses = rag.search(input_text, rag_type, program_typename, RAG_TOP_N)
        tutorial_responses = rag.search(input_text, rag_type, tutorial_typename, 5)
        for responses in [tutorial_responses, program_responses]:
            for response in responses:
                results = response[1]
                for result in results:
                    if len(examples) + len(result.payload["text"]) > 300000:
                        flag_cutoff = True
                        break
                    else:
                        examples += result.payload["text"] + "\n\n------------------\n\n"

                if flag_cutoff:
                    break


    full_response = query_LLM(prompt, input_text, lib_contents, examples, model)
    program = get_code(full_response)

    return program


# Given the prompt, input text, included lib content, few-shot examples and model name,
# this function queries LLM and return the output.
def query_LLM(prompt: str, input_text: str, lib_contents: str, examples: str, model: str) -> str:
    client = ai.Client()

    content = prompt + "\n\n---------------------- Input file ----------------------\n\n" + \
              input_text + "\n\n---------------------- Included libraries ----------------------\n\n" + lib_contents
    if examples != "":
        content = content + "\n\n---------------------- Examples/tutorials ----------------------\n\n" + examples

    messages = [
        {"role": "system", "content": "You are a helpful assistant."},
        {"role": "user", "content": content}
    ]

    # consider o3 specially for temperature
    kwargs = {
        "model": model,
        "messages": messages,
    }
    if model.lower() != "openai:o3":
        kwargs["temperature"] = temperature

    response = client.chat.completions.create(**kwargs)
    full_output = response.choices[0].message.content
    return full_output

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