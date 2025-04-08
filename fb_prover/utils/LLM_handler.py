import subprocess

from openai import OpenAI

# APT_KEY is in environmental variable
# chatgpt model, all models are listed here https://platform.openai.com/docs/models
# options: gpt-3.5-turbo, gpt-4o, o1
GPT_MODEL = 'o1'

ANNOTATE_PROMPT = f"You are an expert VeriFast programmer. Now I want to use VeriFast as an entailment prover for separation logic. \
Given a VeriFast lemma that checks whether its precondition (after requires) entails the postcondition (after ensures), \
please add auxiliary specifications (such as open/close/lemma) inside the lemma body to make it pass the verification. \
Note that PLEASE DON'T MODIFY the predicates, lemma's precondition, lemma's postcondition or add source code in the lemma. \
You can modify the signature of lemma to solve the syntax error. \
If you don't need to add auxiliary spec, you can add nothing. \
Please just show one code block with the complete code and specification to be verified, in the format of ```c CODE and SPEC ```."

FIX_PROMPT = f"You are an expert VeriFast programmer. Now I want to fix the verification error in the code below.\
Note that PLEASE DON'T MODIFY the predicates, lemma's precondition, lemma's postcondition or add source code in the lemma. \
You can modify the signature of lemma to solve the syntax error. \
If you don't need to add auxiliary spec, you can add nothing. \
Please just show one code block with the complete code and specification to be verified, in the format of ```c CODE and SPEC ```."

# Given the prompt, input and extra content,
# this function queries LLM and return the output.
def query_LLM(prompt: str, input: str, extra_content: str) -> str:
    client = OpenAI()
    full_input = prompt + f'\n\n```\n{input}```' + f'\n\nHere are some examples:\n\n{extra_content}'

    chat_completion = client.chat.completions.create(
        messages = [
            {'role': 'system', 'content': 'You are a helpful assistant.'},
            {'role': 'user', 'content': full_input}

        ],
        model = GPT_MODEL,
    )
    return chat_completion.choices[0].message.content


# Given an output text from LLM,
# this function gets the VeriFast code and return.
def get_verifast_code(output: str) -> str:
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


# Given the name of file of helper lemma and some examples,
# this function leverages LLM to add auxiliary specifications to prove such lemma,
# and it writes the new lemma into the same file
def annotate_lemma(lemma_file: str, example_text: str):
    with open(lemma_file, 'r') as file:
        lemma_text = file.read()

    result_content = query_LLM(ANNOTATE_PROMPT, lemma_text, example_text)
    result_program = get_verifast_code(result_content)

    with open(lemma_file, 'w') as file:
        file.write(result_program)


# Given the path to a file of lemma and the max number of fixes,
# this function first verifies the lemma, and continues fixing & verifying
# until successfully verified or reaching the limit.
def verify_and_fix_lemma(lemma_file: str, max_fix_iter: int):
    # do the first verification
    verify_output = verify_lemma(lemma_file)
    is_verified = check_verified_success(verify_output)

    # fix and verify the lemma within the limit
    for i in range(max_fix_iter):
        if is_verified:
            break
        else:
            fix_lemma(lemma_file, verify_output)
            verify_output = verify_lemma(lemma_file)
            is_verified = check_verified_success(verify_output)

    return is_verified


# Given the path to a file of VeriFast lemma,
# this function verifies the lemma by using VeriFast and returns the output.
def verify_lemma(lemma_file: str) -> str:
    result = subprocess.run(['verifast', lemma_file], capture_output = True, text = True)
    return result.stdout


# Given the path to a file of VeriFast lemma and the output of VeriFast verifier,
# this function tries to fix the lemma by requesting LLM.
# it will write into the same file.
def fix_lemma(lemma_file: str, verify_output: str):
    with open(lemma_file, 'r') as file:
        lemma_text = file.read()

    result_content = query_LLM(FIX_PROMPT, lemma_text, verify_output)
    result_program = get_verifast_code(result_content)

    with open(lemma_file, 'w') as file:
        file.write(result_program)


# Given the output of VeriFast verifier,
# this function checks whether it means a successful verification.
def check_verified_success(output: str) -> bool:
    success_flag = '0 errors found'
    return success_flag in output