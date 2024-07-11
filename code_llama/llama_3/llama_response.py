import subprocess
import time

CUSTOM_SYSTEM_PROMPT = (
    "You are a VeriFast expert. After reading the code, provide the natural language specifications. "
    "Please write the specifications inside the code without deleting the function body."
)
instruction = (
    "please write the specification into the code like this: #include <stdint.h> #include <stdlib.h> #include <string.h> #include \"arraylist.h\""
    "struct arraylist {{ void **data;int size;int capacity;}};"
    "/*@predicate arraylist(struct arraylist *a; list<void*> vs) ="
    "a->data |-> ?data &*& a->size |-> ?size &*& a->capacity |-> ?capacity &*& malloc_block_arraylist(a) &*& malloc_block_pointers(data, capacity) &*& data[0..size] |-> vs &*& data[size..capacity] |-> _;@*/"
    "struct arraylist *create_arraylist() //@ requires true;"
    "//@ ensures arraylist(result, nil);"
    "{{struct arraylist *a = malloc(sizeof(struct arraylist)); void *data = 0;if(a == 0) abort();a->size = 0;data = malloc(100 * sizeof(void*));if(data == 0) abort();a->data = data;a->capacity = 100;return a; }}"
    "\n\n and here is the code: {code}"
)

def read_code_from_path(file_path):
    with open(file_path, 'r') as file:
        code = file.read()
    return code

code_file_path = r"D:\_purdue\692\ai-for-verification\ai-for-verification\mimic-user-behavior\arraylist_z\arraylist_n.c"
code_content = read_code_from_path(code_file_path)

def run_llama2(prompt):
    try:
        print("Starting the llama3 model...")
        process = subprocess.Popen(
            ['ollama', 'run', 'llama3'],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            shell=True
        )
        
        print("Waiting for the model to initialize...")
        time.sleep(10)
        
        print(f"Sending prompt: {prompt}")
        stdout, stderr = process.communicate(input=prompt + '\n', timeout=30)
        
        print("Output:", stdout)
        if stderr:
            print("Errors:", stderr)
        
        return stdout.strip()
    
    except subprocess.TimeoutExpired:
        process.kill()
        stdout, stderr = process.communicate()
        print("Process timed out.")
        print("Output:", stdout)
        print("Errors:", stderr)
    except Exception as e:
        print(f"An error occurred: {e}")

if __name__ == '__main__':
    user_prompt = f"{CUSTOM_SYSTEM_PROMPT}\n\n{instruction.format(code=code_content)}"
    response = run_llama2(user_prompt)
    print("Model Response:", response)
