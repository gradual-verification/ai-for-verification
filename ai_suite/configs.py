import textwrap

# the name of LLMs to be tested
models = ["google:gemini-2.5-pro-preview-03-25", "google:gemini-2.0-flash",
        "openai:gpt-4.5-preview", "openai:o1", "openai:o3-mini", "openai:gpt-4o",
        "deepseek:deepseek-chat", "deepseek:deepseek-reasoner",
        "anthropic:claude-3-7-sonnet-20250219", "anthropic:claude-3-5-sonnet-20241022", "anthropic:claude-3-5-haiku-20241022",
        "groq:llama-3.3-70b-versatile", "groq:llama-3.1-8b-instant",
        "mistral:codestral-latest", "mistral:codestral-2405"]
# models = ["openai:gpt-4o-2024-08-06"]

# the type of prompt, can be "BASIC", "COT", "RAG_SPARSE", "RAG_DENSE"
prompt_type_name = "RAG_SPARSE"

# "non-split" or "split" on functional granularity
split_type = "non-split"

# the suffix of input files to be evaluated
input_suffixes = ("fbp.c", "fb.c", "nl.c")

# options to store and delete the vector embedding of context in RAG
store_embedding = False
delete_embedding = False

# the number of returned context in RAG
RAG_TOP_N = 20

# the temperature of LLM
temperature = 0

# the name of collection in vector database to store knowledge base
collection_name = "LLM4SL"

# the name of lib files being implicitly included
default_lib_files = ["prelude.h", "prelude_core.gh", "list.gh"]

# the folder that stores the lib files
lib_folder = "lib/"

# the folder that stores the input files
base_input_folder = "../input-output-pairs/full/DIY/"

# the folder that stores knowledge base
KB_folder = "KB"

# the folder that stores the output of LLM
base_output_folder = "output1/"

# prompts for different types
basic_prompt = textwrap.dedent("""\
    You are an expert VeriFast programmer.
    Your task is that for the input C file below, please include
    a formal VeriFast verification to make sure all functions
    annotated with:

        // TODO: make this function pass the verification

    are verified correctly. The included library files are also provided.

    Please show a single code block with the complete C code and its
    specification, in exactly this format:

    ```c
    <CODE and SPEC>
    ```
    """)

CoT_prompt = textwrap.dedent("""\
    You are an expert VeriFast programmer.
    Your task is that for the input C file below, please include
    a formal VeriFast verification to make sure all functions
    annotated with:

        // TODO: make this function pass the verification

    are verified correctly, following the steps:

    Step 1: Write precondition and postcondition for each function. Following the sub-steps:
        1.1 Generate a precondition that represents constraints on the input behavior of the function as specified in the input program \
            either in natural language comments before the function or as a precondition between the function declaration and function body. \
            Make sure that any predicates or data types in the generated precondition are declared.
        1.2 Place the newly generated precondition between the function declaration and the function body.
        1.3 Go back to the newly generated precondition and add additional specifications as needed to verify memory safety of the function.
        1.4 Go back to the newly generated precondition and add additional specifications as needed to verify integers stay within their bounds in the function.
        1.5 Generate a postcondition that represents constraints on the output behavior of the function as defined in the input program \
            either in natural language comments before the function or as a postcondition between the function declaration and function body. \
            Make sure that any predicates or data types in the generated postcondition are declared.
        1.6 Place the newly generated postcondition between the function declaration and the function body (after the previously generated precondition).
        1.7 Go back to the newly generated postcondition and add additional specifications to verify memory safety after this function is called.
        1.8 Go back to the newly generated postcondition and add additional specifications to verify that integers stay within their bounds after this function is called.

    Step 2: Write loop invariant if the function has a loop. Following the sub-steps:
        2.1 Generate a loop invariant that specifies the properties that hold at each loop iteration.
        2.2 Place the newly generated loop invariant between the loop head and loop body.
        2.3 Go back to the newly generated loop invariant and add checks to confirm safe memory access and bounded integers in each loop iteration.
        2.4 Go back to the newly generated loop invariant and make sure it can prove the conditions after the loop.

    Step 3: Add other auxiliary specifications such as open, close and lemma.
    To be specific, those statements allow the information in the proved conditions and source code to prove the next condition,
    where the conditions include the precondition of a function call, the access to memory location, loop invariant and the postcondition.
    For example, use `open` statement to unfold a predicate into several conditions in its body;
    Use `close` statement to fold several conditions into a whole predicate;
    Apply lemmas to transform conditions into equivalent forms for proof.

    The included library files are also provided. Please show a single code block with the complete C code and its specification, in exactly this format:

    ```c
    <CODE and SPEC>
    ```
    """)

RAG_prompt = textwrap.dedent("""\
    You are an expert VeriFast programmer.
    Your task is that for the input C file below, please include
    a formal VeriFast verification to make sure all functions
    annotated with:

        // TODO: make this function pass the verification

    are verified correctly. The included library files and some examples/tutorials about VeriFast are also provided.

    Please show a single code block with the complete C code and its
    specification, in exactly this format:

    ```c
    <CODE and SPEC>
    ```
    """)