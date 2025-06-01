# the name of LLMs to be tested
models = ["google:gemini-2.5-pro-preview-03-25", "google:gemini-2.0-flash",
        "openai:gpt-4.5-preview", "openai:o1", "openai:o3-mini", "openai:gpt-4o",
        "deepseek:deepseek-chat", "deepseek:deepseek-reasoner",
        "anthropic:claude-3-7-sonnet-20250219", "anthropic:claude-3-5-sonnet-20241022", "anthropic:claude-3-5-haiku-20241022",
        "groq:llama-3.3-70b-versatile", "groq:llama-3.1-8b-instant",
        "mistral:codestral-latest", "mistral:codestral-2405"]

# the name of lib files being implicitly included
default_lib_files = ["prelude.h", "prelude_core.gh", "list.gh"]

# the folder that stores the lib files
lib_folder = "lib/"

# the folder that stores the input files
base_input_folder = "../input-output-pairs/full/DIY/"

# the folder that stores knowledge base
KB_folder = "KB"

# the folder that stores the output of LLM
base_output_folder = "output/"

prompt = f"You are an expert VeriFast programmer, your task is that for the C code below, modify it to include a formal code verification in VeriFast that verifies correctly. \
                Please just show one code block with the complete code and specification to be verified, in the format of ```c CODE and SPEC ```."