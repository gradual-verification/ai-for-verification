from LLM_handler import handle_LLM
from RAG import BestRAG
from utils import *

models = ["google:gemini-2.5-pro-preview-03-25", "google:gemini-2.0-flash", "openai:gpt-4.5-preview", "openai:o1", "openai:o3-mini", "openai:gpt-4o",
        "deepseek:deepseek-chat", "deepseek:deepseek-reasoner",
        "anthropic:claude-3-7-sonnet-20250219", "anthropic:claude-3-5-sonnet-20241022", "anthropic:claude-3-5-haiku-20241022",
        "groq:llama-3.3-70b-versatile", "groq:llama-3.1-8b-instant",
        "mistral:codestral-latest", "mistral:codestral-2405"]

# This function can query multiple LLM models.
# Please specify the input file, output folder and prompt in main() function.
def main():
    input_file = "input/stack_values_nl.c"
    KB_folder = "KB"
    output_folder = "output"

    prompt = f"You are an expert VeriFast programmer, your task is that for the C code below, modify it to include a formal code verification in Verifast that verifies correctly. \
                Please just show one code block with the complete code and specification to be verified, in the format of ```c CODE and SPEC ```."
    prompt_type = PromptType.BASIC

    # preparations: environmental variables, knowledge base for RAG, reading program
    old_env = save_env_var()
    modify_env_var()

    rag = BestRAG(
        url="https://85f59506-74d0-43cc-adf1-0c64033be499.us-east4-0.gcp.cloud.qdrant.io:6333",
        api_key="eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJhY2Nlc3MiOiJtIn0.pv84dpuUrh50MBE-XGuQ9SIzTblyCNa1Ug8ar1WuMFY",
        collection_name="LLM4SL"
    )
    if prompt_type.is_RAG():
        rag.store_KB_embeddings(KB_folder)

    with open(input_file, 'r') as file:
        input_program = file.read()

    # try on each model
    for model in models:
        output_program = handle_LLM(input_program, prompt, prompt_type, rag, model)
        output_file = os.path.join(output_folder, model + ".c")

        os.makedirs(output_folder, exist_ok=True)
        with open(output_file, 'w') as file:
            file.write(output_program)

        print("Finish " + model + "\n")

    # finish
    if prompt_type.is_RAG():
        rag.delete_KB_embeddings(KB_folder)
    restore_env_var(old_env)


if __name__ == '__main__':
    main()
