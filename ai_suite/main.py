from LLM_handler import handle_LLM
from RAG import BestRAG
from utils import *
from lib_extractor import *
from configs import *


# This function can query multiple LLM models.
# Please specify the input folder, output folder and prompt in configs.py
def main():
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

    rel_input_files = get_rel_input_files(base_input_folder)

    for rel_input_file in rel_input_files:
        # get the program and included programs of the input file
        input_file = os.path.join(base_input_folder, rel_input_file)
        input_folder = os.path.dirname(input_file)

        with open(input_file, 'r') as file:
            input_program = file.read()

        results = read_included_lib_files(default_lib_files, input_folder, input_file, lib_folder)

        # try on each model
        for model in models:
            output_program = handle_LLM(input_program, prompt, prompt_type, rag, model)

            # write the output program into the output folder
            new_base_output_folder = os.path.join(base_output_folder, model)
            output_file = os.path.join(new_base_output_folder, rel_input_file)

            output_folder = os.path.dirname(output_file)
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
