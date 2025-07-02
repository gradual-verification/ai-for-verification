from LLM_handler import handle_LLM
from RAG import BestRAG
from utils import *
from lib_extractor import *
from configs import *

def main():
    # preparations: environmental variables
    old_env = save_env_var()
    modify_env_var()

    prompt_type = PromptType.from_string(prompt_type_name)

    rag = BestRAG(
        url=os.environ["qdrant_url"],
        api_key=os.environ["qdrant_api_key"],
        collection_name=collection_name
    )

    if prompt_type.is_RAG() and store_embedding:
        rag.store_KB_embeddings(KB_folder)
    elif prompt_type.is_RAG() and delete_embedding:
        rag.delete_collection()
    else:
        evaluate(prompt_type, rag)

    restore_env_var(old_env)


# This function can query multiple LLM models.
# Please specify the input folder, output folder and prompt in configs.py
def evaluate(prompt_type: PromptType, rag: BestRAG):
    prompt = prompt_type.get_prompt()
    rel_input_files = get_rel_input_files(base_input_folder)

    for rel_input_file in rel_input_files:
        # get the program and included programs of the input file
        input_file = os.path.join(base_input_folder, rel_input_file)
        input_folder = os.path.dirname(input_file)

        with open(input_file, "r") as file:
            input_program = file.read()

        # get the content of included lib files
        lib_contents = read_included_lib_files(default_lib_files, input_folder, input_file, lib_folder)

        # try on each model
        for model in models:
            output_program = handle_LLM(prompt, input_program, lib_contents, prompt_type, rag, model)

            # write the output program into the output folder
            new_base_output_folder = os.path.join(base_output_folder, model + "_" + prompt_type_name + "_" + split_type)
            output_file = os.path.join(new_base_output_folder, rel_input_file)

            output_folder = os.path.dirname(output_file)
            os.makedirs(output_folder, exist_ok=True)
            with open(output_file, "w") as file:
                file.write(output_program)

            print("Finish " + model + " on " + rel_input_file + "\n")


if __name__ == "__main__":
    main()
