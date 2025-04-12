from LLM_handler import handle_LLM
from utils import *

models = ["openai:gpt-4.5-preview", "openai:o1", "openai:o3-mini", "openai:gpt-4o",
        "deepseek:deepseek-chat", "deepseek:deepseek-reasoner",
        "anthropic:claude-3-7-sonnet-20250219", "anthropic:claude-3-5-sonnet-20241022", "anthropic:claude-3-5-haiku-20241022",
        "google:gemini-2.5-pro-preview-03-25", "google:gemini-2.0-flash",
        "groq:llama-3.3-70b-versatile", "groq:llama-3.1-8b-instant",
        "mistral:codestral-latest", "mistral:codestral-2405"]


# This function can query multiple LLM models.
# Please specify the input file, output folder and prompt in main() function.
def main():
    input_file = "stack_values/stack_values_fbp.c"
    output_folder = "output/"

    prompt = f"You are an expert Verifast programmer, your task is that for the C code below, modify it to include a formal code verification in Verifast that verifies correctly. \
                Please just show one code block with the complete code and specification to be verified, in the format of ```c CODE and SPEC ```."

    my_models = ["google:gemini-2.5-pro-preview-03-25", "google:gemini-2.0-flash"]


    old_env = save_env_var()
    modify_env_var()

    with open(input_file, 'r') as file:
        input_program = file.read()

    for model in my_models:
        output_program = handle_LLM(input_program, prompt, model)

        output_file = os.path.join(output_folder, model + ".c")

        os.makedirs(output_folder, exist_ok=True)
        with open(output_file, 'w') as file:
            file.write(output_program)

        print("Finish " + model + "\n")

    restore_env_var(old_env)


if __name__ == '__main__':
    main()
