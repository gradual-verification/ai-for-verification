About how to run the script to use LLM to generate output file.

1. Install `python3` and `python3-openai`.
2. Add `OPENAI_API_KEY` into environmental variable.
3. Specify the GPT model (i.e., `GPT_MODEL`), path of the folder of input files (i.e., `TEST_FOLDER_PATH`) and path of the folder of results (i.e., `RESULT_FOLDER_PATH`).
4. Run `python3 basic_prompting.py` and `python3 CoT_prompting.py`.