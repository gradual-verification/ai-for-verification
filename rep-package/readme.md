This folder contains the data and documentation for the evaluation of paper [Evaluating the Ability of Large Language Models to Generate Verifiable Specifications in VeriFast](https://arxiv.org/abs/2411.02318), where

* `raw_benchmark/`: stores the original benchmark programs of VeriFast, and its `readme.md` shows how to find our benchmark.
* `IO-pairs/`: stores 21 input-output pairs of our benchmarks, and its `readme.md` shows how to get each output file and 3 input files.
* `scripts/`: stores the 2 scripts to do prompt engineering (basic prompting and chain of thought), and its `readme.md` shows how to run them.
* `raw-pairs/`: stores the raw output of GPT-4o for 21 IO-pairs with 2 prompting methods.
* `analysis/`: stores the documentation and data of qualitative analysis. Here, `qualitative_analysis.md` stores the workflow and coding for qualitative analysis; `qualitative_analysis.xlsx` stores the detailed steps of analysis for each benchmark; `result_basic_gpt-4o/` and  `result_CoT_gpt-4o/` stores the fixed (i.e., verifiable) output files for each benchmark.