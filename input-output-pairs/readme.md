This folder stores the input-output pairs as test cases for prompt engineering. The output is the verifast benchmark files (listed [here](https://docs.google.com/document/d/1xChFtlseYdnfJKehhrdEoeKIBxl0KIvL6Xrhy4Bnkqw/edit)) that should capture the functional behavior and pass the verification; The input files have 3 types (`.n` for natural language, `.m` for mathematical proof, and `.w` for weaker version) and they test the ability of LLM to generate specifications.

Note that not all output files can pass the verification on [verifast](https://github.com/verifast/verifast/tree/master) with the default option. They are placed in different sub directories based on their errors:

* `verified` stores the input-output pairs whose output files can be verified by verifast with the default option, where `verified/linked` stores the ones that can be both verified and linked, while `verifast/unlinked` stores the ones that can only be verified but not linked.
* `unverified` stores the input-output pairs whose output files cannot be verified by verifast with the  default option (e.g., not adding `-disable_overflow_check` or `-fno-strict-aliasing`). Here, those files are categorized by their errors in the verification (e.g., arithmetic overflow, failed condition).



For more details, please see the analysis in [the note](https://docs.google.com/document/d/1hataiIXApiVoAv6aGjb5syemPWZtXNn_xuhOJaKq_gE/edit#heading=h.vda9kzkqqiqw) and [the spreadsheet](https://docs.google.com/spreadsheets/d/1qlsn6ucidcVfpnqH8Llz0IyjPbDzY2GB_oTlsazi-wU/edit?gid=0#gid=0).

