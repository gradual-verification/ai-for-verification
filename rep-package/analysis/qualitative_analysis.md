The procedure of qualitative analysis

# Workflow

In qualitative analysis, we first check whether functional behavior (FB) is prevserved in precondition&postcondition and source code for each file; Then, we iteratively categorize the errors and fix them in the output file; Finally, we check the convention on the source code or specifications that don't have error in the output file.

<img src="imgs/workflow.png" alt="workflow" style="zoom: 33%;" />

# Coding

Definition of Coding, includes the coding for functional behavior preservation, errors and convention.

## Functional Behavior Preservation

We need to assign code to two components in the output about whether they preserve function behavior, and those two components are Precondition&postcondition and source code.

Here we show the coding for Precondition&postcondition, and the one for source code is similar.

- Preserved: For all functions, the intention of the function expressed in precondition&postcondition in the output is equivalent to the intention of the function expressed in the precondition&postcondition or natural language comment in the input.
- (only) Strengthened: (Other than the case of preserved) There exists some function, the intention of the function expressed in precondition&postcondition in the output implies the intention of the function expressed in the precondition&postcondition or natural language comment in the input.
- (only) Weakened: (Other than the case of preserved and strengthened) There exists some function, the intention of the function expressed in precondition&postcondition in the output is implied by the intention of the function expressed in the precondition&postcondition or natural language comment in the input.
- Other cases: Not defined

## Error code

We divide the errors based on whether the error occurred is about proving. So they are divided into compilation errors (not about proving) and verification errors (about proving).

### Compilation Error

These errors represent “parse errors” in Verifast, which are basically errors that the VeriFast tool cannot interpret the code. This could be due to syntax issues such as missing semicolons, incorrect brackets, invalid keywords, or other structural errors that prevent verification. To better represent the compilation errors, we have the following subcodes:

- Specification out-of-position: This subcode represents situations where the specifications are not present at the correct location and are misplaced within the output file, resulting in parse error. Common cases are the precondition, postcondition or loop invariant is not at the right position.
- Syntax error: the error happens during the parsing stage 
- Include or Type Check error: This subcode represents errors that arise due to GPT hallucinating variables, predications or function calls, due to which fails the include or type check stage. The error commonly happens during the include stage or type check stage.

### Verification Error

The error occurred is about failing to prove a condition. Based on the component (e.g., precondition, postcondition, …) that the fix is on, the errors include:

- Incorrect precondition/postcondition
- Incorrect predicate definition
- Incorrect predicate usage: e.g., adding/deleting/changing open/close/assert/leak of predicate in function body.
- Incorrect lemma definition
- Incorrect lemma usage: e.g., adding/deleting/changing lemma in function body
- Incorrect loop invariant: the content of loop invariant is modified to fix the error.
- Others: including the source code is modified, the built-in statement (e.g., open_struct) is added.

## Convention code

After modifying the output file and making it verify, we can inspect the unmodified specifications and source code in the output file to see whether they have any conventional code. We have codes:

- Redundant: the condition in the spec, after being removed, doesn’t affect the verification. 
- Ambiguous: the specification’s name doesn't show the specification’s intention.

# Analysis

The data analysis is stored in `qualitative_analysis.xlsx`, where the data and analysis of each benchmark is stored in each subsheet, and the aggregated result is stored in subsheet `statistics` and `final_table`.