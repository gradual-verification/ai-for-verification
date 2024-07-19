the python code uses the prompt engineering and then run the verifast to verify the result and then send the verified result to the GPT again to let the GPT fix the code it generated.

steps:
Start

	1. Prompt Engineering in Python: Generate a Python code prompt.
	2. Run VeriFast: Execute VeriFast to verify the result.
	3. Verification Successful?
		Yes: Proceed to the next step.
		No: Go back to step 2 and re-engineer the prompt.
	4. Send Verified Result to GPT: Submit the verified result to GPT for review.
	5. GPT Fixes Code: GPT modifies and fixes the code.
End

flowchart::

 Start
     |
     v
  Prompt Engineering in Python
     |
     v
  Run VeriFast
     |
     v
Verification Successful?
  /        \
Yes       No
  |         |
  v         |
Send Verified Result to GPT
            |
  GPT Fixes Code
     |
     v
    End


