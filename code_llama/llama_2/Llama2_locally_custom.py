from langchain import PromptTemplate, LLMChain
from langchain.llms import CTransformers
import time

B_INST, E_INST = "[INST]", "[/INST]"
B_SYS, E_SYS = "<<SYS>>\n", "\n<</SYS>>\n\n"

CUSTOM_SYSTEM_PROMPT = "You are an advanced assistant that provides translation from English to French"
instruction = "Convert the following text from English to French: \n\n {text}"

SYSTEM_PROMPT = B_SYS + CUSTOM_SYSTEM_PROMPT + E_SYS

template = B_INST + SYSTEM_PROMPT + instruction + E_INST

print(template)
prompt = PromptTemplate(template=template, input_variables=["text"])

llm = CTransformers(model=r'models\llama-2-7b-chat.ggmlv3.q4_0.bin',  # Use raw string to avoid escape sequence issues
                    model_type='llama',
                    config={'max_new_tokens': 128,
                            'temperature': 0.01}
                   )
LLM_Chain = LLMChain(prompt=prompt, llm=llm)

# Start timer
start = time.time()

# Run the chain
response = LLM_Chain.run("How are you")

# End timer
end = time.time()

print(response)
print(f"Time to retrieve response: {end - start}")
