from langchain import PromptTemplate
from langchain.llms import CTransformers

# Use double backslashes
llm = CTransformers(model='models\\llama-2-7b-chat.ggmlv3.q4_0.bin',
                    model_type='llama')

template = """
I want you to act as a naming consultant for new companies.
What is a good name for a company that makes {product}?
"""

prompt = PromptTemplate.from_template(template)
print(prompt.format(product="colorful socks"))

print(llm(prompt.format(product="colorful socks")))
