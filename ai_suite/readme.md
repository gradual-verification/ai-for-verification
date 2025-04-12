This is the infrastructure to interact with LLMs on verifying VeriFast programs.

# Run

In current directory, create `venv` 

```bash
python3 -m venv .venv
source .venv/bin/activate
```

Then install dependencies:

```
pip install aisuite pydantic docstring_parser vertexai
```

Also don't forget to put API-KEYS in environmental variables. For example, in `/etc/profile`,

```
#open-ai
export OPENAI_API_KEY="XXX"
#deepseek
export DEEPSEEK_API_KEY="XXX"
#claude
export ANTHROPIC_API_KEY="XXX"
#gemini
export GEMINI_API_KEY="XXX"
#groq
export GROQ_API_KEY="XXX"
#mistral
export MISTRAL_API_KEY="XXX"
```

Now, run

```bash
python main.py
```




