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

Also don't forget to add API-KEYS to `configs/API-Keys.json` and add google account credentials to `configs/credentials.json`.

Now, run

```bash
python main.py
```




