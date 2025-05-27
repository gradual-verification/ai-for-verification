import os
import json
from enum import Enum

class PromptType(Enum):
    BASIC = 1
    COT = 2
    RAG_SPARSE = 3
    RAG_DENSE = 4

    def is_RAG(self):
        return self == PromptType.RAG_SPARSE or self == PromptType.RAG_DENSE


def save_env_var() -> dict:
    return os.environ.copy()


def modify_env_var():
    os.environ["GOOGLE_PROJECT_ID"] = "gen-lang-client-0570172807"
    os.environ["GOOGLE_REGION"] = "us-central1"
    os.environ["GOOGLE_APPLICATION_CREDENTIALS"] = "./configs/credentials.json"
    load_API_keys()


def load_API_keys():
    with open("configs/API-keys.json", "r") as f:
        keys = json.load(f)

    for name, value in keys.items():
        os.environ[name] = value


def restore_env_var(old_env: dict):
    os.environ.clear()
    os.environ.update(old_env)
