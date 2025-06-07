import os
import json
from enum import Enum

class PromptType(Enum):
    BASIC = 1
    COT = 2
    RAG_SPARSE = 3
    RAG_DENSE = 4

    @classmethod
    def from_string(cls, name: str) -> "PromptType":
        try:
            return cls[name]
        except KeyError:
            raise ValueError(f"'{name}' is not a valid {cls.__name__}")

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


# get the relative path of input files
def get_rel_input_files(base_input_folder: str) -> list[str]:
    rel_input_files = []

    for dirpath, _, filenames in os.walk(base_input_folder):
        rel_dirpath = os.path.relpath(dirpath, base_input_folder)
        for fname in filenames:
            if fname.endswith(("fbp.c", "fb.c", "nl.c")):
                rel_fname = os.path.join(rel_dirpath, fname)
                rel_input_files.append(rel_fname)

    return rel_input_files