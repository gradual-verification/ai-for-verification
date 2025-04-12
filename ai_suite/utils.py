import os

def save_env_var() -> dict:
    return os.environ.copy()


def modify_env_var():
    os.environ["GOOGLE_PROJECT_ID"] = "gen-lang-client-0570172807"
    os.environ["GOOGLE_REGION"] = "us-central1"
    os.environ["GOOGLE_APPLICATION_CREDENTIALS"] = "./configs/credentials.json"


def restore_env_var(old_env: dict):
    os.environ.clear()
    os.environ.update(old_env)
