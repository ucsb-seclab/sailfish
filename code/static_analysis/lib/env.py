import os
import sys
from enum import IntEnum


# Define error codes
class Error(IntEnum):
    ENV_VAR_NOT_SET = 1
    FILE_NOT_FOUND = 2


def check_env_var(env_var):
    # Check if environment variable is set
    try:
        env_val = os.environ[env_var]
        return env_val
    except KeyError as ke:
        print("[*] Set and export " + env_var + " environment variable")
        sys.exit(Error.ENV_VAR_NOT_SET)
