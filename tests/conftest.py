import sys
import os

from pysmt.shortcuts import get_env
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from pysmt.environment import pop_env
import pytest
from ramsey_extensions.environment import push_ramsey


@pytest.fixture(autouse=True)
def cleanup():
    pop_env()
    push_ramsey()
    get_env().enable_infix_notation = True
