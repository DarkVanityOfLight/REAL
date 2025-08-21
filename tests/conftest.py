import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

from pysmt.environment import pop_env
import pytest
from ramsey_extensions.environment import push_ramsey


@pytest.fixture(autouse=True)
def cleanup():
    pop_env()
    push_ramsey()
