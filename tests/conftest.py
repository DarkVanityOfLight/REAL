import sys
import os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

import pytest
from ramsey_extensions.environment import push_ramsey


@pytest.fixture(scope="session", autouse=True)
def push_ramsey_once():
    push_ramsey()
