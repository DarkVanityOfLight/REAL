from pysmt.environment import Environment, push_env
from pysmt.smtlib.script import SmtPrinter

from RamseyQuantors.operators import RAMSEY_NODE_TYPE
from RamseyQuantors.printers import ExtendedSerializer

from .type_checker import ExtendedTypeChecker
from .formula import ExtendedFormulaManager

class RamseyEnvironment(Environment):
    TypeCheckerClass = ExtendedTypeChecker
    FormulaManagerClass = ExtendedFormulaManager
    HRSerializerClass = ExtendedSerializer

    def __init__(self):
        super().__init__()

def push_ramsey():
    env = RamseyEnvironment()
    push_env(env)
