from pysmt.environment import Environment, push_env
from pysmt.smtlib.script import SmtPrinter
from pysmt.substituter import MGSubstituter

from RamseyQuantors.operators import RAMSEY_NODE_TYPE
from RamseyQuantors.printers import ExtendedSerializer
from RamseyQuantors.substituter import ExtendedMGSubstituter

from .type_checker import ExtendedTypeChecker
from .formula import ExtendedFormulaManager

class RamseyEnvironment(Environment):
    TypeCheckerClass = ExtendedTypeChecker
    FormulaManagerClass = ExtendedFormulaManager
    HRSerializerClass = ExtendedSerializer
    SubstituterClass = ExtendedMGSubstituter

    def __init__(self):
        super().__init__()

def push_ramsey():
    env = RamseyEnvironment()
    push_env(env)
