from io import StringIO

import pysmt.operators as op
from pysmt.environment import get_env
from pysmt.walkers import TreeWalker, DagWalker, handles
from pysmt.utils import quote
from pysmt.smtlib.printers import SmtDagPrinter, SmtPrinter, write_annotations, write_annotations_dag

class ExtendedSmtPrinter(SmtPrinter):

    def __init__(self, stream, annotations=None):
        super().__init__(stream, annotations)

    def walk_mod(self, formula): return self.walk_nary(formula, "mod")

class ExtendedSmtDagPrinter(SmtDagPrinter):

    def __init__(self, stream, template=".def_%d", annotations=None):
        super().__init__(stream, template, annotations)

    def walk_mod(self, formula, args):
        return self.walk_nary(formula, args, "mod")

def to_smtlib(formula, daggify=True):
    """Returns a Smt-Lib string representation of the formula.

    The daggify parameter can be used to switch from a linear-size
    representation that uses 'let' operators to represent the
    formula as a dag or a simpler (but possibly exponential)
    representation that expands the formula as a tree.

    See :py:class:`SmtPrinter`
    """
    buf = StringIO()
    p = None
    if daggify:
        p = ExtendedSmtDagPrinter(buf)
    else:
        p = ExtendedSmtPrinter(buf)
    p.printer(formula)
    res = buf.getvalue()
    buf.close()
    return res
