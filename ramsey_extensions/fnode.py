from typing import Self, Tuple
from pysmt.fnode import FNode
import pysmt.environment

import ramsey_extensions.smtlib.printers
from ramsey_extensions.operators import MOD_NODE_TYPE, RAMSEY_NODE_TYPE


class ExtendedFNode(FNode):
    """
    Extended FNode with support for the Ramsey quantifier.

    Adds utilities to identify and extract bounded variables.
    """

    def is_ramsey(self) -> bool:
        """Return True if this node is a Ramsey quantifier."""
        return self.node_type() == RAMSEY_NODE_TYPE

    def is_quantifier(self) -> bool:
        """Return True if this node is any quantifier (exists, forall, or Ramsey)."""
        return self.is_exists() or self.is_forall() or self.is_ramsey()

    def quantifier_vars(self) -> Tuple[Self] | Tuple[Tuple[Self, ...], Tuple[Self, ...]]:
        """
        Return a tuple of bound variables for this quantifier.

        For Ramsey, returns the two variable groups.
        For exists/forall, returns the single payload of variables.
        """
        if not self.is_quantifier():
            raise AssertionError("Node is not a quantifier")

        payload = self._content.payload

        # For standard quantifiers, payload is a sequence of FNode
        return tuple(payload)

    def is_mod(self) -> bool:
        """Return True if this node is a Modulo operator."""
        return self.node_type() == MOD_NODE_TYPE

    def __mod__(self, right):
        return self._apply_infix(right, _mgr().Mod, _mgr().BVURem)


    def to_smtlib(self, daggify=True):
        """Returns a Smt-Lib string representation of the formula.

        The daggify parameter can be used to switch from a linear-size
        representation that uses 'let' operators to represent the
        formula as a dag or a simpler (but possibly exponential)
        representation that expands the formula as a tree.

        See :py:class:`SmtPrinter`
        """
        return ramsey_extensions.smtlib.printers.to_smtlib(self, daggify)


def _env():
    """Aux function to obtain the environment."""
    return pysmt.environment.get_env()


def _mgr():
    """Aux function to obtain the formula manager."""
    return pysmt.environment.get_env().formula_manager
