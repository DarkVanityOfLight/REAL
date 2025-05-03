from typing import Self, Tuple
from pysmt.fnode import FNode
import pysmt.environment

from RamseyQuantors.operators import MOD_NODE_TYPE, RAMSEY_NODE_TYPE


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

    def quantifier_vars(self) -> Tuple[Self, ...]:
        """
        Return a tuple of bound variables for this quantifier.

        For Ramsey, returns concatenation of the two variable groups.
        For exists/forall, returns the single payload of variables.
        """
        if not self.is_quantifier():
            raise AssertionError("Node is not a quantifier")

        payload = self._content.payload
        if self.is_ramsey():
            left_vars, right_vars = payload  # two tuples of FNode
            return tuple(left_vars) + tuple(right_vars)

        # For standard quantifiers, payload is a sequence of FNode
        return tuple(payload)

    def is_mod(self) -> bool:
        """Return True if this node is a Modulo operator."""
        return self.node_type() == MOD_NODE_TYPE

    def __mod__(self, right):
        return self._apply_infix(right, _mgr().Mod, _mgr().BVURem)


def _env():
    """Aux function to obtain the environment."""
    return pysmt.environment.get_env()


def _mgr():
    """Aux function to obtain the formula manager."""
    return pysmt.environment.get_env().formula_manager
