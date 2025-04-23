from typing import Tuple
from pysmt.fnode import FNode

from RamseyQuantors.operators import RAMSEY_NODE_TYPE


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

    def quantifier_vars(self) -> Tuple[FNode, ...]:
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
