from pysmt.formula import FormulaManager
from pysmt.fnode import FNodeContent

from RamseyQuantors.fnode import ExtendedFNode
from RamseyQuantors.operators import RAMSEY_NODE_TYPE


class ExtendedFormulaManager(FormulaManager):
    """
    FormulaManager extension to support Ramsey quantifiers.

    Bound variables are passed in the payload as two equal-length tuples.
    """

    def __init__(self, env=None):
        super().__init__(env)

    def create_node(self, node_type, args, payload=None):
        """
        Create or retrieve a cached ExtendedFNode with given type, args, and payload.
        """
        content = FNodeContent(node_type, args, payload)
        if content in self.formulae:
            return self.formulae[content]

        node = ExtendedFNode(content, self._next_free_id)
        self._next_free_id += 1
        self.formulae[content] = node
        self._do_type_check(node)
        return node

    def Ramsey(self, vargroup1, vargroup2, formula):
        """
        Constructs a Ramsey quantifier node:
            Ramsey(vars1, vars2). formula(vars1 + vars2)

        Args:
            vargroup1 (Sequence[FNode]): First group of bound variables.
            vargroup2 (Sequence[FNode]): Second group of bound variables.
            formula (FNode): Boolean formula over bound variables.

        Returns:
            FNode: A RAMSEY quantifier node.

        Raises:
            ValueError: If variable groups differ in length.
        """
        # Empty first group => no quantification
        if not vargroup1:
            return formula

        if len(vargroup1) != len(vargroup2):
            raise ValueError(
                f"RAMSEY quantifier requires equal-length variable groups: "
                f"got {len(vargroup1)} and {len(vargroup2)}"
            )

        payload = (tuple(vargroup1), tuple(vargroup2))
        return self.create_node(
            node_type=RAMSEY_NODE_TYPE,
            args=(formula,),
            payload=payload
        )
