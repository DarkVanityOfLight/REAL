from pysmt.operators import new_node_type
import pysmt.operators

# Define a new node, our ramsey quantifier
RAMSEY_QUANTIFIER_NAME = "Ramsey"
RAMSEY_NODE_TYPE = new_node_type(None, RAMSEY_QUANTIFIER_NAME.upper())
pysmt.operators.QUANTIFIERS = pysmt.operators.QUANTIFIERS.union([RAMSEY_NODE_TYPE])
pysmt.operators.__OP_STR__[RAMSEY_NODE_TYPE] = "RAMSEY"


# Define the modulo operation
MOD_NAME = "mod"
MOD_NODE_TYPE = new_node_type(None, MOD_NAME.upper())
pysmt.operators.__OP_STR__[MOD_NODE_TYPE] = "MOD"
#TODO: Add to IRA maybe?

TOINT_NODE_TYPE = new_node_type(None, "TOINT")
pysmt.operators.__OP_STR__[TOINT_NODE_TYPE] = "TOINT"
