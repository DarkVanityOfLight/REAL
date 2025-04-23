from pysmt.operators import new_node_type

# Define a new node, our ramsey quantifier
RAMSEY_QUANTIFIER_NAME = "Ramsey"
RAMSEY_NODE_TYPE = new_node_type(None, RAMSEY_QUANTIFIER_NAME.upper())
