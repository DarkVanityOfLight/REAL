from pysmt.shortcuts import And, Equals, Exists, Or, Plus, Real, Symbol
from ramsey_elimination.formula_utils import real_vector
from ramsey_extensions.shortcuts import Ramsey


def benchmark_half_real(dim: int, bound: float):
    x = real_vector('a',dim)
    y = real_vector('b',dim)
    f = And([And(2*y[i] <= x[i],x[i] >= bound) for i in range(dim)])
    return Ramsey(x, y, f)

def benchmark_equal_exists_real(dim: int):
    x = real_vector('a', dim)
    y = real_vector('b', dim)
    z = real_vector('c', dim)
    f = And([And(x[i] < y[i], Equals(x[i], z[i])) for i in range(dim)])
    return Ramsey(x, y, Exists(z, f))


def benchmark_equal_free_real(dim: int):
    x = real_vector('a', dim)
    y = real_vector('b', dim)
    z = real_vector('c', dim)
    f = And([And(x[i] < y[i], Equals(x[i], z[i])) for i in range(dim)])
    return Ramsey(x, y, f)


def benchmark_dickson_real(dim: int):
    x = real_vector('a', dim)
    y = real_vector('b', dim)
    f = And([x[i] >= 0 for i in range(dim)])
    g = And(Or([y[i] < x[i] for i in range(dim)]),And([y[i] <= x[i] for i in range(dim)]))
    g = Or(g,And(Or([y[i] < x[i] for i in range(dim)]),Or([x[i] < y[i] for i in range(dim)])))
    f = And(f,g)
    return Ramsey(x, y, f)

def benchmark_sorted_chain_real(dim: int):
    """
    Constrains the vector y to be strictly sorted, where each element y[i]
    is also greater than the corresponding element x[i]. This creates a
    long chain of dependencies: x[i] < y[i] < y[i+1].
    """
    x = real_vector('a', dim)
    y = real_vector('b', dim)

    # Each element of y must be greater than the corresponding x element
    y_gt_x = [y[i] > x[i] for i in range(dim)]

    # The elements of y must be in strictly ascending order
    y_is_sorted = [y[i] < y[i+1] for i in range(dim - 1)]

    f = And(y_gt_x + y_is_sorted)
    return Ramsey(x, y, f)

def benchmark_average_real(dim: int):
    """
    Constrains each element of y to be greater than the average of all
    elements in x. This tests the handling of constraints that aggregate
    many variables together.
    """
    x = real_vector('a', dim)
    y = real_vector('b', dim)

    # To maintain linearity, we express the average as Sum(x) / dim
    # by multiplying the dimension on the other side.
    sum_x = Plus(x)

    # dim * y[i] > Sum(x) for all i
    f = And([dim * y[i] > sum_x for i in range(dim)])
    return Ramsey(x, y, f)

def benchmark_bounding_box_real(dim: int):
    """
    Constrains y to be inside a bounding box defined by two free vectors
    z1 and z2. The vector x is constrained to be strictly "below" this box.
    This tests chains of inequalities involving multiple free variables.
    f: x < z1 < y < z2
    """
    x = real_vector('a', dim)
    y = real_vector('b', dim)
    z1 = real_vector('c', dim)
    z2 = real_vector('d', dim)

    f = And([And(x[i] < z1[i], z1[i] < y[i], y[i] < z2[i]) for i in range(dim)])
    return Ramsey(x, y, f)

def benchmark_cyclic_dependency_real(dim: int):
    """
    Creates a cyclic dependency among the elements of y. Each y[i] is
    constrained by y[i-1], and y[0] is constrained by y[dim-1]. This
    can be challenging for propagation-based solvers.
    """
    x = real_vector('a', dim)
    y = real_vector('b', dim)

    # Standard forward chain: y[i] > x[i] + y[i-1]
    chain = [y[i] > x[i] + y[i-1] for i in range(1, dim)]

    # The cyclic link: y[0] is greater than the last element in the chain
    cycle_link = [y[0] > y[dim-1]]

    f = And(chain + cycle_link)
    return Ramsey(x, y, f)

def benchmark_midpoint_real(dim: int):
    """
    Constrains y to be the exact midpoint between x and a free vector z,
    under the condition that z is strictly greater than x in every dimension.
    This tests the solver's handling of equality constraints derived from
    linear expressions.
    """
    x = real_vector('a', dim)
    y = real_vector('b', dim)
    z = real_vector('c', dim)

    # Enforce that z is a distinct point, "above" x
    z_is_greater = And([z[i] > x[i] for i in range(dim)])

    # y[i] is the midpoint of x[i] and z[i], expressed as 2*y[i] = x[i] + z[i]
    midpoint_eq = And([Equals(Real(2) * y[i], x[i] + z[i]) for i in range(dim)])

    f = And(z_is_greater, midpoint_eq)
    return Ramsey(x, y, f)


def benchmark_average_eq_real(dim: int):
    """
    Constrains each element of y to be greater than the average of all
    elements in x. This tests the handling of constraints that aggregate
    many variables together.
    """
    x = real_vector('a', dim)
    y = real_vector('b', dim)

    # To maintain linearity, we express the average as Sum(x) / dim
    # by multiplying the dimension on the other side.
    sum_x = Plus(x)

    # dim * y[i] > Sum(x) for all i
    f = And([dim * y[i] >= sum_x for i in range(dim)])
    return Ramsey(x, y, f)
