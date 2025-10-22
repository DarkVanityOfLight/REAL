from ramsey_elimination.formula_utils import int_vector, real_vector
from ramsey_elimination.mixed_elimination import eliminate_mixed_ramsey_from_separated, full_mixed_ramsey_elimination
from ramsey_extensions.shortcuts import *

ELIMINATION_FUNC = eliminate_mixed_ramsey_from_separated
BENCHMARK_ARGS = {
    "benchmark_program": [(1000, )]
}

def benchmark_program(dim: int):
    x1_r = real_vector('x1_r', dim)
    x1_i = int_vector('x1_i', dim)
    x2 = int_vector('x2', dim)
    y1_r = real_vector('y1_r', dim)
    y1_i = int_vector('y1_i', dim)
    y2 = int_vector('y2', dim)

    f1 = And([And(GE(x1_r[i], Real(0)), GT(x1_r[i], Real(1)), GE(y1_r[i], Real(0)), LT(y1_r[i], Real(1))) for i in range(dim)])
    f2 = And([Or(GT(x1_i[i], Int(0)), And(Equals(x1_i[i], Int(0)), GT(x1_r[i], Real(0)))) for i in range(dim)])
    f3 = And([GT(x2[i], Int(0)) for i in range(dim)])

    g = []
    for i in range(dim):
        g1 = And(Equals(Times(Int(2), y1_i[i]), x1_i[i]), GE(Times(Real(2), y1_r[i]), Plus(x1_r[i], Real(1))))
        g2 = And(Equals(Times(Int(2), y1_i[i]), Plus(x1_i[i], Int(1))), GE(Times(Real(2), y1_r[i]), x1_r[i]))
        g3 = GE(Times(Int(2), y1_i[i]), Plus(x1_i[i], Int(2)))
        g.append(Or(g1,g2,g3))

    f4 = And(g)
    f5 = And([LE(y2[i], Minus(x2[i], x1_i[i])) for i in range(dim)])
    f = And(f1,f2,f3,f4,f5)

    return Ramsey(x1_i +x1_r, y1_i+y1_r, f)


def benchmark_finite_duration_scheduling_mixed(valid_durations: list):
    """
    A scheduling problem where start times are real but task durations are
    integers chosen from a small, pre-defined set of valid options.
    """
    s_real = real_vector("s", 2)  # s[0] for task 1, s[1] for task 2
    d_int = int_vector("d", 2)    # d[0] for task 1, d[1] for task 2

    # Auxiliary real variables for the durations to keep atoms pure
    d_real = real_vector("d_real", 2)

    # Bridge for task 1's duration
    bridge1_disjuncts = []
    for dur in valid_durations:
        d = And(Equals(d_int[0], Int(dur)), Equals(d_real[0], Real(dur)))
        bridge1_disjuncts.append(d)
    f_bridge1 = Or(bridge1_disjuncts)

    # Bridge for task 2's duration
    bridge2_disjuncts = []
    for dur in valid_durations:
        d = And(Equals(d_int[1], Int(dur)), Equals(d_real[1], Real(dur)))
        bridge2_disjuncts.append(d)
    f_bridge2 = Or(bridge2_disjuncts)

    # Pure real constraints for scheduling logic
    f_real_constraints = And(s_real[0] >= Real(0), s_real[1] >= Real(0))
    # Overlap condition: s1 < s2 + d2 AND s2 < s1 + d1
    f_real_overlap = And(s_real[0] < s_real[1] + d_real[1],
                        s_real[1] < s_real[0] + d_real[0])

    f = And(f_bridge1, f_bridge2, f_real_constraints, f_real_overlap)

    # Define x and y vectors for Ramsey based on the two tasks
    x = [s_real[0], d_int[0]]
    y = [s_real[1], d_int[1]]
    return Ramsey(x, y, f)
