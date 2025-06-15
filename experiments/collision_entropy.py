"""Compute a simple collision entropy metric for small circuit classes.

For a given ``n`` and ``max_gates`` the script enumerates all distinct Boolean
functions computable with at most that many gates (using AND/OR/NOT).  Treating
this set of functions as a uniform distribution, the collision entropy ``H_2``
equals ``log2(|F|)``.  We therefore return the base-2 logarithm of the number of
unique functions.
"""

import argparse
from math import log2
from lemma_b_search import all_functions


def log2_unique_functions(n: int, max_gates: int) -> float:
    """Return ``log2`` of the number of distinct functions enumerated."""
    funcs = all_functions(n, max_gates)
    total = len(funcs)
    if total == 0:
        return 0.0
    return log2(total)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Measure log2 of distinct functions for small circuit class")
    parser.add_argument(
        "n", type=int, nargs="?", default=3,
        help="number of input bits (default: 3)")
    parser.add_argument(
        "max_gates", type=int, nargs="?", default=2,
        help="maximum number of gates (default: 2)")
    args = parser.parse_args()
    h2 = log2_unique_functions(args.n, args.max_gates)
    print(f"n={args.n}, gates<={args.max_gates}, H2={h2:.4f}")
