"""Compute a simple collision entropy metric for small circuit classes.

For a given ``n`` and ``max_gates`` the script enumerates all distinct Boolean
functions computable with at most that many gates (using AND/OR/NOT).
Treating this set of functions as a uniform distribution, the collision entropy
``H_2`` equals ``log2(|F|)``.  Optionally the script can list the number of
circuits computing each truth table instead of printing the entropy.  Use
``--list-counts`` to output counts, ``--descending`` to sort by frequency, and
``--top`` to limit the number of rows printed.
"""

import argparse
from math import log2
from lemma_b_search import all_functions, function_counts


def log2_unique_functions(n: int, max_gates: int) -> float:
    """Return ``log2`` of the number of distinct functions enumerated."""
    funcs = all_functions(n, max_gates)
    total = len(funcs)
    if total == 0:
        return 0.0
    return log2(total)


def collision_entropy_by_circuit(n: int, max_gates: int) -> float:
    """Compute collision entropy weighting each circuit equally."""
    counts = function_counts(n, max_gates)
    total = sum(counts.values())
    if total == 0:
        return 0.0
    sum_sq = sum(c * c for c in counts.values())
    return -log2(sum_sq / (total * total))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Measure log2 of distinct functions for small circuits"
    )
    parser.add_argument(
        "n", type=int, nargs="?", default=3,
        help="number of input bits (default: 3)")
    parser.add_argument(
        "max_gates", type=int, nargs="?", default=2,
        help="maximum number of gates (default: 2)")
    parser.add_argument(
        "--circuits", action="store_true",
        help="weight entropy by individual circuits")
    parser.add_argument(
        "--list-counts", action="store_true",
        help="print table counts instead of entropy")
    parser.add_argument(
        "--descending", action="store_true",
        help="sort counts from largest to smallest")
    parser.add_argument(
        "--top", type=int, default=0,
        help="limit output to the first N rows when listing counts")
    args = parser.parse_args()

    if args.list_counts:
        counts = function_counts(args.n, args.max_gates)
        width = 1 << args.n
        items = list(counts.items())
        if args.descending:
            items = sorted(items, key=lambda x: (-x[1], x[0]))
        else:
            items = sorted(items)
        if args.top:
            items = items[: args.top]
        for tbl, cnt in items:
            bits = format(tbl, f"0{width}b")
            print(f"{bits} {cnt}")
    else:
        if args.circuits:
            h2 = collision_entropy_by_circuit(args.n, args.max_gates)
        else:
            h2 = log2_unique_functions(args.n, args.max_gates)
        print(f"n={args.n}, gates<={args.max_gates}, H2={h2:.4f}")
