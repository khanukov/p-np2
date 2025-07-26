"""Estimate the circuit capacity drop for small parameters.

For each ``k`` up to the chosen ``max_k`` the script enumerates all circuits
with at most ``max_gates`` gates that depend on exactly ``k`` input bits.
The total count of such circuits is compared to ``2^{k}``, yielding the
exponent ``alpha`` in the inequality ``#circuits <= 2^{(1-alpha) * k}``.
The enumeration uses the helper ``function_counts`` from ``lemma_b_search.py``
so that the logic stays consistent with the other experiments.
"""

import argparse
from math import log2
from collections import Counter
from lemma_b_search import function_counts


def capacity_drop(max_k: int, max_gates: int) -> list[tuple[int, int, float]]:
    """Enumerate circuits for ``k`` inputs and report the drop exponent.

    Returns a list of triples ``(k, count, alpha)`` where ``count`` is the total
    number of circuits found and ``alpha = 1 - log2(count) / k``.
    ``alpha`` may be negative when there are more than ``2^k`` circuits, but the
    value still illustrates the trend for small ``k``.
    """
    results = []
    for k in range(1, max_k + 1):
        counts: Counter[int] = function_counts(k, max_gates)
        total = sum(counts.values())
        if k == 0:
            alpha = 0.0
        else:
            alpha = 1.0 - (log2(total) / k)
        results.append((k, total, alpha))
    return results


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Estimate the circuit capacity drop for small k",
    )
    parser.add_argument(
        "max_k", type=int, nargs="?", default=6,
        help="largest input size to enumerate (default: 6)")
    parser.add_argument(
        "max_gates", type=int, nargs="?", default=3,
        help="maximum number of gates per circuit (default: 3)")
    args = parser.parse_args()

    results = capacity_drop(args.max_k, args.max_gates)
    for k, count, alpha in results:
        print(f"k={k}: circuits={count}, alpha={alpha:.4f}")
