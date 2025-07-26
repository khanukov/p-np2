"""Estimate the circuit capacity drop for small parameters.

The script has two modes:

* **Direct enumeration** (default):
  For each ``k`` up to ``max_k`` it enumerates all circuits that *exactly*
  use ``k`` input bits and at most ``max_gates`` logical gates.  The total
  count of such circuits is compared to ``2^{k}``, yielding the exponent
  ``alpha`` in the inequality ``#circuits ≤ 2^{(1-α) k}``.

* **Prefix enumeration** (``--prefix N``):
  For a fixed overall input size ``N`` it counts, for each prefix length
  ``k`` from ``1`` to ``N``, how many circuits share the same left ``k``-bit
  prefix of the truth table.  This supports the "canonical circuits" approach
  from roadmap B‑3 by estimating how many circuits actually depend on a
  chosen subset of inputs.

Both modes rely on the enumeration helpers from ``lemma_b_search.py`` so the
logic stays consistent with the other experiments.
"""

import argparse
from math import log2
from collections import Counter
from lemma_b_search import function_counts, prefix_capacity_drop


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


def prefix_drop(n: int, max_gates: int) -> list[tuple[int, int, float]]:
    """Measure prefix capacity drop for circuits on ``n`` inputs.

    This wraps ``prefix_capacity_drop`` from ``lemma_b_search`` and simply
    forwards its output.
    """

    return prefix_capacity_drop(n, max_gates)


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
    parser.add_argument(
        "--prefix", type=int, metavar="N", default=0,
        help=(
            "measure prefix capacity drop for circuits on N inputs "
            "instead of enumerating by k"
        ),
    )
    args = parser.parse_args()

    if args.prefix > 0:
        results = prefix_drop(args.prefix, args.max_gates)
        for k, count, alpha in results:
            print(f"prefix k={k}: max_count={count}, alpha={alpha:.4f}")
    else:
        results = capacity_drop(args.max_k, args.max_gates)
        for k, count, alpha in results:
            print(f"k={k}: circuits={count}, alpha={alpha:.4f}")
