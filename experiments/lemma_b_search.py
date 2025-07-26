# Prototype tool to explore Lemma B (structural compression of small circuits)
# Enumerates all boolean functions computable by circuits up to a given size
# with inputs of size n, using AND/OR/NOT. For small n and gate count it
# exhaustively generates truth tables and measures the number of unique
# "left" and "right" halves when the truth table is split at position k.
# This is a toy experiment to gather data about possible rectangle covers.

"""Small enumeration tool used for Lemma B experiments.

The script enumerates all Boolean functions computable by circuits with a
bounded number of AND/OR/NOT gates on ``n`` inputs.  For each possible split of
the truth table into ``k`` left bits and ``n-k`` right bits, it reports the
  number of distinct left and right halves.
  This gives a rough upper bound on the size of a rectangular cover for the
  family of functions under consideration.

The original prototype had parameters ``n`` and ``max_gates`` hard-coded.  This
version accepts them via command-line options so that different settings can be
explored without editing the file.
"""

import argparse
import csv
from collections import Counter, defaultdict
from math import log2

# encode a boolean function on n inputs as an integer with 2**n bits


def variables(n):
    """Return list of truth tables for variables x0..x_{n-1}."""
    tables = []
    for i in range(n):
        table = 0
        for x in range(1 << n):
            bit = (x >> i) & 1
            table |= bit << x
        tables.append(table)
    return tables


def const_table(n, value):
    table = 0
    if value:
        table = (1 << (1 << n)) - 1
    return table


def all_functions(n, max_gates):
    """Return set of truth tables computed by circuits with <= max_gates."""
    base = set(variables(n)) | {const_table(n, 0), const_table(n, 1)}
    layers = [base]
    all_funcs = set(base)
    for g in range(1, max_gates + 1):
        new_set = set()
        # unary NOT from previous layer
        for f in layers[-1]:
            mask = (1 << (1 << n)) - 1
            new_set.add(mask ^ f)
        # binary AND/OR combining smaller circuits
        for i in range(g):
            for f1 in layers[i]:
                for f2 in layers[g - 1 - i]:
                    new_set.add(f1 & f2)
                    new_set.add(f1 | f2)
        layers.append(new_set)
        all_funcs.update(new_set)
    return all_funcs


def function_counts(n, max_gates):
    """Return a mapping of truth tables to the number of circuits computing
    them."""

    base = Counter()
    for tbl in variables(n):
        base[tbl] += 1
    base[const_table(n, 0)] += 1
    base[const_table(n, 1)] += 1
    layers = [base]
    total = Counter(base)
    mask = (1 << (1 << n)) - 1
    for g in range(1, max_gates + 1):
        new_counter = Counter()
        for f, cnt in layers[-1].items():
            new_counter[mask ^ f] += cnt
        for i in range(g):
            for f1, c1 in layers[i].items():
                for f2, c2 in layers[g - 1 - i].items():
                    new_counter[f1 & f2] += c1 * c2
                    new_counter[f1 | f2] += c1 * c2
        layers.append(new_counter)
        total += new_counter
    return total


def split_tables(funcs, n, k):
    """Split each table into left and right halves of ``2^k`` and
    ``2^(n-k)`` bits."""
    left_len = 1 << k
    left_mask = (1 << left_len) - 1
    left_set = set()
    right_set = set()
    for f in funcs:
        left = f & left_mask
        right = f >> left_len
        left_set.add(left)
        right_set.add(right)
    return len(left_set), len(right_set)


def _entropy(counts: Counter, total: int) -> float:
    """Shannon entropy of a discrete distribution with given counts."""
    h = 0.0
    for c in counts.values():
        p = c / total
        if p > 0:
            h -= p * log2(p)
    return h


def split_entropies(funcs, n, k):
    """Return ``H(A)`` and ``H(B)`` for the left/right halves of the tables."""
    left_len = 1 << k
    left_mask = (1 << left_len) - 1
    left_counts: Counter[int] = Counter()
    right_counts: Counter[int] = Counter()
    for f in funcs:
        left = f & left_mask
        right = f >> left_len
        left_counts[left] += 1
        right_counts[right] += 1
    total = len(funcs)
    return _entropy(left_counts, total), _entropy(right_counts, total)


def _entropy_drop(funcs, n, k):
    """Return ``k - H(A)`` and ``ℓ - H(B)`` for split ``k``.

    Here ``H`` denotes the Shannon entropy in bits and ``ℓ = n - k``.  The
    returned pair measures how far the left and right halves are from being
    uniformly distributed.  A large value suggests a useful split.
    """
    ha, hb = split_entropies(funcs, n, k)
    return k - ha, (n - k) - hb


def prefix_capacity_drop(n: int, max_gates: int) -> list[tuple[int, int, float]]:
    """Estimate how many circuits share a fixed left ``k``-bit prefix.

    For each ``k`` from ``1`` to ``n`` this function computes the maximum number
    of circuits whose truth tables agree on the left ``2^k`` entries.  The
    result is a list ``[(k, count, α), ...]`` where ``count`` is this maximum and
    ``α = 1 - log2(count) / k``.  Large ``α`` indicates that few circuits depend
    on a given prefix, supporting Lemma B's capacity drop hypothesis.
    """

    counts = function_counts(n, max_gates)
    results: list[tuple[int, int, float]] = []
    for k in range(1, n + 1):
        left_len = 1 << k
        mask = (1 << left_len) - 1
        prefix_counter: defaultdict[int, int] = defaultdict(int)
        for table, c in counts.items():
            prefix_counter[table & mask] += c
        max_count = max(prefix_counter.values()) if prefix_counter else 0
        if k == 0 or max_count == 0:
            alpha = 0.0
        else:
            alpha = 1.0 - (log2(max_count) / k)
        results.append((k, max_count, alpha))
    return results


def experiment(
    n,
    max_gates,
    show_entropy=False,
    suggest_split=False,
    show_capacity=False,
    prefix_drop=False,
    csv_path=None,
):
    """Run the enumeration experiment and optionally write CSV output."""
    funcs = all_functions(n, max_gates)
    print(f"n={n}, gates<={max_gates}, total functions: {len(funcs)}")
    best = None
    best_score = -1.0
    writer = None
    if csv_path:
        csv_file = open(csv_path, "w", newline="")
        writer = csv.writer(csv_file)
        header = ["k", "A", "B", "rectangles"]
        if show_entropy or suggest_split:
            header += ["H_A", "H_B"]
        if show_capacity:
            header += ["alpha_A", "alpha_B"]
        if suggest_split:
            header += ["delta_A", "delta_B"]
        writer.writerow(header)
    for k in range(1, n):
        a, b = split_tables(funcs, n, k)
        line = f"  split k={k}: |A|={a}, |B|={b}, rectangles={a*b}"
        ha = hb = None
        alpha_a = alpha_b = None
        if show_entropy or suggest_split:
            ha, hb = split_entropies(funcs, n, k)
            if show_entropy:
                line += f", H(A)={ha:.2f}, H(B)={hb:.2f}"
        if show_capacity:
            if a > 0 and k > 0:
                alpha_a = 1.0 - (log2(a) / k)
            else:
                alpha_a = 0.0
            if b > 0 and (n - k) > 0:
                alpha_b = 1.0 - (log2(b) / (n - k))
            else:
                alpha_b = 0.0
            line += f", αA={alpha_a:.2f}, αB={alpha_b:.2f}"
        if suggest_split:
            da, db = k - ha, (n - k) - hb
            score = max(da, db)
            if score > best_score:
                best_score = score
                best = k
            line += f", ΔA={da:.2f}, ΔB={db:.2f}"
        print(line)
        if writer:
            row = [k, a, b, a * b]
            if show_entropy or suggest_split:
                row += [ha, hb]
            if show_capacity:
                row += [alpha_a, alpha_b]
            if suggest_split:
                row += [da, db]
            writer.writerow(row)
    if writer:
        csv_file.close()
    if suggest_split and best is not None:
        print(f"Suggested split: k={best} with entropy drop {best_score:.2f}")

    if prefix_drop:
        print("\nPrefix capacity drop (max circuits sharing a left prefix):")
        prefix_results = prefix_capacity_drop(n, max_gates)
        for k, cnt, alpha in prefix_results:
            print(f"  k={k}: max_count={cnt}, α={alpha:.2f}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Enumerate small circuits")
    parser.add_argument(
        "n", type=int, nargs="?", default=3,
        help="number of input bits (default: 3)")
    parser.add_argument(
        "max_gates", type=int, nargs="?", default=2,
        help="maximum number of gates (default: 2)")
    parser.add_argument(
        "--entropy", action="store_true",
        help="display Shannon entropies for each split")
    parser.add_argument(
        "--suggest", action="store_true",
        help="print recommended split based on entropy drop")
    parser.add_argument(
        "--capacity", action="store_true",
        help="display estimated α drop for each split")
    parser.add_argument(
        "--prefix", action="store_true",
        help="also print prefix capacity drop statistics")
    parser.add_argument(
        "--csv", type=str, default=None,
        help="write per-split results to a CSV file")
    args = parser.parse_args()
    experiment(
        n=args.n,
        max_gates=args.max_gates,
        show_entropy=args.entropy,
        suggest_split=args.suggest,
        show_capacity=args.capacity,
        prefix_drop=args.prefix,
        csv_path=args.csv,
    )
