# Prototype tool to explore Lemma B (structural compression of small circuits)
# Enumerates all boolean functions computable by circuits up to a given size
# with inputs of size n, using AND/OR/NOT. For small n and gate count it
# exhaustively generates truth tables and measures the number of unique
# "left" and "right" halves when the truth table is split at position k.
# This is a toy experiment to gather data about possible rectangle covers.

from collections import defaultdict
from itertools import product

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


def split_tables(funcs, n, k):
    """Split each table into left/right halves of k and n-k bits."""
    N = 1 << n
    left_bits = 1 << k
    right_bits = N - left_bits
    left_mask = (1 << left_bits) - 1
    left_set = set()
    right_set = set()
    for f in funcs:
        left = f & left_mask
        right = f >> left_bits
        left_set.add(left)
        right_set.add(right)
    return len(left_set), len(right_set)


def experiment(n, max_gates):
    funcs = all_functions(n, max_gates)
    print(f"n={n}, gates<={max_gates}, total functions: {len(funcs)}")
    for k in range(1, n):
        a, b = split_tables(funcs, n, k)
        print(f"  split k={k}: |A|={a}, |B|={b}, rectangles={a*b}")


if __name__ == "__main__":
    experiment(n=3, max_gates=2)
