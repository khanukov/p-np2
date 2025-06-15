import argparse
from math import log2
from lemma_b_search import variables, const_table, all_functions


def collision_entropy(n: int, max_gates: int) -> float:
    """Return log_2 of the number of distinct functions."""
    funcs = all_functions(n, max_gates)
    total = len(funcs)
    if total == 0:
        return 0.0
    return log2(total)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Compute collision entropy of small circuit class")
    parser.add_argument("n", type=int, nargs="?", default=3,
                        help="number of input bits (default: 3)")
    parser.add_argument("max_gates", type=int, nargs="?", default=2,
                        help="maximum number of gates (default: 2)")
    args = parser.parse_args()
    h2 = collision_entropy(args.n, args.max_gates)
    print(f"n={args.n}, gates<={args.max_gates}, H2={h2:.4f}")
