"""Enumerate Boolean functions computed by a single gate."""

import argparse


def truth_tables_single_gate(n):
    var_tables = []
    for i in range(n):
        table = []
        for x in range(1 << n):
            bit = (x >> i) & 1
            table.append(bit)
        var_tables.append(tuple(table))
    const0 = tuple(0 for _ in range(1 << n))
    const1 = tuple(1 for _ in range(1 << n))
    tables = set()
    tables.update(var_tables)
    tables.update({tuple(1 - b for b in t)
                  for t in var_tables})  # NOT of variables
    tables.add(const0)
    tables.add(const1)
    # binary operations on pairs of variables (AND, OR)
    for i in range(n):
        for j in range(i + 1, n):
            t1 = var_tables[i]
            t2 = var_tables[j]
            and_table = tuple(a & b for a, b in zip(t1, t2))
            or_table = tuple(a | b for a, b in zip(t1, t2))
            tables.add(and_table)
            tables.add(or_table)
    return tables


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Enumerate one-gate Boolean functions")
    parser.add_argument(
        "n", type=int, nargs="?", default=3,
        help="number of input bits (default: 3)")
    args = parser.parse_args()
    tables = truth_tables_single_gate(args.n)
    print("unique functions", len(tables))
    print("all tables as bitstrings")
    for tbl in sorted(tables):
        bits = ''.join(str(b) for b in tbl)
        print(bits)
