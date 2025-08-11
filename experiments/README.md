> **Status (2025-08-06)**: This document is part of an unfinished repository. Results and plans may rely on unproven axioms or placeholders.
>
# Experiments for Lemma B

This folder contains small prototype code to explore the **structural compression** conjectured in Lemma B of the research notes.  The script `lemma_b_search.py` exhaustively enumerates Boolean functions that can be computed by circuits of bounded size (over the gates `AND`, `OR`, and `NOT`) on a small number of input variables.  A simpler tool `single_gate_count.py` lists all functions realizable with a single gate for a given input size.

For each split of the truth table into `k` left bits and `n-k` right bits, the script reports how many distinct left and right halves appear among all enumerated functions.  The product `|A| × |B|` is the size of a simple rectangle cover obtained by grouping functions with the same halves.

The goal is to gather data for small `n` and small gate budgets to see whether these rectangle counts grow slower than the total number of functions, hinting at a possible proof strategy for Lemma B.

## Running the experiment

Run the scripts with Python 3.

``lemma_b_search.py`` performs an exhaustive search of circuits with up to
``max_gates`` gates on ``n`` inputs.  Both parameters are optional positional
arguments with defaults ``n=3`` and ``max_gates=2``.  Passing ``--prefix``
will additionally print how many circuits share a fixed left prefix for each
split size, estimating the capacity drop from the "canonical circuits" point of
view.

The script can also report an estimated capacity drop for each split using
``--capacity``.  This prints exponents ``α`` such that ``|A| ≤ 2^{(1-α)k}`` and
``|B| ≤ 2^{(1-α)(n-k)}``, giving a rough idea how structured the function family
is.  Results can be saved as CSV via ``--csv``.

``single_gate_count.py`` simply lists all functions realizable by a single gate
on ``n`` inputs (optional, default ``n=3``).

``capacity_drop.py`` enumerates circuits on ``k`` inputs for growing ``k`` and
prints the observed ``α`` values directly.  Passing ``--prefix N`` measures how
many circuits on ``N`` inputs share a fixed left prefix, providing a more direct
estimate for the capacity drop constant ``α``.

``sunflower_step.py`` tests whether a given collection of supports contains a
`t`‑sunflower and prints the extracted core and petals when successful.

```bash
python3 lemma_b_search.py          # use defaults n=3, max_gates=2
python3 lemma_b_search.py 4 1      # four inputs, at most one gate
python3 lemma_b_search.py 7 3 --capacity  # show α drop for n=7
python3 lemma_b_search.py 8 4 --prefix    # prefix capacity stats for n=8
python3 single_gate_count.py       # tables from one gate on three inputs
python3 capacity_drop.py 6 3       # α for k up to 6 inputs
python3 capacity_drop.py --prefix 7 3  # prefix drop for n=7
python3 collision_entropy.py 3 1         # log2 of unique functions for n=3
python3 collision_entropy.py 3 1 --circuits  # weight by circuit count
python3 collision_entropy.py 3 1 --list-counts  # print truth table counts
python3 collision_entropy.py 3 1 --list-counts --descending
python3 collision_entropy.py 3 1 --list-counts --top 5
python3 sunflower_step.py --t 3 0,1 0,2 1,2  # find a sunflower among supports
```

Enumeration logs up to eight inputs are recorded in `results_n7_n8.md`.
Note that the enumeration grows rapidly with both ``n`` and ``max_gates``.

