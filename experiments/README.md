# Experiments for Lemma B

This folder contains small prototype code to explore the **structural compression** conjectured in Lemma B of the research notes.  The script `lemma_b_search.py` exhaustively enumerates Boolean functions that can be computed by circuits of bounded size (over the gates `AND`, `OR`, and `NOT`) on a small number of input variables.  A simpler tool `single_gate_count.py` lists all functions realizable with a single gate for a given input size.

For each split of the truth table into `k` left bits and `n-k` right bits, the script reports how many distinct left and right halves appear among all enumerated functions.  The product `|A| × |B|` is the size of a simple rectangle cover obtained by grouping functions with the same halves.

The goal is to gather data for small `n` and small gate budgets to see whether these rectangle counts grow slower than the total number of functions, hinting at a possible proof strategy for Lemma B.

## Running the experiment

Run the scripts with Python 3.

``lemma_b_search.py`` performs an exhaustive search of circuits with up to
``max_gates`` gates on ``n`` inputs.  Both parameters are optional positional
arguments with defaults ``n=3`` and ``max_gates=2``.

``single_gate_count.py`` simply lists all functions realizable by a single gate
on ``n`` inputs (optional, default ``n=3``).

```bash
python3 lemma_b_search.py          # use defaults n=3, max_gates=2
python3 lemma_b_search.py 4 1      # four inputs, at most one gate
python3 single_gate_count.py       # tables from one gate on three inputs
python3 collision_entropy.py 3 1   # log2 of unique functions for n=3
```

Note that the enumeration grows rapidly with both ``n`` and ``max_gates``.

