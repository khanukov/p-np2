# Experiments for Lemma B

This folder contains small prototype code to explore the **structural compression** conjectured in Lemma B of the research notes.  The script `lemma_b_search.py` exhaustively enumerates Boolean functions that can be computed by circuits of bounded size (over the gates `AND`, `OR`, and `NOT`) on a small number of input variables.

For each split of the truth table into `k` left bits and `n-k` right bits, the script reports how many distinct left and right halves appear among all enumerated functions.  The product `|A| × |B|` is the size of a simple rectangle cover obtained by grouping functions with the same halves.

The goal is to gather data for small `n` and small gate budgets to see whether these rectangle counts grow slower than the total number of functions, hinting at a possible proof strategy for Lemma B.

## Running the experiment

Run the script with Python 3:

```bash
python3 lemma_b_search.py
```

The default parameters explore circuits on `n=3` input bits with up to 2 gates.  Feel free to adjust `n` and `max_gates` in `lemma_b_search.py` to try other values, but note that the enumeration grows rapidly.
