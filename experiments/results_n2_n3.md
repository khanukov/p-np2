> **Status (2025-08-06)**: This document is part of an unfinished repository. Results and plans may rely on unproven axioms or placeholders.
>
# Enumeration Results for n = 2 and n = 3

This note collects raw counts from running `lemma_b_search.py` with small
parameters. The script enumerates all Boolean functions computable by circuits
with a bounded number of AND/OR/NOT gates. For each split position `k` the
number of distinct left and right halves of the truth table are reported,
together with their product, which gives a trivial rectangle bound.

## `n = 2`, one gate

```
$ python3 lemma_b_search.py 2 1
n=2, gates<=1, total functions: 8
  split k=1: |A|=4, |B|=4, rectangles=16
```

## `n = 3`, up to two gates

```
$ python3 lemma_b_search.py 3 2
n=3, gates<=2, total functions: 40
  split k=1: |A|=4, |B|=30, rectangles=120
  split k=2: |A|=14, |B|=14, rectangles=196
```

These tiny cases confirm the extreme sparsity of small circuits compared to the
`2^{2^n}` possible Boolean functions.
