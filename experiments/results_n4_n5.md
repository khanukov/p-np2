> **Status (2025-08-06)**: This document is part of an unfinished repository. Results and plans may rely on unproven axioms or placeholders.
>
# Enumeration Results for n = 4 and n = 5

This note collects raw counts from running `lemma_b_search.py` with slightly larger
parameters than the default.  The script enumerates all Boolean functions
computable by circuits with a bounded number of gates over `AND`, `OR`, and `NOT`.
For each split position `k` the number of distinct left and right halves of the
truth table are reported, together with their product (a trivial rectangle count).

## `n = 4`, up to three gates

```
$ python3 lemma_b_search.py 4 3
n=4, gates<=3, total functions: 318
  split k=1: |A|=4, |B|=290, rectangles=1160
  split k=2: |A|=14, |B|=220, rectangles=3080
  split k=3: |A|=84, |B|=84, rectangles=7056
```

## `n = 5`, up to three gates

```
$ python3 lemma_b_search.py 5 3
n=5, gates<=3, total functions: 872
  split k=1: |A|=4, |B|=871, rectangles=3484
  split k=2: |A|=14, |B|=836, rectangles=11704
  split k=3: |A|=84, |B|=692, rectangles=58128
  split k=4: |A|=318, |B|=318, rectangles=101124
```

Although the enumeration grows quickly, these numbers remain far below the
`2^{2^n}` possible truth tables for the same `n`, illustrating the sparsity of
small circuits and motivating the search for compact rectangle covers.
