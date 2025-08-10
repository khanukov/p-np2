> **Status (2025-08-06)**: This document is part of an unfinished repository. Results and plans may rely on unproven axioms or placeholders.
>
# Enumeration Results for n = 6

This note collects raw counts from running `lemma_b_search.py` with
parameters `(n=6, max_gates=3)`. The script enumerates all Boolean
functions computable with at most three `AND`/`OR`/`NOT` gates.
For each split position `k` the number of distinct left and right
halves of the truth table are reported, along with their product,
providing a trivial rectangle bound.

```bash
$ python3 lemma_b_search.py 6 3
n=6, gates<=3, total functions: 1954
  split k=1: |A|=4, |B|=1954, rectangles=7816
  split k=2: |A|=14, |B|=1953, rectangles=27342
  split k=3: |A|=84, |B|=1910, rectangles=160440
  split k=4: |A|=318, |B|=1668, rectangles=530424
  split k=5: |A|=872, |B|=872, rectangles=760384
```

Even for six inputs the enumeration completes quickly, and the
resulting counts highlight how sparse the family of small circuits is
relative to all `2^{2^6}` Boolean functions.  These values will serve
as a reference point for future experiments with larger parameters.
