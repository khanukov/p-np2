# Enumeration Results for n = 7 and n = 8

These runs extend the brute-force search to slightly larger circuits as
suggested for gathering empirical evidence towards Lemma B.  Both cases use
``max_gates = 3`` which completes within seconds.

## `n = 7`, up to three gates

```
$ python3 lemma_b_search.py 7 3
n=7, gates<=3, total functions: 3824
  split k=1: |A|=4, |B|=3824, rectangles=15296
  split k=2: |A|=14, |B|=3824, rectangles=53536
  split k=3: |A|=84, |B|=3823, rectangles=321132
  split k=4: |A|=318, |B|=3772, rectangles=1199496
  split k=5: |A|=872, |B|=3408, rectangles=2971776
  split k=6: |A|=1954, |B|=1954, rectangles=3818116
```

## `n = 8`, up to three gates

```
$ python3 lemma_b_search.py 8 3
n=8, gates<=3, total functions: 6794
  split k=1: |A|=4, |B|=6794, rectangles=27176
  split k=2: |A|=14, |B|=6794, rectangles=95116
  split k=3: |A|=84, |B|=6794, rectangles=570696
  split k=4: |A|=318, |B|=6793, rectangles=2160174
  split k=5: |A|=872, |B|=6734, rectangles=5872048
  split k=6: |A|=1954, |B|=6224, rectangles=12161696
  split k=7: |A|=3824, |B|=3824, rectangles=14622976
```

Even for eight inputs the counts remain tiny compared to the ``2^{2^n}``
possible Boolean functions, providing some experimental support for the
capacity drop hypothesis.
