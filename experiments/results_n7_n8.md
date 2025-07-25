# Enumeration Results for n = 7 and n = 8

These runs extend the brute-force search to slightly larger circuits as
suggested for gathering empirical evidence towards Lemma B.  The runs with
``max_gates = 3`` complete within seconds.  A second set with four gates still
finishes quickly and shows the same trend.

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

### `n = 7`, up to four gates

```
$ python3 lemma_b_search.py 7 4
n=7, gates<=4, total functions: 29983
  split k=1: |A|=4, |B|=29983, rectangles=119932
  split k=2: |A|=16, |B|=29982, rectangles=479712
  split k=3: |A|=121, |B|=29869, rectangles=3614149
  split k=4: |A|=886, |B|=28977, rectangles=25673622
  split k=5: |A|=3834, |B|=24870, rectangles=95351580
  split k=6: |A|=11916, |B|=11916, rectangles=141991056
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

### `n = 8`, up to four gates

```
$ python3 lemma_b_search.py 8 4
n=8, gates<=4, total functions: 65258
  split k=1: |A|=4, |B|=65258, rectangles=261032
  split k=2: |A|=16, |B|=65258, rectangles=1044128
  split k=3: |A|=121, |B|=65257, rectangles=7896097
  split k=4: |A|=886, |B|=65128, rectangles=57703408
  split k=5: |A|=3834, |B|=63840, rectangles=244762560
  split k=6: |A|=11916, |B|=56684, rectangles=675446544
  split k=7: |A|=29983, |B|=29983, rectangles=898980289
```

Even for eight inputs the counts remain tiny compared to the ``2^{2^n}``
possible Boolean functions, providing some experimental support for the
capacity drop hypothesis.
