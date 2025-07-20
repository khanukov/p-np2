# Sketch proof of `buildCover_card_bound`

This note elaborates on the measure based induction used to bound the
size of the rectangle cover produced by `buildCover`.
The lemma

```
(buildCover F h hH).card ≤ mBound n h
```

states that with entropy budget `h` no more than `mBound n h` rectangles are
inserted.  The recursive definition of `buildCover` allows three distinct
branches.  The proof analyses them via a double induction on the measure

```
μ(F, h, R) = 2 * h + |uncovered F R|
```

where `uncovered F R` collects all still uncovered `1`‑inputs of the family.

## Inductive strategy

1. **Base case.**  If `uncovered F R = ∅` the recursion terminates and
   returns `R` unchanged.  The bound follows from the assumption that
   `R.card ≤ mBound n h`.
2. **Low-sensitivity branch.**  When all functions have bounded
   sensitivity the helper lemma `low_sensitivity_cover` supplies a set of
   rectangles `R_ls`.  Their cardinality is at most
   `2^(10 * s * log₂(n+1))` where `s` is the maximum sensitivity.  The
   union `R ∪ R_ls` forms the result and the numeric estimate shows that
   this union stays below `mBound n h`.
3. **Entropy branch.**  If the family is not low-sensitivity one fixes a
   coordinate that decreases collision entropy.  The restrictions to both
   values of this bit have entropy budget `h-1`, so the induction
   hypothesis bounds each recursive call by `mBound n (h-1)`.  Doubling the
   result is still bounded by `mBound n h` thanks to the inequality
   `two_mul_mBound_le_succ`.
4. **Sunflower branch.**  Occasionally a sunflower argument extracts a
   single rectangle that covers many functions at once.  This step reduces
   `|uncovered|` by at least two and thus strictly decreases `μ`.  The
   induction hypothesis therefore applies to the remaining uncovered set
   with the same entropy budget.

Since `μ` decreases in every step, after at most `μ(F, h, ∅)` iterations the
recursion stops.  Because `mBound` dominates this initial measure we obtain
`(buildCover F h hH).card ≤ mBound n h`.

The current Lean development provides most helper lemmas described above.
Formalising the complete induction is work in progress.  The current
implementation in `cover.lean` includes a coarse bound following this
strategy, and future updates will replace it with the full argument.
