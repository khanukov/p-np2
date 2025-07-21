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

## Detailed branch analysis
The measure-based induction follows these steps in detail.

### Induction on the measure
We set
$$
\mu(F,h,Rset) = 2*h + |\,\text{uncovered}\;F\;Rset\,|.
$$
The recursion for `buildCover` is well founded with respect to this measure.
We perform a **double induction**: an outer induction on `h` and an inner
induction on the number of uncovered pairs.  This is equivalent to
lexicographic induction on `μ`.  Assume the statement already holds for
all smaller values of `μ`.

### Base case `uncovered = ∅`
If `firstUncovered F Rset = none` the recursion terminates immediately and
returns `Rset`.  Provided that `Rset.card ≤ mBound n h` the claim holds.

### Low-sensitivity branch
Let `s` be the maximal sensitivity of functions in `F`.  When
`s < \log_2(n+1)` the auxiliary lemma `low_sensitivity_cover` produces a
collection `R_ls` of at most
$2^{10 * s * \log_2(n+1)}$ rectangles covering the remaining inputs.  Because
`mBound` eventually dominates this quantity for `h ≥ \log_2(n+1)^2`, their
union with the current set stays below `mBound n h`.

### Entropy branch
Otherwise an entropy split finds a coordinate that decreases collision
entropy.  Both restricted families have budget `h - 1`, so the induction
hypotheses give covers bounded by `mBound n (h-1)`.  Since
`2 * mBound n (h-1) ≤ mBound n h` the union of these two covers also stays
within the desired bound.

### Sunflower branch
A sunflower step occasionally extracts a single rectangle covering several
functions at once.  This reduces the number of uncovered pairs by at least
two without changing `h`.  The induction hypothesis for the smaller measure
then bounds the rest of the construction.

Combining all branches yields the desired inequality
`(buildCover F h Rset).card ≤ mBound n h`.  The current development
implements this induction in `cover.lean`, relying on the lemmas
`mu_union_singleton_lt` and `mu_buildCover_le_start` to show that each
recursive step lowers the measure.

### Numeric considerations
The proof also requires several numeric comparisons. In the entropy branch the inequality
`two_mul_mBound_le_succ` guarantees that doubling the bound for budget `h-1` stays below
`mBound n h`. For the low-sensitivity case the auxiliary constant `10` in the definition of
`mBound` ensures that `2^{10 * s * log₂(n+1)} ≤ 2^{10 * h}` whenever `s < log₂(n+1)` and the
budget satisfies `log₂(n+1)^2 ≤ h`. The sunflower step inserts only a bounded number of
rectangles, so the slack in `mBound` absorbs this additive overhead. Combining these estimates
yields `(buildCover F h ∅).card ≤ mBound n h` for the initial call.

Additional numeric facts:
Doubling the bound for budget `h-1` remains below `mBound n h`.  Expanding the definition
  mBound n h = n * (h + 2) * 2^(10*h)
yields
  2 * mBound n (h-1) = n * (h + 1) * 2^(10*h - 9)
which is at most `mBound n h` for all `h ≥ 1`.
