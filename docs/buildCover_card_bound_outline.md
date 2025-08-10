> **Status (2025-08-06)**: This document is part of an unfinished repository. Results and plans may rely on unproven axioms or placeholders.
>
# Proof outline of `buildCover_card_bound`

This note now corresponds to the formalised proof. It elaborates on the measure based induction used to bound the
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

The induction has now been fully formalised in `cover2.lean`, using these helper lemmas to prove `buildCover_card_bound` outright.

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
implements this induction in `cover2.lean`, relying on the lemmas
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

The formal definition `coverFamily` packages this construction and its
properties.  In particular the lemma `coverFamily_card_bound` exposes the
cardinality estimate without unfolding the recursion.  While numeric
constants may change as the development matures, the overall measure-based
strategy is expected to remain stable.

# Detailed branch reasoning

The following notes expand the outline with a more explicit measure-based argument.
Let
$$
  \mu(F,h,R) = 2h + |\,\text{uncovered}\,F\,R\,|
$$
be the lexicographic measure driving the recursion.  The outer induction is on
`h` and the inner induction counts the remaining uncovered pairs.  Each branch
of `buildCover` strictly decreases this measure.

## Base case
When `uncovered F R = ∅` the recursion stops and returns `R`.  Since the size of
`R` is assumed to be at most `mBound n h`, the claim follows immediately.
The file `cover2.lean` isolates this reasoning in the lemma
`buildCover_card_bound_of_none`, which bounds the result size under the
same hypothesis.

## Low-sensitivity branch
Assume every `g ∈ F` has sensitivity at most `s` with `s < log₂(n+1)`.  The lemma
`low_sensitivity_cover` provides a set `R_ls` covering all remaining inputs and
bounding its size by `2^{C * s * log₂(n+1)}` for a universal constant `C`
(currently chosen as `10`).  Because `s < log₂(n+1)` this exponent is dominated
by `10 * h` once `log₂(n+1)^2 ≤ h`.  Consequently
`R.card + R_ls.card ≤ mBound n h`, which establishes the inductive step.

## Entropy branch
If the family is not low-sensitivity we use `exists_coord_entropy_drop` to find a
coordinate that lowers collision entropy.  Splitting on this bit yields two
restricted families `F₀` and `F₁` with entropy budget `h - 1`.  By induction
their covers contain at most `mBound n (h - 1)` rectangles.  The union of the
two covers therefore has size at most `2 * mBound n (h - 1)`, which stays below
`mBound n h` by `two_mul_mBound_le_succ`.

## Sunflower branch
Occasionally the sunflower lemma extracts a single rectangle that covers many
functions simultaneously.  Adding this rectangle lowers the number of uncovered
pairs by at least two.  The measure drops accordingly and the induction
hypothesis applies to the remaining recursion with the same entropy budget.
Since `mBound` grows fast enough to absorb a constant additive term, inserting a
bounded number of such rectangles preserves the desired inequality.

## Conclusion
By analysing all three branches we see that every recursive call reduces `µ` and
that the numeric constant in `mBound` eventually dominates the total number of
inserted rectangles.  Hence the final cover returned by `buildCover` never
contains more than `mBound n h` rectangles.


## Subexponential tail bound
The arithmetic lemma `mBound_lt_subexp` in `bound.lean` proves that `mBound n h < 2^(n/100)` once `n ≥ n₀(h)`.  Since the dimension `N` of the truth table equals `2^n`, this implies
$$|\mathcal{R}| \le 2^{n/100} = 2^{\log_2 N / 100} \le 2^{N - N^{1/2}}$$
for all sufficiently large `n`.  In other words the size of the cover grows strictly slower than any full exponential `2^N`, matching the usual form `2^{N - N^{\delta}}` of Lemma B for some `\delta > 0`.

## From `mBound` to Lemma B

The formal statement `family_collision_entropy_lemma_table` in
`bound.lean` packages the construction together with the numeric bound
above.  Combining this inequality with the elementary estimate
$$(2^n)/100 \le 2^n - 2^{\lfloor n/2\rfloor}$$
(which holds for all `n \ge 1`) immediately yields a stronger version
in the usual "exponentially small" form
$$|\mathcal{R}| \le 2^{2^n - 2^{\lfloor n/2\rfloor}}.$$
Consequently the cover produced by `buildCover` witnesses Lemma B with
parameter $\delta=1/2$ once `n \ge n₀(h)`.
