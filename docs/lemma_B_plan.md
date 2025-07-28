# Progress Towards Lemma B

This short note summarises the intended formal proof that the family of
small Boolean functions admits a subexponential rectangular cover.  It
collects various helper lemmas already available in the repository and
sketches how they fit together.  The goal is to bound the size of the
cover produced by `buildCover` by the function `mBound` and then use the
asymptotic estimate `mBound_lt_subexp` from `bound.lean`.

The `buildCover_card_bound` lemma establishes
```
(buildCover F h hH).card ≤ mBound n h
```
for any family `F : Family n` whose collision entropy does not exceed
`h`.  Combining this with `cover_exists` we obtain a finite set of
subcubes covering all one‑inputs of every function in `F` with the same
size bound.  Finally `mBound_lt_subexp` shows that for sufficiently
large `n` this bound is `≤ 2^(n/100)`, yielding the desired
subexponential behaviour.

The remaining work mainly concerns connecting these pieces with the
combinatorial lemmas from the `sunflower` development and providing a
computable version of `buildCover`.

## Current status

The formal development now proves the desired sub-exponential bound as
`Bound.lemmaB_circuit_cover`.  This theorem packages the entropy cover
construction and the numeric estimate `mBound_lt_subexp` to show that
all circuits of size `≤ n^c` admit a joint monochromatic cover of at
most `2^{(2^n)/100}` rectangles.  The proof relies on the `family_collision_entropy_lemma_table`
for general families and instantiates it with the circuit family.

These rectangles can now be enumerated constructively via
`Cover.buildCoverCompute`.  The list is obtained from
`Cover.coverFamily`, so algorithmic applications can iterate over the
actual cover.

An alternative presentation is given by the lemma
`Bound.lemmaB_circuit_cover_delta`.  It reformulates the subexponential
bound as `|Rset| ≤ 2^{2^n - 2^{n/2}}`, matching the usual
`2^{N - N^δ}` notation with `δ = 1/2`.  This version follows from the
basic bound by a straightforward numeric comparison.

