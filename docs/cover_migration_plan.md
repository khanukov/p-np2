# Migration plan: `cover.lean` to `cover2.lean`

This note tracks the ongoing effort to port the proofs from `Pnp2/cover.lean`
into the lighter `Pnp2/cover2.lean` module.  The goal is to keep a minimal
interface for downstream files while gradually re-establishing all results.

## Overview

* `cover.lean` contains 88 lemmas supporting the recursive construction of a
  rectangular cover.  The file is self‑contained but heavy.
* `cover2.lean` reintroduces the key numeric definitions and currently provides
  only a subset of these lemmas.
* Statements required by other modules are temporarily marked as `axiom` until
their proofs are ported.

## Status summary

| Category | Lemmas |
|---------|--------|
| Fully migrated | 60 |
| Axioms | 0 |
| Pending | 28 |

The lists below group the lemmas by status.  Names exactly match those in
`cover.lean`.

### Fully migrated

```
numeric_bound
numeric_bound_pos
pow_le_mBound
pow_le_mBound_simple
mBound_pos
two_le_mBound
three_le_mBound
mBound_zero
mBound_eq_zero_iff
mBound_mono
mBound_mono_left
mBound_le_succ
two_mul_mBound_le_succ
card_union_mBound_succ
one_add_mBound_le_succ
card_union_singleton_mBound_succ
card_insert_mBound_succ
card_union_pair_mBound_succ
card_union_triple_mBound_succ
cover_size_bound
size_bounds
mu_nonneg
mu_lower_bound
mu_mono_h
mu_union_singleton_le
mu_union_singleton_lt
mu_union_singleton_succ_le
mu_union_lt
notCovered_empty
NotCovered.monotone
firstUncovered_none_iff
AllOnesCovered.full
AllOnesCovered.superset
AllOnesCovered.union
AllOnesCovered.insert
allOnesCovered_of_firstUncovered_none
mu_of_allCovered
allOnesCovered_of_mu_eq
uncovered_eq_empty_of_allCovered
uncovered_subset_of_union_singleton
uncovered_subset_of_union
uncovered_card_bound
uncovered_init_coarse_bound
uncovered_init_bound_empty
mu_mono_subset
mu_of_firstUncovered_none
mu_gt_of_firstUncovered_some
mu_union_double_lt
mu_union_double_succ_le
mu_union_le
mu_union_singleton_double_lt
mu_union_singleton_double_succ_le
mu_union_singleton_triple_lt
mu_union_singleton_triple_succ_le
mu_union_singleton_quad_succ_le
mu_union_triple_lt
mu_union_triple_succ_le
buildCover_card_bound_base
buildCover_card_bound_of_none
buildCover_card_linear_bound
```

### Not yet ported (28 lemmas)

```
buildCover_card_bound
buildCover_card_bound_lowSens
buildCover_card_bound_lowSens_or
buildCover_card_bound_lowSens_with
buildCover_card_init_mu
buildCover_card_linear_bound_base
buildCover_card_lowSens
buildCover_card_lowSens_with
buildCover_card_univ_bound
buildCover_covers
buildCover_covers_with
buildCover_measure_drop
buildCover_mono
buildCover_mono_lowSens
buildCover_mu
coverFamily_card_univ_bound
coverFamily_mono
coverFamily_spec
coverFamily_spec_cover
cover_exists
lift_mono_of_restrict
lift_mono_of_restrict_fixOne
mono_union
mu_buildCover_le_start
mu_buildCover_lt_start
sunflower_step
mu_union_buildCover_le
mu_union_buildCover_lt
```

## Next steps

1. Port the remaining combinatorial facts about uncovered inputs and the
   termination measure (e.g., `mu_union_buildCover_le` and related lemmas).
2. Recreate the recursion `buildCover` and its counting bounds,
   replacing each remaining axiom with its full proof.
3. Once all lemmas are available, `cover2.lean` can replace `cover.lean` in the
   build and the legacy file will be removed.
