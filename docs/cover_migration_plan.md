# Migration plan: `cover.lean` to `cover2.lean`

This note tracks the ongoing effort to port the proofs from `Pnp2/cover.lean`
into the lighter `Pnp2/cover2.lean` module.  The goal is to keep a minimal
interface for downstream files while gradually re-establishing all results.

## Overview

* `cover.lean` contains 93 lemmas supporting the recursive construction of a
  rectangular cover.  The file is self‑contained but heavy.
* `cover2.lean` reintroduces the key numeric definitions and currently provides
  only a subset of these lemmas.  It additionally includes helpers such as
  `mBound_nonneg` and the monotonicity lemma `uncovered_subset` not present in
  `cover.lean`.
* Statements required by other modules are temporarily marked as `axiom` until
their proofs are ported.

## Status summary

| Category | Lemmas |
|---------|--------|
| Fully migrated | 92 |
| Axioms | 0 |
| Pending | 1 |

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
AllOnesCovered.empty
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
mu_union_buildCover_le
mu_union_buildCover_lt
mu_buildCover_lt_start
mu_buildCover_le_start
buildCover_covers_with
buildCover_covers
buildCover_mu
buildCover_measure_drop
buildCover_card_bound_base
buildCover_card_bound_of_none
buildCover_card_bound
buildCover_card_univ_bound
buildCover_card_init_mu
buildCover_card_linear_bound
buildCover_card_linear_bound_base
buildCover_card_lowSens
buildCover_card_lowSens_with
buildCover_card_bound_lowSens_with
buildCover_card_bound_lowSens
buildCover_card_bound_lowSens_or
buildCover_mono_lowSens
buildCover_mono
cover_exists
lift_mono_of_restrict
lift_mono_of_restrict_fixOne
mono_subset
mono_union
coverFamily_eq_buildCover
coverFamily_spec
coverFamily_spec_cover
coverFamily_mono
coverFamily_card_bound
coverFamily_card_linear_bound
coverFamily_card_univ_bound
```

### Not yet ported (1 lemma)

```
sunflower_step
```

## Next steps

1. Port the remaining combinatorial facts, notably the `sunflower_step` lemma.
2. Recreate the recursion `buildCover` and its counting bounds,
   replacing each remaining axiom with its full proof.
3. Once all lemmas are available, `cover2.lean` can replace `cover.lean` in the
   build and the legacy file will be removed.

Note: `cover2.lean` now contains weak variants `buildCover_covers_with`,
`buildCover_mu`, `mu_union_buildCover_lt`, and `mu_buildCover_lt_start` that
assume the starting rectangle set already covers all `1`‑inputs or merely assert
a non‑strict measure drop.  The companion lemmas `coverFamily_spec` and
`coverFamily_spec_cover` currently rely on the same hypothesis.  The full
statements without this assumption remain pending.

At this stage the lemma `sunflower_step` still depends on the legacy
`Subcube` implementation.  To prepare for this port we introduced
`Boolcube.Subcube.fromPoint` together with basic lemmas on membership and
dimension, but the full `sunflower_step` proof remains pending.  Completing the
lemma still requires reconciling the classical argument with the simplified
subcube structure used throughout `cover2.lean`.
