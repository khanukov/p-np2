> **Status (2025-09-24)**: Combinatorial ingredients for Lemma B are formalised.  The remaining gap is an efficient enumeration strategy.
>
# Progress Towards Lemma B

This note summarises how the Lean development assembles a subexponential rectangular cover for families of small Boolean circuits.

* `Cover/BuildCover.lean` constructs a cover `buildCover F h hH` and proves coverage together with the universal bound `(buildCover F h hH).card ≤ Fintype.card (Subcube n)`.
* `family_entropy_cover.lean` packages the construction into a `FamilyCover` record whose cardinality satisfies `≤ Cover2.mBound n h = n (h+2) 2^{10h}` whenever the arithmetic condition `Fintype.card (Subcube n) ≤ Cover2.mBound n h` holds.
* `bound.lean` shows that `Cover2.mBound n h` is subexponential in `n` (`mBound_lt_subexp`).
* `low_sensitivity_cover.lean` and `merge_low_sens.lean` glue the entropy cover with the low-sensitivity branch, culminating in `decisionTree_cover`.

Combining these pieces yields the statement that families of circuits of size `≤ n^c` admit subexponential covers; the blueprint for the final Lemma B is laid out in `bound.lean` and `cover_numeric.lean`.

## Current status

* ✅ Structural lemmas (`sunflower_step`, `exists_coord_card_drop`, `coreAgreement`).
* ✅ Entropy bounds and the packaged cover (`family_entropy_cover`, `mBound_lt_subexp`).
* ✅ Decision-tree cover and merging arguments.
* ⚠️ Open: devise an efficient (better-than-exhaustive) enumeration of the rectangles produced by `buildCover`.  The executable baseline in `Cover/Compute.lean` still scans the full Boolean cube.

These notes serve as a checklist for future work on the algorithmic side of Lemma B.
