> **Status (2025-09-24)**: `buildCover_card_bound` is fully formalised.  This note records the updated argument and how it feeds the `mBound` estimate exposed by `family_entropy_cover`.
>
# Proof sketch of `buildCover_card_bound`

The lemma

```
(buildCover F h hH).card ≤ Fintype.card (Subcube n)
```

states that the recursion never produces more rectangles than there are subcubes of dimension `n`.  The proof proceeds by analysing the well-founded recursion behind `buildCover`.

* The recursion is controlled by the measure
  ```
  μ(F, h, Rset) = 2 * h + |uncovered F Rset|,
  ```
  where `uncovered` collects the `1`‑inputs not yet covered by the growing rectangle set.
* `buildCoverAux` performs a `WellFounded.fix` recursion on `μ`.  Each branch either:
  1. returns immediately when `uncovered = ∅`,
  2. invokes the classical extender `extendCover` after finding a witness via `firstUncovered`.
* Every recursive step strictly decreases `μ`, because either the entropy budget drops or the set of uncovered pairs shrinks.
* The measure takes values in `ℕ`, therefore the recursion terminates.  The returned finset is a subset of `Subcube n` and the size bound follows from `Finset.card_le_univ`.

The more precise arithmetic bound by the explicit function `mBound n h` is supplied later by `family_entropy_cover`.  That file combines

* the structural properties of `buildCover`, and
* the numeric inequalities from `Cover/Bounds.lean`,

to package the rectangles together with the inequality

```
rects.card ≤ mBound n h
```

under the additional hypothesis `Fintype.card (Subcube n) ≤ mBound n h`.

The present outline is kept for contributors who want to understand how the termination argument connects to the numeric `mBound` interface in the rest of the project.
