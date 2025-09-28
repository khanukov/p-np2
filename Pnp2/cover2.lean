import Pnp2.BoolFunc
import Pnp2.entropy
import Pnp2.sunflower
import Pnp2.Agreement
import Pnp2.BoolFunc.Support
import Pnp2.Sunflower.RSpread
import Pnp2.Boolcube
import Pnp2.Cover.SubcubeAdapters -- subcube conversion utilities
import Pnp2.Cover.Bounds -- numeric bounds for the cover construction
import Pnp2.Cover.CoarseBound -- rough estimate on uncovered pairs
import Pnp2.Cover.Uncovered -- predicates about uncovered points
import Pnp2.Cover.Lifting -- lemmas lifting monochromaticity through restrictions
import Pnp2.Cover.Measure -- termination measure and its basic lemmas
import Pnp2.Cover.BuildCover -- recursive cover construction and its API
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

-- Silence noisy linter suggestions in this development file.
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Classical
open Finset
open Agreement
open BoolFunc (Family BFunc)
open Boolcube (Point Subcube)
open Sunflower

namespace Cover2

/-!  This module gradually reimplements the original `cover.lean` file.
Most numeric and combinatorial lemmas have already been ported, while the
recursive cover construction is currently represented by a lightweight stub.
Remaining gaps are tracked in `docs/cover_migration_plan.md`.

The heavy arithmetic lemmas surrounding the auxiliary function `mBound` live in
`Pnp2.Cover.Bounds`, while a coarse estimate on uncovered pairs resides in
`Pnp2.Cover.CoarseBound`.  This separation keeps the present file focused on the
combinatorial aspects of the cover construction.
-/

@[simp] def size {n : ℕ} (Rset : Finset (Subcube n)) : ℕ := Rset.card

lemma cover_size_bound {n : ℕ} (Rset : Finset (Subcube n)) :
    size Rset ≤ Fintype.card (Subcube n) := by
  classical
  simpa [size] using (Finset.card_le_univ (s := Rset))

@[simp] def bound_function (n : ℕ) : ℕ := Fintype.card (Subcube n)

lemma size_bounds {n : ℕ} (Rset : Finset (Subcube n)) :
    size Rset ≤ bound_function n := by
  classical
  simpa [bound_function] using cover_size_bound (Rset := Rset)

import Pnp2.Cover.SunflowerStep

variable {n h : ℕ} (F : Family n)

/-
Notes:
Lemmas about transferring monochromaticity from restricted families to the
original family have been moved to `Pnp2.Cover.Lifting`.
The following results continue the development using those utilities.
-/

/--
Monochromaticity is preserved when restricting to a subset of rectangles.
If every rectangle in `R₁` is monochromatic for `F` and `R₂ ⊆ R₁`, then every
rectangle in `R₂` remains monochromatic. -/
lemma mono_subset {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    (h₁ : ∀ R ∈ R₁, Subcube.monochromaticForFamily R F)
    (hsub : R₂ ⊆ R₁) :
    ∀ R ∈ R₂, Subcube.monochromaticForFamily R F := by
  intro R hR
  exact h₁ R (hsub hR)

/--
The union of two collections of monochromatic rectangles is again a collection
of monochromatic rectangles. -/
lemma mono_union {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    (h₁ : ∀ R ∈ R₁, Subcube.monochromaticForFamily R F)
    (h₂ : ∀ R ∈ R₂, Subcube.monochromaticForFamily R F) :
    ∀ R ∈ R₁ ∪ R₂, Subcube.monochromaticForFamily R F := by
  intro R hR
  rcases Finset.mem_union.mp hR with h | h
  · exact h₁ R h
  · exact h₂ R h

/--
`buildCover` is implemented in `Cover.BuildCover`.
`cover_exists` repackages its specification as an existential statement for
downstream use. -/

lemma cover_exists {F : Family n} {h : ℕ}
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, ∀ f ∈ F, Boolcube.Subcube.monochromaticFor R f) ∧
      AllOnesCovered (n := n) F Rset := by
  classical
  refine ⟨buildCover (n := n) F h hH, ?_, ?_⟩
  · intro R hR f hf
    exact
      (buildCover_pointwiseMono (F := F) (h := h) (hH := hH) R hR f hf)
  · exact buildCover_covers (F := F) (h := h) (hH := hH)

/--
`cover_exists_bound` strengthens `cover_exists` with an explicit cardinality
bound.  The combinatorial argument for the recursive construction establishes
this estimate via `buildCover_card_bound`, so no unfinished proofs remain in
this statement.
-/
lemma cover_exists_bound {F : Family n} {h : ℕ}
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, ∀ f ∈ F, Boolcube.Subcube.monochromaticFor R f) ∧
      AllOnesCovered (n := n) F Rset ∧
      Rset.card ≤ 2 ^ n := by
  classical
  refine ⟨buildCover (n := n) F h hH, ?_, ?_, ?_⟩
  · intro R hR f hf
    exact buildCover_pointwiseMono (F := F) (h := h) (hH := hH) R hR f hf
  · exact buildCover_covers (F := F) (h := h) (hH := hH)
  · exact buildCover_card_bound (n := n) (F := F) (h := h) hH

/--
  A variant of `cover_exists_bound` that exposes the explicit numerical bound
  `mBound`.  The strengthened combinatorial analysis in
  `Cover.BuildCover` shows directly that the recursion never produces more than
  `mBound n h` rectangles under the standard guard.  This lemma packages that
  fact for downstream use.
  -/
lemma cover_exists_mBound {F : Family n} {h : ℕ}
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hn : 0 < n) (hlarge : n ≤ 5 * h) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, ∀ f ∈ F, Boolcube.Subcube.monochromaticFor R f) ∧
      AllOnesCovered (n := n) F Rset ∧
      Rset.card ≤ mBound n h := by
  classical
  -- The same witness as in `cover_exists_bound` suffices; we only sharpen the
  -- numerical estimate.
  refine ⟨buildCover (n := n) F h hH, ?_, ?_, ?_⟩
  · intro R hR f hf
    exact buildCover_pointwiseMono (F := F) (h := h) (hH := hH) R hR f hf
  · exact buildCover_covers (F := F) (h := h) (hH := hH)
  · simpa using
      (buildCover_card_le_mBound (n := n) (F := F)
        (h := h) (hH := hH) hn hlarge)

end Cover2
