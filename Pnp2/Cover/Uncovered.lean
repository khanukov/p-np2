import Pnp2.BoolFunc
import Pnp2.Boolcube
import Pnp2.Cover.SubcubeAdapters
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

open Classical
open Finset
open BoolFunc (Family BFunc)
open Boolcube (Point Subcube)

namespace Cover2

/-!
### Tracking uncovered points

This module isolates the basic predicates used to reason about points that
are **not yet covered** by a set of rectangles.  The definitions here are
independent of the rest of the cover construction and therefore live in a
separate file.  They provide the infrastructure for exploring the uncovered
set, selecting witnesses, and transferring coverage information between
different rectangle collections.
-/

/-- `x` is not covered by `Rset` when it does not belong to any rectangle in
    the set.  This is essentially the complement of the union of the
    rectangles. -/
def NotCovered {n : ℕ} (Rset : Finset (Subcube n)) (x : Point n) : Prop :=
  ∀ R ∈ Rset, ¬ x ∈ₛ R

/-- The empty set of rectangles obviously leaves every point uncovered. -/
@[simp] lemma notCovered_empty {n : ℕ} (x : Point n) :
    NotCovered (n := n) (Rset := (∅ : Finset (Subcube n))) x := by
  intro R hR
  -- membership in the empty set yields a contradiction
  cases hR

/-- Uncoveredness is monotone with respect to shrinking the set of rectangles.
    If `x` is uncovered by a larger set, then it is uncovered by any subset. -/
lemma NotCovered.monotone {n : ℕ} {R₁ R₂ : Finset (Subcube n)} (hsub : R₁ ⊆ R₂)
    {x : Point n} (hx : NotCovered (n := n) (Rset := R₂) x) :
    NotCovered (n := n) (Rset := R₁) x := by
  intro R hR
  exact hx R (hsub hR)

/-!
If a point misses every rectangle in `R₁ ∪ R₂`, then it certainly misses every
rectangle from `R₁` and from `R₂` individually.  Conversely, if it misses all
rectangles from each component, then it misses the union.  This convenient
characterisation is frequently used when reasoning about incremental cover
constructions.
-/
lemma NotCovered.union {n : ℕ} {R₁ R₂ : Finset (Subcube n)} {x : Point n} :
    NotCovered (n := n) (Rset := R₁ ∪ R₂) x ↔
      NotCovered (n := n) (Rset := R₁) x ∧
        NotCovered (n := n) (Rset := R₂) x := by
  classical
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro R hR
      exact h R (by exact Finset.mem_union.mpr <| Or.inl hR)
    · intro R hR
      exact h R (by exact Finset.mem_union.mpr <| Or.inr hR)
  · intro h R hR
    have hmem := Finset.mem_union.mp hR
    cases hmem with
    | inl hR1 => exact h.1 R hR1
    | inr hR2 => exact h.2 R hR2

/-!
`uncovered F Rset` collects all pairs `⟨f, x⟩` where `f ∈ F`, `f x = true` and
the point `x` is not covered by the rectangles in `Rset`.  This set shrinks as
we add more rectangles to the cover.
-/
@[simp] def uncovered {n : ℕ} (F : Family n) (Rset : Finset (Subcube n)) :
    Set (Σ _ : BFunc n, Point n) :=
  {p | p.1 ∈ F ∧ p.1 p.2 = true ∧ NotCovered (n := n) (Rset := Rset) p.2}

/-!
`firstUncovered` is a tiny search routine: it returns some element of the
uncovered set if one exists, and `none` otherwise.  The use of the axiom of
choice makes the definition noncomputable, but this is sufficient for the
structural arguments in the cover development.
-/
noncomputable def firstUncovered {n : ℕ} (F : Family n)
    (Rset : Finset (Subcube n)) :
    Option (Σ _ : BFunc n, Point n) :=
  if h : (uncovered (n := n) F Rset).Nonempty then
    some h.choose
  else
    none

/-- `firstUncovered` returns `none` exactly when the uncovered set is empty. -/
@[simp] lemma firstUncovered_none_iff {n : ℕ} (F : Family n)
    (R : Finset (Subcube n)) :
    firstUncovered (n := n) F R = none ↔
      uncovered (n := n) F R = (∅ : Set (Σ _ : BFunc n, Point n)) := by
  classical
  unfold firstUncovered
  by_cases h : (uncovered (n := n) F R).Nonempty
  · have hne : uncovered (n := n) F R ≠ (∅ : Set _) :=
      Set.nonempty_iff_ne_empty.mp h
    -- Neither the proof of existence nor the inequality matters to `simp`.
    simp [Set.nonempty_iff_ne_empty]
  ·
    have hempty : uncovered (n := n) F R = (∅ : Set _) := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp; exact h ⟨p, hp⟩
    simp [Set.nonempty_iff_ne_empty]

/-- If `firstUncovered` returns `some p`, then `p` indeed belongs to the uncovered set. -/
lemma mem_uncovered_of_firstUncovered_some {n : ℕ} {F : Family n} {R : Finset (Subcube n)}
    {p : Σ _ : BFunc n, Point n}
    (hp : firstUncovered (n := n) F R = some p) :
    p ∈ uncovered (n := n) F R := by
  classical
  unfold firstUncovered at hp
  split_ifs at hp with h
  · cases hp
    exact Classical.choose_spec h

/-- Every `1`-input of every `f ∈ F` lies inside some rectangle of `Rset`. -/
@[simp] def AllOnesCovered {n : ℕ} (F : Family n)
    (Rset : Finset (Subcube n)) : Prop :=
  ∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R

/-- A single rectangle covering the entire cube trivially covers all `1`-inputs. -/
lemma AllOnesCovered.full {n : ℕ} (F : Family n) :
    AllOnesCovered (n := n) F ({Subcube.full} : Finset (Subcube n)) := by
  intro f hf x hx
  refine ⟨Subcube.full, by simp, ?_⟩
  simp

/-- Coverage is preserved when enlarging the set of rectangles. -/
lemma AllOnesCovered.superset {n : ℕ} {F : Family n}
    {R₁ R₂ : Finset (Subcube n)} (h₁ : AllOnesCovered (n := n) F R₁)
    (hsub : R₁ ⊆ R₂) :
    AllOnesCovered (n := n) F R₂ := by
  intro f hf x hx
  rcases h₁ f hf x hx with ⟨R, hR, hxR⟩
  exact ⟨R, hsub hR, hxR⟩

/-- Coverage by a union splits into coverage by each component. -/
lemma AllOnesCovered.union {n : ℕ} {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    (h₁ : AllOnesCovered (n := n) F R₁)
    (h₂ : AllOnesCovered (n := n) F R₂) :
    AllOnesCovered (n := n) F (R₁ ∪ R₂) := by
  intro f hf x hx
  by_cases hx1 : ∃ R ∈ R₁, x ∈ₛ R
  · rcases hx1 with ⟨R, hR, hxR⟩
    exact ⟨R, by simpa [Finset.mem_union] using Or.inl hR, hxR⟩
  · rcases h₂ f hf x hx with ⟨R, hR, hxR⟩
    exact ⟨R, by simpa [Finset.mem_union, hx1] using Or.inr hR, hxR⟩

/-- Inserting a rectangle preserves coverage. -/
lemma AllOnesCovered.insert {n : ℕ} {F : Family n}
    {Rset : Finset (Subcube n)} {R : Subcube n}
    (hcov : AllOnesCovered (n := n) F Rset) :
    AllOnesCovered (n := n) F (Insert.insert R Rset) := by
  classical
  have hsub : Rset ⊆ Insert.insert R Rset := by
    intro S hS; exact Finset.mem_insert.mpr (Or.inr hS)
  exact AllOnesCovered.superset (F := F) (R₁ := Rset)
    (R₂ := Insert.insert R Rset) hcov hsub

/-- When no rectangles are present, `AllOnesCovered` asserts that the family
    has no `1`-inputs at all. -/
@[simp] lemma AllOnesCovered.empty {n : ℕ} {F : Family n} :
    AllOnesCovered (n := n) F (∅ : Finset (Subcube n)) ↔
      ∀ f ∈ F, ∀ x, f x = true → False := by
  classical
  constructor
  · intro h f hf x hx
    rcases h f hf x hx with ⟨R, hR, _⟩
    cases hR
  · intro h f hf x hx
    exact False.elim (h f hf x hx)

/-!
If all `1`-inputs are covered, then the set of uncovered pairs is empty.  This
lemma often allows the uncovered set to be replaced by `∅` in proofs.
-/
lemma uncovered_eq_empty_of_allCovered {n : ℕ} {F : Family n}
    {Rset : Finset (Subcube n)}
    (hcov : AllOnesCovered (n := n) F Rset) :
    uncovered (n := n) F Rset = (∅ : Set (Σ _ : BFunc n, Point n)) := by
  classical
  ext p; constructor
  · intro hp
    have hf : p.1 ∈ F := hp.1
    have hx : p.1 p.2 = true := hp.2.1
    have hnc : NotCovered (n := n) (Rset := Rset) p.2 := hp.2.2
    rcases hcov p.1 hf p.2 hx with ⟨R, hR, hxR⟩
    have : ¬ Boolcube.Subcube.Mem R p.2 := hnc R hR
    exact False.elim (this hxR)
  · intro hp; cases hp

/-- If `firstUncovered` reports `none`, then every `1`-input is covered. -/
lemma allOnesCovered_of_firstUncovered_none {n : ℕ} {F : Family n}
    {Rset : Finset (Subcube n)}
    (hfu : firstUncovered (n := n) F Rset = none) :
    AllOnesCovered (n := n) F Rset := by
  classical
  intro f hf x hx
  by_contra hxcov
  have hxNC : NotCovered (n := n) (Rset := Rset) x := by
    intro R hR hxR; exact hxcov ⟨R, hR, hxR⟩
  have hx_mem' : (⟨f, x⟩ : Σ _ : BFunc n, Point n) ∈
      uncovered (n := n) F Rset := ⟨hf, hx, hxNC⟩
  have hempty : uncovered (n := n) F Rset =
      (∅ : Set (Σ _ : BFunc n, Point n)) :=
    (firstUncovered_none_iff (n := n) (F := F) (R := Rset)).1 hfu
  have hx_mem : f ∈ F ∧ f x = true ∧
      NotCovered (n := n) (Rset := Rset) x := hx_mem'
  have hx_mem_set : (⟨f, x⟩ : Σ _ : BFunc n, Point n)
      ∈ uncovered (n := n) F Rset := by
    simpa [uncovered] using hx_mem
  have hx_eq := congrArg
      (fun s => (⟨f, x⟩ : Σ _ : BFunc n, Point n) ∈ s) hempty
  have hx_mem_empty := Eq.mp hx_eq hx_mem_set
  cases hx_mem_empty

/-- Adding rectangles can only reduce the uncovered set. -/
lemma uncovered_subset_of_union_singleton {n : ℕ} {F : Family n}
    {Rset : Finset (Subcube n)} {R : Subcube n} :
    uncovered (n := n) F (Rset ∪ {R}) ⊆ uncovered (n := n) F Rset := by
  intro p hp
  rcases hp with ⟨hf, hx, hnc⟩
  refine ⟨hf, hx, ?_⟩
  intro S hS
  exact hnc S (by exact Finset.mem_union.mpr <| Or.inl hS)

/-- A more general monotonicity result for arbitrary unions. -/
lemma uncovered_subset_of_union {n : ℕ} {F : Family n}
    {R₁ R₂ : Finset (Subcube n)} :
    uncovered (n := n) F (R₁ ∪ R₂) ⊆ uncovered (n := n) F R₁ := by
  intro p hp
  rcases hp with ⟨hf, hx, hnc⟩
  refine ⟨hf, hx, ?_⟩
  intro S hS
  exact hnc S (by exact Finset.mem_union.mpr <| Or.inl hS)

/-- Inclusion of rectangle sets induces inclusion on uncovered pairs. -/
lemma uncovered_subset {n : ℕ} {F : Family n} {R₁ R₂ : Finset (Subcube n)}
    (hsub : R₁ ⊆ R₂) :
    uncovered (n := n) F R₂ ⊆ uncovered (n := n) F R₁ := by
  intro p hp
  rcases hp with ⟨hf, hx, hnc⟩
  refine ⟨hf, hx, ?_⟩
  intro R hR
  exact hnc R (hsub hR)

end Cover2

