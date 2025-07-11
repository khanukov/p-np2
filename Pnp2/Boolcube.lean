-- boolcube.lean – fundamental definitions.
-- Some older proofs still use `sorry`; the modern entropy‑drop lemma is
-- available fully proved in `entropy.lean`.  Requires mathlib4 ≥ 2025‑05‑20.

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Pnp2.sunflower
import Pnp2.entropy

open Sunflower
open BoolFunc

namespace Boolcube

/‑!  ### 0. Basic objects – points, subcubes, Boolean functions ‑/

variable {n : ℕ}

abbrev Point (n : ℕ) := Fin n → Bool

structure Subcube (n : ℕ) where fix : Fin n → Option Bool    -- none ⇒ "coordinate is free"

namespace Subcube

@[simp] def support (C : Subcube n) : Finset (Fin n) := Finset.univ.filter fun i ↦ (C.fix i).isSome

/‑ point x lies in C iff it matches all fixed coordinates. -/ @[simp] def Mem (C : Subcube n) (x : Point n) : Prop := ∀ i, (C.fix i).elim True fun b ↦ x i = b

@[simp] def dim (C : Subcube n) : ℕ := n - C.support.card

@[simp] def full  : Subcube n := ⟨fun _ ↦ none⟩ @[simp] def point (x : Point n) : Subcube n := ⟨fun i ↦ some (x i)⟩

@[simp] lemma mem_full  (x : Point n) : (full : Subcube n).Mem x := by intro; simp [full]

@[simp] lemma mem_point_iff (x y : Point n) : (point x).Mem y ↔ x = y := by constructor · intro h; funext i; have := h i; simp [point] at this; exact this · intro h i; simp [h, point]

/‑ Fix exactly one coordinate. -/ @[simp] def fixOne (i : Fin n) (b : Bool) : Subcube n := ⟨fun j ↦ if h : j = i then some b else none⟩

@[simp] lemma mem_fixOne_iff {i b x} :
  (fixOne (n := n) i b).Mem x ↔ x i = b := by
  constructor
  · intro h; simpa using h i
  · intro h j; by_cases hj : j = i
    · cases hj; simp [fixOne, h]
    · simp [fixOne, hj]

@[simp] lemma dim_full (n : ℕ) :
  (Subcube.full : Subcube n).dim = n := by
  classical
  simp [Subcube.dim, Subcube.support]

@[simp] lemma dim_point (x : Point n) :
  (Subcube.point (n := n) x).dim = 0 := by
  classical
  simp [Subcube.dim, Subcube.support]

end Subcube

abbrev BoolFun (n : ℕ) := Point n → Bool abbrev Family  (n : ℕ) := Finset (BoolFun n)

namespace Entropy

/‑ Collision entropy (uniform measure) – we keep only the logarithmic form. -/ @[simp] def H₂ {n} (F : Family n) : ℝ := Real.logb 2 (F.card)

lemma H₂_nonneg {F : Family n} : 0 ≤ H₂ F := by
  classical
  unfold H₂
  by_cases hF : F.card = 0
  · -- `logb` of zero is zero by definition
    simp [hF]
  ·
    have hb : (1 : ℝ) < 2 := by norm_num
    have hx : 1 ≤ (F.card : ℝ) := by
      have hpos : 0 < F.card := Nat.pos_of_ne_zero hF
      exact_mod_cast Nat.succ_le_of_lt hpos
    have := Real.logb_nonneg (b := 2) hb hx
    simpa using this

end Entropy

/‑!  ### 1.  Entropy‑drop lemma  ‑/

open Entropy

-- Coordinate‑entropy drop (cardinal version).  For a nonempty family of
-- points and `n ≥ 2`, there exists a coordinate `i` and bit `b` such that
-- fixing that bit drops the family size by at least `|F| / n`.
/-- Subfamily of `F` consisting of points whose value at `i` equals `b`. -/
def coordSlice (i : Fin n) (b : Bool) (F : Finset (Point n)) :
    Finset (Point n) :=
  F.filter (fun x ↦ x i = b)

namespace coordSlice

@[simp] lemma card_le (i : Fin n) (b : Bool) (F : Finset (Point n)) :
    (coordSlice i b F).card ≤ F.card :=
  card_filter_le _ _

@[simp] lemma disj (i : Fin n) (F : Finset (Point n)) :
    Disjoint (coordSlice i true F) (coordSlice i false F) := by
  intro x hxT hxF
  simp [coordSlice] at hxT hxF
  cases hxT.2.trans hxF.2

lemma partition (i : Fin n) (F : Finset (Point n)) :
    (coordSlice i true F).card + (coordSlice i false F).card = F.card := by
  classical
  have hdisj := disj i F
  have hunion : (coordSlice i true F) ∪ (coordSlice i false F) = F := by
    ext x; simp [coordSlice, Bool.decEq_true, Bool.decEq_false]
  simpa [hunion] using card_union_of_disjoint (s := coordSlice i true F)
    (t := coordSlice i false F) hdisj

end coordSlice

open coordSlice

lemma exists_coord_card_drop
    (hn : 2 ≤ n)
    {F : Finset (Point n)} (hF : F.Nonempty) :
    ∃ i : Fin n, ∃ b : Bool,
      (coordSlice i b F).card ≤ F.card - F.card / n := by
  classical
  by_contra h
  push_neg at h
  have hsum (i : Fin n) :
      (coordSlice i true F).card > F.card - F.card / n ∧
      (coordSlice i false F).card > F.card - F.card / n := h i
  have hlt : (coordSlice 0 true F).card + (coordSlice 0 false F).card
                > 2 * (F.card - F.card / n) := by
    have hi := hsum 0
    have hadd := add_lt_add_of_lt_of_lt hi.1 hi.2
    simpa [two_mul] using hadd
  have hEq : (coordSlice 0 true F).card + (coordSlice 0 false F).card = F.card :=
    partition 0 F
  have : (F.card : ℝ) > 2 * (F.card - F.card / n) := by
    have hEq' := congrArg (fun k : ℕ => (k : ℝ)) hEq
    have hlt' : ((coordSlice 0 true F).card + (coordSlice 0 false F).card : ℝ)
        > 2 * ((F.card - F.card / n) : ℝ) := by exact_mod_cast hlt
    simpa [hEq'] using hlt'
  have rhs_le : 2 * (F.card - F.card / n) ≤ (F.card : ℝ) := by
    have : (n : ℝ) ≥ 2 := by exact_mod_cast hn
    have hdiv : (F.card : ℝ) / n ≤ (F.card : ℝ) / 1 := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hpos : (0 : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast (Nat.zero_le _)
      exact div_le_div_of_le_of_nonneg hpos this
    nlinarith
  have hcontr := lt_of_lt_of_le this rhs_le
  exact lt_irrefl _ hcontr

-- Entropy version.  From the cardinal drop we derive a quantitative decrease of
-- `H₂`.  Using `log₂ (1 - 1/n) ≤ -1 / (n * ln 2)`.
lemma exists_coord_entropy_drop
    (F : Family n) (hn : 0 < n) (hF : 1 < F.card) :
    ∃ i : Fin n, ∃ b : Bool,
      H₂ (F.restrict i b) ≤ H₂ F - 1 := by
  classical
  simpa using
    (BoolFunc.exists_coord_entropy_drop (F := F) (hn := hn) (hF := hF))


/-!  ### 2.  High‑level cover structure and recursive constructor -/

namespace Boolcube

structure LabeledCube (n : ℕ) (F : Family n) where
  cube : Subcube n
  bit  : Bool
  mono : ∀ f ∈ F, ∀ x, cube.Mem x → f x = bit

namespace LabeledCube

/-- A cube that fixes a single coordinate to the given bit. -/
@[simp] def fixOneLabel {n} (i : Fin n) (b : Bool) (F : Family n) :
    LabeledCube n F :=
  { cube := Subcube.fixOne i b
    bit  := b
    mono := by
      intro f hf x hx
      have hxi : x i = b := (Subcube.mem_fixOne_iff).mp hx
      simpa [hxi] }

/-- A cube obtained from an arbitrary `Subcube`. -/
@[simp] def ofSubcube {n} {F : Family n} (C : Subcube n) (b : Bool)
    (hmono : ∀ f ∈ F, ∀ x, C.Mem x → f x = b) : LabeledCube n F :=
  ⟨C, b, hmono⟩

end LabeledCube

/-- A *cover* is a finite set of labeled cubes that together cover
all `1`‑points of every function in `F`. -/
structure Cover {n : ℕ} (F : Family n) where
  cubes  : Finset (LabeledCube n F)
  cover₁ : ∀ f ∈ F, ∀ x, f x = true → ∃ C ∈ cubes, C.cube.Mem x

/- Sunflower step lemma from early drafts (deprecated).
-- The current development in `cover.lean` relies directly on the fully
-- formalised `Sunflower.sunflower_exists` from `sunflower.lean`, so this
-- placeholder proof has been removed.

/-- **Recursive construction** of a `Cover` for any family `F`.  The algorithm
alternates two steps until the family becomes empty:
1. **Sunflower step** – if `sunflower_exists` succeeds we extract a
   monochromatic subcube of positive dimension, add it to the cover and remove
   every function already covered by that cube.
2. **Entropy step** – otherwise we perform an entropy‑drop split given by
   `exists_coord_card_drop`, filter the family and recurse.

Termination measure: the cardinality `F.card` strictly decreases in every
iteration. -/
noncomputable def buildCover : ∀ {n : ℕ}, (F : Family n) → Cover F
| 0, F =>
  { cubes := ∅,
    cover₁ := by
      intro f hf x hx
      cases hf } -- empty family
| (n+1), F =>
  if hF0 : F.card = 0 then
    { cubes := ∅,
      cover₁ := by
        intro f hf x hx
        have : f ∈ (F : Finset _) := hf
        have : (0 : ℕ) < F.card := by
          have := Finset.card_pos.mpr ⟨f, hf⟩; linarith
        exact False.elim (by
          have := by simpa using this; linarith) }
  else
    have hFpos : 0 < F.card := by
      have := Nat.pos_of_ne_zero hF0
      simpa using this
    have hn_pos : 0 < n.succ := Nat.succ_pos _
    (by
      by_cases hs : ∃ C b, (∀ f ∈ F, ∀ x, C.Mem x → f x = b) ∧ 1 ≤ C.dim :=
        by
          cases hs with
          | intro C b hmono hdim =>
            let F' : Family (n+1) :=
              F.filter fun f ↦ ¬(∀ x, C.Mem x → f x = b)
            let recCover := buildCover (F := F')
            exact {
              cubes := recCover.cubes.insert (LabeledCube.ofSubcube C b hmono),
              cover₁ := by
                intro f hf x hfx
                by_cases hfull : (∀ x, C.Mem x → f x = b)
                · refine ?_
                  refine ⟨_,?_,?⟩
                  · apply Finset.mem_insert_self
                  · have : C.Mem x := ?_
                    sorry
                ·
                  have hF' : f ∈ F' := by
                    simp [F', hfull, hf]
                  obtain ⟨C', hC'mem, hCx⟩ := recCover.cover₁ f hF' x hfx
                  exact ⟨C', by simp [hC'mem], hCx⟩ } )
        (fun hNoSunflower ↦
          by
            obtain ⟨i, b, hcard⟩ := exists_coord_card_drop F hn_pos hFpos
            let F' : Family (n+1) := F.filter fun f ↦ ∃ x, x i = b
            let recCover := buildCover (F := F')
            exact {
              cubes := recCover.cubes.insert (LabeledCube.fixOneLabel i b F),
              cover₁ := by
                intro f hf x hfx
                by_cases hxi : x i = b
                ·
                  have : C : LabeledCube (n+1) F := LabeledCube.fixOneLabel i b F
                  by_cases hfxi : f x = b
                  · refine ⟨this, ?_, ?_⟩
                    · simp [Finset.mem_insert]
                    ·
                      have hmem : this.cube.Mem x := by
                        simpa [LabeledCube.fixOneLabel, Subcube.mem_fixOne_iff, hxi]
                      exact hmem
                  ·
                    have hfF' : f ∈ F' := by
                      simp [F', hf, hxi] at *
                    obtain ⟨C', hC'mem, hCx⟩ := recCover.cover₁ f hfF' x hfx
                    exact ⟨C', by simp [Finset.mem_insert, hC'mem], hCx⟩
                ·
                  classical
                  have hy : ∃ y, y i = b :=
                    ⟨fun _ => b, by simp⟩
                  have hfF' : f ∈ F' := by
                    simpa [F', hy, hf] using (show f ∈ F ∧ (∃ y, y i = b) from ⟨hf, hy⟩)
                  obtain ⟨C', hC'mem, hCx⟩ := recCover.cover₁ f hfF' x hfx
                  exact ⟨C', by simp [Finset.mem_insert, hC'mem], hCx⟩
            }) )

end Boolcube
