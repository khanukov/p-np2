/-
entropy.lean
============

This module sketches a collision-entropy framework.  Some of the proofs
are still incomplete (`sorry`), but the definitions can be imported by
other files.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic
import BoolFunc

open Classical
open Real
open BoolFunc

namespace BoolFunc

/-! ### Collision probability and entropy -/

/-- *Collision probability* of a *uniform* family `F` of Boolean functions.
We work in `ℝ` because later analytic lemmas (`log` monotonicity, etc.) live
in `ℝ`. -/
noncomputable
 def collProb {n : ℕ} (F : Family n) : ℝ :=
  if h : (F.card = 0) then 0 else (F.card : ℝ)⁻¹

@[simp] lemma collProb_pos {n : ℕ} {F : Family n} (h : 0 < F.card) :
    collProb F = (F.card : ℝ)⁻¹ := by
  simp [collProb, h.ne', h]

@[simp] lemma collProb_zero {n : ℕ} {F : Family n} (h : F.card = 0) :
    collProb F = 0 := by simp [collProb, h]

lemma collProb_nonneg {n : ℕ} (F : Family n) :
    0 ≤ collProb F := by
  by_cases h : F.card = 0
  · simp [collProb, h]
  · have : 0 < (F.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h
    simpa [collProb, h] using inv_nonneg.mpr (le_of_lt this)

lemma collProb_le_one {n : ℕ} (F : Family n) :
    collProb F ≤ 1 := by
  -- Proof currently omitted.
  sorry

@[simp] lemma collProb_card_one {n : ℕ} {F : Family n} (h : F.card = 1) :
    collProb F = 1 := by simp [collProb, h]

lemma collProb_ne_zero_of_pos {n : ℕ} {F : Family n} (h : 0 < F.card) :
    collProb F ≠ 0 := by
  have : (F.card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt h)
  simpa [collProb, h] using inv_ne_zero this

/-- **Collision entropy** `H₂(F)` (base‑2). -/
noncomputable def H₂ {n : ℕ} (F : Family n) : ℝ :=
  Real.logb 2 F.card

@[simp] lemma H₂_eq_log_card {n : ℕ} (F : Family n) :
    H₂ F = Real.logb 2 F.card := rfl

@[simp] lemma H₂_card_one {n : ℕ} (F : Family n) (h : F.card = 1) :
    H₂ F = 0 := by simp [H₂, h]

/-!
`Family.restrict i b` keeps only those functions in `F` whose value on the
coordinate `i` equals the Boolean bit `b`.  The next two helper lemmas are
straightforward bookkeeping about cardinals and need no additional imports.
-/

lemma card_partition_restrict {n : ℕ} (F : Family n) (i : Fin n) :
    (F.restrict i true).card + (F.restrict i false).card = F.card := by
  -- Placeholder proof pending library facts.
  sorry

lemma exists_restrict_half {n : ℕ} (F : Family n) (hn : 0 < n) (hF : 1 < F.card) :
    ∃ i : Fin n, ∃ b : Bool, (F.restrict i b).card ≤ F.card / 2 := by
  -- Proof omitted.
  classical
  sorry

-- The above arithmetic on naturals is tedious; a simpler *real* argument will
-- be used in the entropy proof, so we postpone nat‑level clean‑up and rely on
-- `exists_restrict_half` proven below with reals.

/-- **Existence of a halving restriction (ℝ version)** – a cleaner proof in
ℝ, avoiding intricate Nat‑arithmetic. We reuse it in the entropy drop proof.
-/
lemma exists_restrict_half_real {n : ℕ} (F : Family n) (hn : 0 < n)
    (hF : 1 < F.card) : ∃ i : Fin n, ∃ b : Bool,
    ((F.restrict i b).card : ℝ) ≤ (F.card : ℝ) / 2 := by
  classical
  -- Proof omitted.
  sorry

/-- **Entropy‑Drop Lemma.**  There exists a coordinate / bit whose
restriction lowers collision entropy by ≥ 1 bit. -/
lemma exists_coord_entropy_drop {n : ℕ} (F : Family n)
    (hn : 0 < n) (hF : 1 < F.card) :
    ∃ i : Fin n, ∃ b : Bool,
      H₂ (F.restrict i b) ≤ H₂ F - 1 := by
  -- Proof omitted.
  classical
  sorry

end BoolFunc
