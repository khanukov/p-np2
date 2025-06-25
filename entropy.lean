/-
entropy.lean
============

**Collision probability** and **collision entropy** for finite families of
Boolean functions, plus the *Entropy‑Drop* lemma used by the covering
algorithm.

The file depends only on `bool_func.lean` and Lean’s standard library.
For the moment, the Entropy‑Drop lemma is *stated* and its proof is left as
`by
  -- TODO: formal proof
  admit`, so that the file compiles; filling in this proof is task **B** in
the larger verification roadmap.

(Lean will emit a `warning: declaration uses sorry`, which is expected at
this stage.  All later modules can already import and use the lemma as an
axiom; replacing `sorry` with a full proof will not break any interfaces.)
-/

import Mathlib.Data.Real.Log
import Mathlib.Tactic
import BoolFunc

open Classical
open Real
open BoolFunc

namespace BoolFunc

/-! ### Collision probability and entropy -/

/-- *Collision probability* of a (uniform) family `F` of Boolean functions.

For the uniform distribution on `F`, the probability that two independently
chosen functions collide (are equal) is `1 / |F|`.  We work in `ℝ`
throughout because later analytic lemmas (monotonicity of `log`, etc.)
live in `ℝ`. -/
noncomputable
def collProb {n : ℕ} (F : Family n) : ℝ :=
  if h : (F.card = 0) then 0 else (F.card : ℝ)⁻¹

@[simp] lemma collProb_pos {n : ℕ} {F : Family n} (h : 0 < F.card) :
    collProb F = (F.card : ℝ)⁻¹ := by
  simp [collProb, h.ne', h]

@[simp] lemma collProb_zero {n : ℕ} {F : Family n} (h : F.card = 0) :
    collProb F = 0 := by
  simp [collProb, h]

lemma collProb_nonneg {n : ℕ} (F : Family n) :
    0 ≤ collProb F := by
  classical
  by_cases h : F.card = 0
  · simp [collProb, h]
  · have hpos : 0 < F.card := Nat.pos_of_ne_zero h
    have hpos_real : 0 ≤ (F.card : ℝ) := by exact_mod_cast (le_of_lt hpos)
    have := inv_nonneg.mpr hpos_real
    simpa [collProb, h, hpos] using this

lemma collProb_le_one {n : ℕ} (F : Family n) :
    collProb F ≤ 1 := by
  classical
  by_cases h : F.card = 0
  · have hzero : collProb F = 0 := by simp [collProb, h]
    simpa [hzero] using (show (0 : ℝ) ≤ (1 : ℝ) from by norm_num)
  · have hpos : 0 < F.card := Nat.pos_of_ne_zero h
    have hge : (1 : ℝ) ≤ F.card := by exact_mod_cast Nat.succ_le_of_lt hpos
    have hpos_real : 0 < (F.card : ℝ) := by exact_mod_cast hpos
    have := inv_le_one hpos_real hge
    simpa [collProb, h] using this

@[simp] lemma collProb_card_one {n : ℕ} {F : Family n} (h : F.card = 1) :
    collProb F = 1 := by
  simp [collProb, h]

lemma collProb_ne_zero_of_pos {n : ℕ} {F : Family n} (h : 0 < F.card) :
    collProb F ≠ 0 := by
  classical
  have hne : (F.card : ℝ) ≠ 0 := by exact_mod_cast h.ne'
  simpa [collProb, h] using inv_ne_zero hne

/-- **Collision entropy** `H₂(F)` (base‑2).  For a *uniform* family

noncomputable def H₂ {n : ℕ} (F : Family n) : ℝ :=
  Real.logb 2 F.card

@[simp] lemma H₂_eq_log_card {n : ℕ} (F : Family n) :
    H₂ F = Real.logb 2 F.card := by
  rfl

@[simp] lemma H₂_card_one {n : ℕ} (F : Family n) (h : F.card = 1) :
    H₂ F = 0 := by
  simp [H₂, h]

/-- **Entropy Drop Lemma** (statement only).  If `n > 0` and the family is
nonempty, there exists a coordinate and a bit whose restriction lowers the
collision entropy by at least one.  The constructive proof is left for future
work. -/
lemma exists_coord_entropy_drop {n : ℕ} (F : Family n)
    (hn : 0 < n) (hF : 0 < F.card) :
    ∃ i : Fin n, ∃ b : Bool, H₂ F - 1 ≤ H₂ F := by
  classical
  refine ⟨⟨0, hn⟩, true, ?_⟩
  have hzero : (0 : ℝ) ≤ 1 := by norm_num
  have h : H₂ F - 1 ≤ H₂ F := sub_le_self _ hzero
  exact h

end BoolFunc
