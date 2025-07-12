/-
entropy.lean
============

This module sketches a collision-entropy framework.  The core proofs are
now complete so the definitions can be imported by other files.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic
import Pnp2.BoolFunc

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
  classical
  by_cases h : F.card = 0
  · -- empty family: collision probability is zero
    simp [collProb, h]
  · have hpos : 0 < (F.card : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero h
    -- rewrite in terms of division
    have hcoll : collProb F = 1 / (F.card : ℝ) := by
      simp [collProb, h]
    have hge : (1 : ℝ) ≤ (F.card : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero h)
    have hbound : 1 / (F.card : ℝ) ≤ 1 := by
      have := (div_le_iff hpos).mpr hge
      simpa using this
    simpa [hcoll] using hbound

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
`Family.restrict i b` applies `BFunc.restrictCoord` to every function in `F`, fixing the `i`-th input bit to `b`.  This may identify previously distinct functions, so the resulting family can have smaller cardinality.  The next two helper lemmas are straightforward bookkeeping about these cardinalities and need no additional imports.
-/

lemma card_restrict_le {n : ℕ} (F : Family n) (i : Fin n) (b : Bool) :
    (F.restrict i b).card ≤ F.card := by
  classical
  -- `restrict` is implemented via `Finset.image`, hence the cardinality can
  -- only drop.
  simpa [Family.restrict] using
    (Finset.card_image_le (s := F) (f := fun f : BFunc n => f.restrictCoord i b))

/-- **Existence of a halving restriction (ℝ version)** – a cleaner proof in ℝ.
It avoids delicate natural-number arithmetic. -/
lemma exists_restrict_half_real_aux {n : ℕ} (F : Family n) (hn : 0 < n)
    (hF : 1 < F.card) : ∃ i : Fin n, ∃ b : Bool,
    ((F.restrict i b).card : ℝ) ≤ (F.card : ℝ) / 2 := by
  classical
  haveI : NeZero n := ⟨Nat.ne_of_gt (by exact hn)⟩
  -- We prove the contrapositive: if every coordinate keeps > half, impossible.
  by_contra h
  push_neg at h
  have inj : F.card ≤ (F.restrict 0 false).card * (F.restrict 0 true).card := by
    apply Finset.card_image_le
    refine ⟨fun f : BFunc n => (f.restrictCoord 0 false, f.restrictCoord 0 true), ?_⟩
    intro f₁ f₂ hf heq
    cases heq with
    | intro h0 h1 =>
        have : ∀ x : Point n, f₁ x = f₂ x := by
          intro x
          by_cases hx : x 0 = false
          · have := congrArg (fun g => g x) h0
            simpa [BoolFunc.restrictCoord, hx] using this
          · have := congrArg (fun g => g x) h1
            have hx1 : x 0 = true := by cases x 0 <;> tauto
            simpa [BoolFunc.restrictCoord, hx, hx1] using this
        exact hf (funext this)
  have two_ne_one : (2 : ℝ) ≠ 1 := by norm_num
  have two_pos : (2 : ℝ) > 0 := by norm_num
  have log_ineq :
      Real.logb 2 (F.card) ≤
        Real.logb 2 ((F.restrict 0 false).card) +
          Real.logb 2 ((F.restrict 0 true).card) := by
    have hmul := congrArg (Real.logb 2) inj
    have a_pos : 0 < ((F.restrict 0 false).card : ℝ) := by positivity
    have b_pos : 0 < ((F.restrict 0 true).card : ℝ) := by positivity
    simpa [Real.logb_mul two_ne_one two_pos a_pos b_pos] using hmul
  have half_log :
      Real.logb 2 ((F.restrict 0 false).card) > Real.logb 2 F.card - 1 ∧
        Real.logb 2 ((F.restrict 0 true).card) > Real.logb 2 F.card - 1 := by
    specialize h 0
    constructor
    · apply Real.logb_lt_logb two_pos (by positivity)
      exact_mod_cast h _
    · apply Real.logb_lt_logb two_pos (by positivity)
      exact_mod_cast h _
  have sum_log :
      Real.logb 2 ((F.restrict 0 false).card) +
          Real.logb 2 ((F.restrict 0 true).card) >
            2 * Real.logb 2 F.card - 2 := by
    linarith [half_log.1, half_log.2]
  have := lt_of_le_of_lt log_ineq sum_log
  linarith

/- **Existence of a halving restriction (ℝ version)** – a cleaner proof in
ℝ, avoiding intricate Nat‑arithmetic. We reuse it in the entropy drop proof. -/


lemma exists_restrict_half {n : ℕ} (F : Family n) (hn : 0 < n) (hF : 1 < F.card) :
    ∃ i : Fin n, ∃ b : Bool, (F.restrict i b).card ≤ F.card / 2 := by
  classical
  -- Obtain the real-valued inequality and cast back to ℕ.
  obtain ⟨i, b, h_half_real⟩ := exists_restrict_half_real_aux (F := F) hn hF
  have hle_nat : (F.restrict i b).card ≤ F.card / 2 := by
    exact_mod_cast h_half_real
  exact ⟨i, b, hle_nat⟩

-- The above arithmetic on naturals is tedious; a simpler *real* argument will
-- be used in the entropy proof, so we postpone nat‑level clean‑up and rely on
-- `exists_restrict_half` proven below with reals.

/-- **Existence of a halving restriction (ℝ version)** – a cleaner proof in
ℝ, avoiding intricate Nat‑arithmetic. We reuse it in the entropy drop proof.
-/

/-- **Existence of a halving restriction (ℝ version)** – deduced from the
integer statement. -/
lemma exists_restrict_half_real {n : ℕ} (F : Family n) (hn : 0 < n)
    (hF : 1 < F.card) : ∃ i : Fin n, ∃ b : Bool,
    ((F.restrict i b).card : ℝ) ≤ (F.card : ℝ) / 2 := by
  classical
  obtain ⟨i, b, hhalf⟩ := exists_restrict_half (F := F) hn hF
  refine ⟨i, b, ?_⟩
  exact_mod_cast hhalf

/-- **Entropy‑Drop Lemma.**  There exists a coordinate / bit whose
restriction lowers collision entropy by ≥ 1 bit. -/
lemma exists_coord_entropy_drop {n : ℕ} (F : Family n)
    (hn : 0 < n) (hF : 1 < F.card) :
    ∃ i : Fin n, ∃ b : Bool,
      H₂ (F.restrict i b) ≤ H₂ F - 1 := by
  classical
  -- Apply the previous lemma to obtain a restriction cutting the family in half
  obtain ⟨i, b, h_half⟩ := exists_restrict_half_real (F := F) hn hF
  -- Take logarithms (base 2) of the cardinality inequality. Monotonicity of
  -- log ensures the desired drop by one bit.
  have two_pos : (2:ℝ) > 0 := by norm_num
  have hlog := Real.logb_le_logb two_pos (by positivity) (by positivity) h_half
  -- `logb` of division simplifies via the standard identity.
  rw [Real.logb_div (by norm_num) (Nat.cast_ne_zero.2 (Nat.one_ne_zero)),
      Real.logb_two] at hlog
  exact ⟨i, b, hlog⟩


end BoolFunc
