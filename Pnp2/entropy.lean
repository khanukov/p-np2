/-
entropy.lean
============

This module sketches a collision-entropy framework.  Some of the proofs
are still incomplete (`sorry`), but the definitions can be imported by
other files.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
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
  -- Proof omitted
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
`Family.restrict i b` applies `BFunc.restrictCoord` to every function in `F`, fixing the `i`-th input bit to `b`.  This may identify previously distinct functions, so the resulting family can have smaller cardinality.  The next two helper lemmas are straightforward bookkeeping about these cardinalities and need no additional imports.
-/

lemma card_restrict_le {n : ℕ} (F : Family n) (i : Fin n) (b : Bool) :
    (F.restrict i b).card ≤ F.card := by
  classical
  -- Proof omitted
  sorry

/-- Discrete halving lemma for a single Boolean function: one of the two
restrictions fixes at most half of the `true` inputs. -/
lemma exists_restrict_half_prob {n : ℕ} [Fintype (Point n)] (f : BFunc n) :
    ∃ i : Fin n,
      (ones (BFunc.restrictCoord f i false)).card ≤ (ones f).card / 2 ∨
      (ones (BFunc.restrictCoord f i true)).card ≤ (ones f).card / 2 := by
  classical
  -- Proof omitted
  sorry

lemma exists_restrict_half {n : ℕ} (F : Family n) (hn : 0 < n) (hF : 1 < F.card) :
    ∃ i : Fin n, ∃ b : Bool, (F.restrict i b).card ≤ F.card / 2 := by
  classical
  -- Proof omitted
  sorry

-- The above arithmetic on naturals is tedious; a simpler *real* argument will
-- be used in the entropy proof, so we postpone nat‑level clean‑up and rely on
-- `exists_restrict_half` proven below with reals.

/-- **Existence of a halving restriction (ℝ version)** – a cleaner proof in
ℝ, avoiding intricate Nat‑arithmetic. We reuse it in the entropy drop proof.
-/
lemma exists_restrict_half_real_aux {n : ℕ} (F : Family n) (hn : 0 < n)
    (hF : 1 < F.card) : ∃ i : Fin n, ∃ b : Bool,
    ((F.restrict i b).card : ℝ) ≤ (F.card : ℝ) / 2 := by
  classical
  -- Proof omitted
  sorry

/-- **Existence of a halving restriction (ℝ version)** – deduced from the
integer statement. -/
lemma exists_restrict_half_real {n : ℕ} (F : Family n) (hn : 0 < n)
    (hF : 1 < F.card) : ∃ i : Fin n, ∃ b : Bool,
    ((F.restrict i b).card : ℝ) ≤ (F.card : ℝ) / 2 := by
  classical
  -- Proof omitted
  sorry

/-- **Entropy‑Drop Lemma.**  There exists a coordinate / bit whose
restriction lowers collision entropy by ≥ 1 bit. -/
lemma exists_coord_entropy_drop {n : ℕ} (F : Family n)
    (hn : 0 < n) (hF : 1 < F.card) :
    ∃ i : Fin n, ∃ b : Bool,
      H₂ (F.restrict i b) ≤ H₂ F - 1 := by
  classical
  -- Proof omitted
  sorry

/-- Auxiliary lemma translating a discrete cardinal bound for a restricted
function into a real-valued probability bound. -/
lemma discrete_to_real_bound {n : ℕ} [Fintype (Point n)]
    (f : BFunc n) (i : Fin n) (ε : ℝ) :
    (ones (BFunc.restrictCoord f i false)).card ≤ (ones f).card / 2 →
    ε > 0 →
    prob_restrict_false f i ≤ (1 - ε) / 2 := by
  intro h_discrete hε
  -- Proof omitted
  sorry

/-- **Existence of a halving restriction (probability version).**  There exists
a coordinate whose conditional probability of outputting `true` is at most
`(1 - ε) / 2`. -/
lemma exists_restrict_half_real_prob {n : ℕ} [Fintype (Point n)]
    (f : BFunc n) (ε : ℝ) (hε : ε > 0) :
    ∃ i : Fin n,
      prob_restrict_false f i ≤ (1 - ε) / 2 ∨
      prob_restrict_true f i ≤ (1 - ε) / 2 := by
  classical
  -- Proof omitted
  sorry

end BoolFunc
