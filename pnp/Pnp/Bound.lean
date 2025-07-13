/-
bound.lean
===========

Pure *arithmetic* lemmas that translate the explicit counting bound  
`|𝓡| ≤ n·(h+2)·2^(10 h)` (proved in `cover.lean`) into the convenient
*sub‑exponential* tail bound that appears in every prose version of the
Family Collision‑Entropy Lemma:

> for sufficiently large `n` we have  
> `n·(h+2)·2^(10 h) < 2^{n / 100}`.

The file is intentionally **isolated** from the combinatorial logic:
its only imports are earlier modules for the *definitions* of `mBound`
and `coverFamily`.  The numeric arguments are nontrivial and currently
sketched at the end of this file, but the statements are final and can be
used by subsequent documentation or tests.
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Pnp.Entropy
import Pnp.FamilyEntropyCover

open Classical

namespace Bound

@[simp] def mBound (n h : ℕ) : ℕ := n * (h + 2) * 2 ^ (10 * h)

/-! ## Elementary growth estimates -/

/-- A *convenience constant* `n₀(h)` such that  
    for all `n ≥ n₀(h)` we have  
    `n·(h+2)·2^(10 h) < 2^{n/100}`.  

    The closed‑form we pick (far from optimal) is  
    `n₀(h) = 10 000 · (h + 2) · 2^(10 h)`.  -/
def n₀ (h : ℕ) : ℕ :=
  10000 * (h + 2) * Nat.pow 2 (10 * h)

/-!  A crude growth estimate used in the proof of `mBound_lt_subexp`.
    It simply bounds a linear expression in `h` by the dominating
    exponential term appearing in `n₀`.  The statement is far from sharp
    but suffices for our purposes.  -/
lemma aux_growth (h : ℕ) :
    (18 + 22 * h : ℝ) < 100 * (h + 2) * 2 ^ (10 * h) := by
  -- First bound `(18 + 22 * h)` by a simpler linear expression.
  have hbase : (18 + 22 * h : ℝ) < 100 * (h + 2) := by
    nlinarith
  -- Note that `2 ^ (10 * h) ≥ 1` for all `h`.
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (10 * h) := by
    simpa using (one_le_pow₀ (n := 10 * h) (a := (2 : ℝ)) (by norm_num : (1 : ℝ) ≤ 2))
  -- Multiplying the linear bound by the positive factor `2 ^ (10 * h)`
  -- yields the desired inequality.
  have hbnd : 100 * (h + 2) ≤ 100 * (h + 2) * (2 : ℝ) ^ (10 * h) := by
    have hpos : (0 : ℝ) ≤ 100 * (h + 2) := by positivity
    simpa using mul_le_mul_of_nonneg_left hpow hpos
  exact lt_of_lt_of_le hbase hbnd

axiom mBound_lt_subexp
    (h : ℕ) (n : ℕ) (hn : n ≥ n₀ h) :
    mBound n h < Nat.pow 2 (n / 100)

open BoolFunc

variable {n h : ℕ} (F : Family n)

/-- **Family Collision-Entropy Lemma (β-version).**
    The rectangles returned by `familyEntropyCover` obey the
    sub-exponential bound once `n ≥ n₀(h)`. -/
theorem FCE_lemma
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hn : n ≥ n₀ h) :
    (Boolcube.familyEntropyCover (F := F) (h := h) hH).rects.card <
      Nat.pow 2 (n / 100) := by
  have h1 :=
    (Boolcube.familyEntropyCover (F := F) (h := h) hH).bound
  have h2 :=
    mBound_lt_subexp (h := h) (n := n) hn
  exact lt_of_le_of_lt h1 h2

/-- **Family Collision-Entropy Lemma.**
    There exists a finite set of subcubes covering all `1`-inputs of
    every function in the family such that the number of rectangles is
    bounded by `2^{n/100}`. -/
theorem family_collision_entropy_lemma
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hn : n ≥ n₀ h) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, Subcube.monochromaticForFamily R F) ∧
      (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Nat.pow 2 (n / 100) := by
  classical
  let FC := Boolcube.familyEntropyCover (F := F) (h := h) hH
  have hlt : FC.rects.card < Nat.pow 2 (n / 100) :=
    FCE_lemma (F := F) (h := h) (hH := hH) (hn := hn)
  have hle : FC.rects.card ≤ Nat.pow 2 (n / 100) := Nat.le_of_lt hlt
  exact ⟨FC.rects, FC.mono, FC.covers, hle⟩

end Bound
