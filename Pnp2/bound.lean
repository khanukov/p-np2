/-
bound.lean
===========

Pure *arithmetic* lemmas that translate the explicit counting bound
`|𝓡| ≤ n·3^n·(h+2)·2^(10 h)` (proved in `cover2.lean`) into the more usable
tail estimates that appear in the narrative of the Family Collision–Entropy
Lemma.  While the catalogue grows exponentially in `n`, it is still controlled
by a small power of the ambient truth-table size `2^n`; the lemmas below make
this quantitative.

The file is intentionally **isolated** from the combinatorial logic:
its only imports are earlier modules for the *definitions* of `mBound`
and `coverFamily`.  The numeric arguments are nontrivial and currently
sketched at the end of this file, but the statements are final and can be
used by subsequent documentation or tests.
-/

import Pnp2.cover2
import Pnp2.family_entropy_cover
import Mathlib.Tactic

open Classical
open Cover2
open Boolcube

namespace Bound

/-! ## Elementary growth estimates -/

/-- A *convenience constant* `n₀(h)` kept for backwards compatibility with the
legacy presentation of the numeric bounds.  None of the new inequalities below
depend on it, but existing documentation still references the guard. -/
def n₀ (h : ℕ) : ℕ :=
  10000 * (h + 2) * Nat.pow 2 (10 * h)

/-!  A crude growth estimate retained for downstream tests.  It bounds a linear
    expression in `h` by the dominating exponential term appearing in `n₀`.  The
    statement is far from sharp but suffices for sanity checks.  -/
lemma aux_growth (h : ℕ) :
    (18 + 22 * h : ℝ) < 100 * (h + 2) * 2 ^ (10 * h) := by
  -- The inequality clearly holds for small `h` by direct computation.
  -- For larger `h` the right-hand side grows extremely fast since it
  -- contains `2^(10*h)`.
  induction' h with d hd
  · norm_num
  · -- Use the induction hypothesis for `d` and compare to the next step.
    have hd' : (18 + 22 * d : ℝ) < 100 * (d + 2) * 2 ^ (10 * d) := hd
    -- First, bound the linear growth on the left by a large multiple of the
    -- previous step.
    have hbound :
        (18 + 22 * (d + 1) : ℝ) ≤ 1024 * (18 + 22 * d) := by
      have hdiff :
          1024 * (18 + 22 * d) - (18 + 22 * (d + 1))
            = (18 + 22 * d) * 1023 - 22 := by
        ring
      -- The right-hand side is clearly positive: `(18 + 22*d) ≥ 18` and the
      -- massive factor `1023` dominates the small subtraction.
      have hnonneg :
          0 ≤ (18 + 22 * d : ℝ) * 1023 - 22 := by
        have hge : (18 : ℝ) ≤ 18 + 22 * d := by
          have : (0 : ℝ) ≤ 22 * d := by positivity
          linarith
        have hmul_ge :
            (18 : ℝ) * 1023 ≤ (18 + 22 * d) * 1023 := by
          exact mul_le_mul_of_nonneg_right hge (by norm_num : (0 : ℝ) ≤ 1023)
        have hconst : (0 : ℝ) ≤ (18 : ℝ) * 1023 - 22 := by norm_num
        exact le_trans hconst (sub_le_sub_right hmul_ge 22)
      exact sub_nonneg.mp (by simpa [hdiff] using hnonneg)
    -- Strengthen the RHS via the induction hypothesis.
    have hlt :
        1024 * (18 + 22 * d)
          < 1024 * (100 * (d + 2) * 2 ^ (10 * d)) := by
      have hpos : (0 : ℝ) < 1024 := by norm_num
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (mul_lt_mul_of_pos_left hd' hpos)
    -- Finally, compare the catalogue growth at successive steps.
    have hstep :
        1024 * (100 * (d + 2) * 2 ^ (10 * d))
          ≤ 100 * (d + 3) * 2 ^ (10 * (d + 1)) := by
      have hbase :
          (100 * (d + 2) * 2 ^ (10 * d) : ℝ)
            ≤ 100 * (d + 3) * 2 ^ (10 * d) := by
        have hle : (d + 2 : ℝ) ≤ d + 3 := by norm_num
        have hpos : (0 : ℝ) ≤ 100 * 2 ^ (10 * d) := by positivity
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (mul_le_mul_of_nonneg_left hle hpos)
      have :
          1024 * (100 * (d + 2) * 2 ^ (10 * d))
            ≤ 1024 * (100 * (d + 3) * 2 ^ (10 * d)) := by
        have hpos : (0 : ℝ) ≤ 1024 := by norm_num
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (mul_le_mul_of_nonneg_left hbase hpos)
      simpa [pow_add, pow_succ, mul_comm, mul_left_comm, mul_assoc] using this
    exact lt_of_le_of_lt hbound (lt_of_lt_of_le hlt hstep)

/-! ## Bounding the catalogue size by a power of two -/

lemma two_pow_ge_self (k : ℕ) : k ≤ 2 ^ k := by
  induction' k with k hk
  · simp
  · have hk' : k + 1 ≤ 2 ^ k + 1 := Nat.succ_le_succ hk
    have hpow : 1 ≤ 2 ^ k := Nat.succ_le_of_lt (pow_pos (by decide) _)
    have hsum : 2 ^ k + 1 ≤ 2 ^ k + 2 ^ k := by
      have := Nat.add_le_add_left hpow (2 ^ k)
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
    have := le_trans hk' hsum
    simpa [pow_succ, two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using this

/-- The explicit catalogue bound is at most `2^{3 n + 11 h + 2}`.  Interpreted in
terms of the truth-table size `N = 2^n`, this gives a cubic bound
`mBound n h ≤ N^3 · 2^{11 h + 2}`.  The constants are intentionally generous,
keeping the algebraic proof short while providing a practical global estimate. -/
lemma mBound_le_two_pow_linear (n h : ℕ) :
    mBound n h ≤ Nat.pow 2 (3 * n + 11 * h + 2) := by
  have hn : n ≤ 2 ^ n := two_pow_ge_self n
  have hthree : 3 ^ n ≤ 2 ^ (2 * n) := by
    have hpow := Nat.pow_le_pow_left (by decide : 3 ≤ 4) n
    have hfour : (4 : ℕ) = 2 ^ 2 := by norm_num
    have hpow' : 4 ^ n = 2 ^ (2 * n) := by
      have := (pow_mul (2 : ℕ) 2 n).symm
      simpa [hfour, pow_mul, two_mul, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc] using this
    simpa [hpow'] using hpow
  have hh : h + 2 ≤ 2 ^ (h + 2) := two_pow_ge_self (h + 2)
  have hprod₁ : n * 3 ^ n ≤ 2 ^ n * 2 ^ (2 * n) :=
    Nat.mul_le_mul hn hthree
  have hprod₂ : n * 3 ^ n * (h + 2)
      ≤ (2 ^ n * 2 ^ (2 * n)) * 2 ^ (h + 2) :=
    Nat.mul_le_mul hprod₁ hh
  have hprod₃ :
      n * 3 ^ n * (h + 2) * 2 ^ (10 * h)
        ≤ ((2 ^ n * 2 ^ (2 * n)) * 2 ^ (h + 2)) * 2 ^ (10 * h) :=
    Nat.mul_le_mul_right _ hprod₂
  have hrewrite :
      ((2 ^ n * 2 ^ (2 * n)) * 2 ^ (h + 2)) * 2 ^ (10 * h)
        = 2 ^ (3 * n + 11 * h + 2) := by
    simp [pow_add, add_comm, add_left_comm, add_assoc, two_mul,
      Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  simpa [mBound, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, hrewrite]
    using hprod₃

open Boolcube

variable {n h : ℕ} (F : Family n)

/-- The size bound from `familyEntropyCover` yields an explicit cubic bound in
the truth-table size. -/
theorem FCE_lemma (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hn_pos : 0 < n) :
    (Boolcube.familyEntropyCover (F := F) (h := h) hH hn_pos).rects.card ≤
      Nat.pow 2 (3 * n + 11 * h + 2) := by
  have hcard :=
    (Boolcube.familyEntropyCover (F := F) (h := h) hH hn_pos).bound
  have hsub := mBound_le_two_pow_linear (n := n) (h := h)
  exact hcard.trans hsub

/-- **Family Collision-Entropy Lemma.**  A family of Boolean functions with
bounded collision entropy admits a set of monochromatic rectangles covering all
`1`-inputs whose size is at most `2^{3 n + 11 h + 2}`.  Interpreting the exponent
in terms of the truth-table size `2^n` gives a cubic bound. -/
theorem family_collision_entropy_lemma
    (hH : BoolFunc.H₂ F ≤ (h : ℝ))
    (hn_pos : 0 < n) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, ∀ g ∈ F, Boolcube.Subcube.monochromaticFor R g) ∧
      (∀ f ∈ F, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Nat.pow 2 (3 * n + 11 * h + 2) := by
  classical
  let FC := Boolcube.familyEntropyCover (F := F) (h := h) hH hn_pos
  have hle := FCE_lemma (F := F) (h := h) (hH := hH)
      (hn_pos := hn_pos)
  refine ⟨FC.rects, FC.mono, FC.covers, hle⟩

end Bound
