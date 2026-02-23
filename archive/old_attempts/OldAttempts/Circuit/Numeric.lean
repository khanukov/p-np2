import OldAttempts.Circuit.EntropyCover
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Log

noncomputable section

open Classical

namespace Boolcube
namespace Circuit

/-- Convenience abbreviation for the exponent appearing in the cover bound. -/
def powFamilyExponentBound (n c : ℕ) : ℕ :=
  3 * n + 11 * powFamilyEntropyBound n c + 2

/-- A coarse but explicit upper bound on `powFamilyEntropyBound`.  The bound is
obtained by replacing each logarithm by its argument and by bounding the
auxiliary alphabet size `encodingAlphabet` with the naive sum `n + 4 * n^c + 5`.
Although extremely loose, the estimate suffices for later comparisons with the
ambient power `2^n`. -/
lemma powFamilyEntropyBound_le_polynomial (n c : ℕ) :
    powFamilyEntropyBound n c ≤
      4 * n ^ (c + 1) + 16 * n ^ (2 * c) + 28 * n ^ c + 2 := by
  classical
  -- Abbreviations for clarity.
  set L := encodingLength n c := 4 * n ^ c
  set A := encodingAlphabet n c := max n (4 * n ^ c) + 5
  -- Replace integer logarithms by their arguments.
  have hlog₁ : Nat.log2 (L + 1) ≤ L + 1 := by
    simpa [Nat.log2_eq_log_two] using (Nat.log_le_self (2) (L + 1))
  have hlog₂ : Nat.log2 A ≤ A := by
    simpa [Nat.log2_eq_log_two] using (Nat.log_le_self (2) A)
  -- From the definition of `powFamilyEntropyBound` we obtain a linear bound in
  -- terms of `L` and `A`.
  have hstep :
      powFamilyEntropyBound n c ≤ L * A + 2 * L + 2 := by
    have := add_le_add
      (add_le_add_right hlog₁ 1)
      (Nat.mul_le_mul_left _ (add_le_add_right hlog₂ 1))
    simpa [powFamilyEntropyBound, L, A, encodingLength, encodingAlphabet,
      Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc, Nat.add_mul, two_mul] using this
  -- Crude inequality for the alphabet size.
  have hA_le : A ≤ n + 4 * n ^ c + 5 := by
    refine Nat.add_le_add_right ?_ 5
    exact max_le
      (Nat.le_add_right _ _)
      (Nat.le_add_left _ _)
  -- Bounding the product term `L * A`.
  have hprod : L * A ≤ 4 * n ^ (c + 1) + 16 * n ^ (2 * c) + 20 * n ^ c := by
    have := Nat.mul_le_mul_left L hA_le
    simpa [L, encodingLength, Nat.mul_add, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
      Nat.pow_add, Nat.pow_succ, Nat.succ_eq_add_one] using this
  -- Bounding the remaining linear term.
  have hlin : 2 * L ≤ 8 * n ^ c := by
    simp [L, encodingLength, two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  -- Combine the pieces and regroup constants.
  have htotal : L * A + 2 * L + 2 ≤
      (4 * n ^ (c + 1) + 16 * n ^ (2 * c) + 20 * n ^ c) + 8 * n ^ c + 2 := by
    have := add_le_add hprod hlin
    exact add_le_add_right this 2
  have htarget :
      (4 * n ^ (c + 1) + 16 * n ^ (2 * c) + 20 * n ^ c) + 8 * n ^ c + 2
        = 4 * n ^ (c + 1) + 16 * n ^ (2 * c) + 28 * n ^ c + 2 := by
    ring
  exact hstep.trans (by simpa [htarget] using htotal)



/-- The exponent governing the size of the covering family grows at most like a
single monomial of degree `2c + 1`.  The constant `555` is a generous upper
bound obtained by comparing each contribution with the dominant power. -/
lemma powFamilyExponentBound_le_monomial {n c : ℕ} (hn : 1 ≤ n) :
    powFamilyExponentBound n c ≤ 555 * n ^ (2 * c + 1) := by
  classical
  have hpoly := powFamilyEntropyBound_le_polynomial (n := n) (c := c)
  have hexp_poly :
      powFamilyExponentBound n c ≤
        3 * n + 44 * n ^ (c + 1) + 176 * n ^ (2 * c) + 308 * n ^ c + 24 := by
    have hscaled := Nat.mul_le_mul_left 11 hpoly
    have hsum :
        3 * n + 11 * (4 * n ^ (c + 1) + 16 * n ^ (2 * c) + 28 * n ^ c + 2) + 2
          = 3 * n + 44 * n ^ (c + 1) + 176 * n ^ (2 * c) + 308 * n ^ c + 24 := by
      ring
    simpa [powFamilyExponentBound, hsum]
      using add_le_add_left hscaled (3 * n)
  have hpow_mono : ∀ {a b : ℕ}, a ≤ b → n ^ a ≤ n ^ b :=
    fun h => Nat.pow_le_pow_of_le_left hn h
  have hpow_ge_one : 1 ≤ n ^ (2 * c) :=
    Nat.one_le_pow_of_one_le hn _
  have hle_self_pow : n ≤ n ^ (2 * c + 1) := by
    have := Nat.mul_le_mul_left n hpow_ge_one
    simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using this
  have hterm₁ : 3 * n ≤ 3 * n ^ (2 * c + 1) :=
    Nat.mul_le_mul_left _ hle_self_pow
  have hterm₂ : 44 * n ^ (c + 1) ≤ 44 * n ^ (2 * c + 1) := by
    have hc : c + 1 ≤ 2 * c + 1 := by
      have : c ≤ 2 * c := by
        have := Nat.le_add_right c c
        simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
      exact add_le_add this (le_of_eq rfl)
    exact Nat.mul_le_mul_left _ (hpow_mono (by simpa using hc))
  have hterm₃ : 176 * n ^ (2 * c) ≤ 176 * n ^ (2 * c + 1) := by
    exact Nat.mul_le_mul_left _ (hpow_mono (Nat.le_succ _))
  have hterm₄ : 308 * n ^ c ≤ 308 * n ^ (2 * c + 1) := by
    have hc : c ≤ 2 * c := by
      have := Nat.le_add_right c c
      simpa [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
    exact Nat.mul_le_mul_left _ (hpow_mono (le_trans hc (Nat.le_succ _)))
  have hterm₅ : 24 ≤ 24 * n ^ (2 * c + 1) := by
    have hpos : 1 ≤ n ^ (2 * c + 1) :=
      Nat.one_le_pow_of_one_le hn _
    simpa using Nat.mul_le_mul_left 24 hpos
  have hbounded :
      3 * n + 44 * n ^ (c + 1) + 176 * n ^ (2 * c) + 308 * n ^ c + 24
        ≤ 555 * n ^ (2 * c + 1) := by
    have hsum := add_le_add hterm₁
      (add_le_add hterm₂ (add_le_add hterm₃ (add_le_add hterm₄ hterm₅)))
    simpa [Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using hsum
  exact hexp_poly.trans hbounded

open Filter
open scoped Real

/-- For large `n` the crude polynomial bound on the cover exponent is dwarfed by the
base-two exponential `2 ^ n`.  This technical lemma packages the analytic
statement obtained from `isLittleO_pow_exp_pos_mul_atTop` for later use in the
arithmetic inequalities. -/
private lemma eventually_monomial_le_half_pow (c : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (555 : ℝ) * (n : ℝ) ^ (2 * c + 1) ≤ (2 : ℝ) ^ n / 2 := by
  classical
  -- Choose the small multiplicative constant that will allow us to absorb the
  -- polynomial into the exponential.
  let ε : ℝ := 1 / (2 * (555 : ℝ))
  have hεpos : 0 < ε := by
    have : (0 : ℝ) < 2 * (555 : ℝ) := by norm_num
    exact one_div_pos.mpr this
  -- The general asymptotic lemma states that `n^(2c+1)` is little-o of
  -- `exp ((log 2) * n)`.
  have hLittle :
      (fun n : ℕ => (n : ℝ) ^ (2 * c + 1)) =o[atTop]
        fun n : ℕ => Real.exp (Real.log 2 * (n : ℝ)) := by
    have hlog : 0 < Real.log (2 : ℝ) := by
      have : (1 : ℝ) < 2 := by norm_num
      simpa using Real.log_pos this
    simpa [Function.comp, Nat.cast_id]
      using
        (isLittleO_pow_exp_pos_mul_atTop (k := 2 * c + 1)
            (hb := hlog)).comp_tendsto tendsto_natCast_atTop_atTop
  -- Instantiate the little-o bound with the chosen `ε`.
  have hbound := hLittle.def hεpos
  -- Simplify the inequality: the norms disappear since every term is
  -- non-negative.
  refine hbound.mono ?_
  intro n hn
  have hclean : (n : ℝ) ^ (2 * c + 1) ≤ ε * Real.exp (Real.log 2 * (n : ℝ)) := by
    have hpoly : ‖(n : ℝ) ^ (2 * c + 1)‖ = (n : ℝ) ^ (2 * c + 1) := by
      have : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le _)
      simpa [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg this _)]
    have hexp : ‖Real.exp (Real.log 2 * (n : ℝ))‖ =
        Real.exp (Real.log 2 * (n : ℝ)) := by
      simp [Real.norm_eq_abs, Real.abs_of_nonneg (Real.exp_pos _).le]
    simpa [hpoly, hexp] using hn
  have hmul := mul_le_mul_of_nonneg_left hclean (by positivity : 0 ≤ (555 : ℝ))
  have :
      (555 : ℝ) * (n : ℝ) ^ (2 * c + 1) ≤
        (555 : ℝ) * ε * Real.exp (Real.log 2 * (n : ℝ)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  -- Reduce the right-hand side to a base-two exponential with a natural
  -- exponent.
  have htwo : Real.exp (Real.log 2 * (n : ℝ)) = (2 : ℝ) ^ n := by
    simp [Real.exp_mul, Real.exp_nat_mul]
  simpa [ε, htwo, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    using this

/-- A concrete upper bound on the cover exponent that is valid for all
`n` beyond a certain threshold.  The eventual inequality is extracted from
`eventually_monomial_le_half_pow` and translated back to the natural numbers. -/
lemma powFamilyExponentBound_eventually_le_two_pow_pred (c : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      powFamilyExponentBound n c ≤ 2 ^ (n - 1) ∧ 2 ≤ n := by
  classical
  -- Combine the analytic inequality with the arithmetic comparison obtained in
  -- `powFamilyExponentBound_le_monomial`.
  have hpoly := eventually_monomial_le_half_pow c
  have htwo := eventually_ge_atTop (2 : ℕ)
  refine (hpoly.and htwo).mono ?_
  intro n hn
  rcases hn with ⟨hbound, hn⟩
  -- Translate the intermediate inequality to the cover exponent.
  have hmono :=
      powFamilyExponentBound_le_monomial (n := n) (c := c)
        (hn := (Nat.le_trans (by decide : 1 ≤ 2) hn))
  have hcast :
      (powFamilyExponentBound n c : ℝ) ≤
          (555 : ℝ) * (n : ℝ) ^ (2 * c + 1) := by
    exact_mod_cast hmono
  have :
      (powFamilyExponentBound n c : ℝ) ≤ (2 : ℝ) ^ n / 2 :=
    hcast.trans hbound
  -- Rewrite the right-hand side as `2^(n-1)` to eliminate the real numbers.
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have htwo : ((2 : ℝ) ^ n) / 2 = (Nat.pow 2 (n - 1) : ℝ) := by
    have hpred := Nat.succ_pred_eq_of_pos hnpos
    have hpow := pow_succ (2 : ℝ) (n - 1)
    have hrepr : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1) * 2 := by
      simpa [hpred] using hpow
    simpa [hrepr, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc,
      pow_one] using congrArg (fun x : ℝ => x / 2) hrepr
  have htarget :
      (powFamilyExponentBound n c : ℝ) ≤ (Nat.pow 2 (n - 1) : ℝ) := by
    simpa [htwo] using this
  exact ⟨(by exact_mod_cast htarget), hn⟩

/-- The threshold from which the double-exponential bound for the covering
exponent holds.  The definition uses choice on the event obtained in
`powFamilyExponentBound_eventually_le_two_pow_pred`. -/
def coverThreshold (c : ℕ) : ℕ :=
  Classical.choose <|
    (Filter.eventually_atTop.1
      (powFamilyExponentBound_eventually_le_two_pow_pred (c := c)))

/-- Beyond `coverThreshold` the exponent controlling the size of the cover is at
most `2^(n-1)`; we record this fact explicitly for later arithmetic arguments. -/
lemma coverThreshold_spec (c : ℕ) :
    ∀ ⦃n : ℕ⦄, coverThreshold c ≤ n →
      powFamilyExponentBound n c ≤ 2 ^ (n - 1) ∧ 2 ≤ n := by
  classical
  have h := (Filter.eventually_atTop.1
      (powFamilyExponentBound_eventually_le_two_pow_pred (c := c)))
  simpa [coverThreshold] using (Classical.choose_spec h)

/-- Elementary inequality showing that removing a half-sized exponential from
`2^n` still leaves at least `2^(n-1)` when `n ≥ 2`. -/
lemma two_pow_pred_le_two_pow_sub_half {n : ℕ} (hn : 2 ≤ n) :
    2 ^ (n - 1) ≤ 2 ^ n - 2 ^ (n / 2) := by
  have hpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hdiv : n / 2 ≤ n - 1 := by
    have hlt : n / 2 < n := Nat.div_lt_self hpos (by decide : 1 < 2)
    have : n = (n - 1).succ := Nat.succ_pred_eq_of_pos hpos
    simpa [this, Nat.lt_succ_iff] using hlt
  have hpow : 2 ^ (n / 2) ≤ 2 ^ (n - 1) :=
    Nat.pow_le_pow_of_le_left (by decide : 1 ≤ 2) hdiv
  -- Move to the reals where subtraction behaves additively and then convert back.
  have hpow_real : (2 : ℝ) ^ (n / 2) ≤ (2 : ℝ) ^ (n - 1) := by
    exact_mod_cast hpow
  have hsum := add_le_add_left hpow_real ((2 : ℝ) ^ (n - 1))
  have hsucc : (n - 1).succ = n := Nat.succ_pred_eq_of_pos hpos
  have hpow_succ : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1) * 2 := by
    simpa [hsucc, mul_comm] using pow_succ (2 : ℝ) (n - 1)
  have hsum' : (2 : ℝ) ^ (n - 1) + (2 : ℝ) ^ (n / 2) ≤ (2 : ℝ) ^ n := by
    simpa [two_mul, add_comm, add_left_comm, add_assoc, hpow_succ,
      mul_comm, mul_left_comm] using hsum
  have hreal : (2 : ℝ) ^ (n - 1) ≤ (2 : ℝ) ^ n - (2 : ℝ) ^ (n / 2) :=
    (le_sub_iff_add_le).2 hsum'
  exact_mod_cast hreal

/-- Final comparison with the double-exponential expression appearing in the
statement of Lemma B-5. -/
lemma powFamilyExponentBound_le_doubleExp {n c : ℕ}
    (hn : coverThreshold c ≤ n) :
    powFamilyExponentBound n c ≤ 2 ^ n - 2 ^ (n / 2) := by
  obtain ⟨hbound, htwo⟩ := coverThreshold_spec (c := c) hn
  have hineq := two_pow_pred_le_two_pow_sub_half (n := n) htwo
  exact hbound.trans hineq


end Circuit
end Boolcube
