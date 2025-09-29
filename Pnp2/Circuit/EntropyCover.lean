import Pnp2.canonical_circuit
import Pnp2.bound
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Sqrt

/-!
# Circuit families and entropy-driven covers

This module specialises the general **Family Collision–Entropy Lemma** to the
families of Boolean functions computed by small circuits.  The combinatorial
workhorse is already carried out in `Pnp2.canonical_circuit`: we know that the
number of size-`≤ n^c` circuits (and hence their collision entropy) grows only
polynomially with `n`.  Here we package those estimates into concrete covering
statements that will feed directly into the formal proof of Lemma B-5.

The key results are:

* `powFamily_cover` — instantiates `Bound.family_collision_entropy_lemma` with
the circuit family, yielding a collection of monochromatic subcubes that cover
**every** function in the family simultaneously.
* `powFamily_cover_for_member` — refines the previous statement to an arbitrary
member `f` of the family, filtering out rectangles that are monochromatic of
colour `0` for `f`.  The resulting set consists only of `1`-rectangles and still
respects the original cardinality bound.

Both lemmas are intentionally verbose, with extensive comments explaining how
the existing infrastructure fits together.  This should make it easy to trace
the dependencies when assembling the final statement of Lemma B-5.
-/

open Classical
open Boolcube

namespace Boolcube
namespace Circuit

/--
This section establishes a simple but crucial numeric inequality used to
compare the coarse `2^{3n + 66 n^{c+1} + 2}` rectangle bound delivered by the
entropy-cover lemma with the *doubly exponential* target `2^{2^n - 2^{n/2}}`
appearing in Lemma B-5.  The strategy is deliberately elementary: we only use
basic monotonicity of the natural square root together with the discrete
inequality `(m + 1)^2 ≤ 2^m` once `m ≥ 6`.  This avoids any heavy analysis
while still providing an explicit (albeit extremely generous) threshold from
which the double-exponential bound dominates.
-/

namespace Numeric

open scoped Real

/--
For integers `m ≥ 6`, the exponential function `2^m` dominates the quadratic
`(m + 1)^2`.  The proof proceeds by induction on `m`, observing that the ratio
between successive squares is at most `2` beyond this threshold whereas the
power of two doubles at every step.
-/
lemma succ_sq_le_two_pow {m : ℕ} (hm : 6 ≤ m) : (m + 1) ^ 2 ≤ Nat.pow 2 m := by
  -- Initial seed of the induction.
  have hbase : (6 + 1) ^ 2 ≤ Nat.pow 2 6 := by decide
  refine Nat.le_induction hbase ?_ hm
  intro k hk ih
  -- Auxiliary bound: `2 * (k + 1) + 1 ≤ (k + 1)^2` once `k ≥ 2`.
  have hk₂ : 2 ≤ k := le_trans (by decide) hk
  have hk₂sq : 2 ≤ k ^ 2 := by
    have hpow : 4 ≤ k ^ 2 := by
      simpa [Nat.pow_two] using Nat.mul_self_le_mul_self hk₂
    exact le_trans (by decide) hpow
  have haux : 2 * (k + 1) + 1 ≤ (k + 1) ^ 2 := by
    have := add_le_add_left hk₂sq (2 * k + 1)
    simpa [two_mul, Nat.pow_two, Nat.mul_add, Nat.add_mul, add_comm, add_left_comm,
      add_assoc, Nat.succ_eq_add_one] using this
  have haux_pow : 2 * (k + 1) + 1 ≤ Nat.pow 2 k := le_trans haux ih
  have hsum : (k + 2) ^ 2 = (k + 1) ^ 2 + (2 * (k + 1) + 1) := by ring
  calc
    (k + 2) ^ 2 = (k + 1) ^ 2 + (2 * (k + 1) + 1) := hsum
    _ ≤ Nat.pow 2 k + Nat.pow 2 k := add_le_add ih haux_pow
    _ = Nat.pow 2 (k + 1) := by
      simp [Nat.pow_succ, two_mul, add_comm, add_left_comm, add_assoc, mul_comm,
        mul_left_comm, mul_assoc]

/--
If `n ≥ 36`, the binary logarithm of `n` is bounded by the integer square root
of `n`.  This follows from the previous lemma applied to `Nat.sqrt n`.
-/
lemma log2_le_natSqrt {n : ℕ} (hn : 36 ≤ n) :
    Real.log2 (n : ℝ) ≤ Nat.sqrt n := by
  have hnpos : 0 < n := lt_of_le_of_lt hn (by decide)
  -- From `36 ≤ n` we infer `6 ≤ sqrt n` via the characterisation of `Nat.sqrt`.
  have hsqrt_ge : 6 ≤ Nat.sqrt n := by
    have : (6 : ℕ) ^ 2 ≤ n := by simpa [Nat.pow_two] using hn
    exact (Nat.le_sqrt'.mpr this)
  -- Apply the discrete bound `(m + 1)^2 ≤ 2^m` with `m = sqrt n`.
  have hpow : (Nat.sqrt n + 1) ^ 2 ≤ Nat.pow 2 (Nat.sqrt n) :=
    succ_sq_le_two_pow hsqrt_ge
  -- By definition of `Nat.sqrt`, `n` is strictly smaller than `(sqrt n + 1)^2`.
  have hlt : (n : ℕ) < (Nat.sqrt n + 1) ^ 2 := Nat.lt_succ_sqrt' n
  -- Therefore `n < 2^(sqrt n)`, and `log₂` preserves this inequality.
  have hlt' : (n : ℝ) < (2 : ℝ) ^ Nat.sqrt n := by
    exact_mod_cast lt_of_lt_of_le hlt hpow
  have hpow_pos : 0 < (2 : ℝ) ^ Nat.sqrt n := by positivity
  have hlog := Real.log2_le_log2 (by exact_mod_cast hnpos) hpow_pos (le_of_lt hlt')
  -- Simplify the right-hand side using `log₂(2^k) = k`.
  simpa using hlog

/--
If `n ≥ 4 (c + 1)^2` then `2 (c + 1)` is at most the integer square root of `n`,
and consequently `2 (c + 1) · √n ≤ n`.
-/
lemma two_mul_natSqrt_mul_le {n c : ℕ} (h : 4 * (c + 1) ^ 2 ≤ n) :
    2 * ((c + 1) * Nat.sqrt n) ≤ n := by
  set m := 2 * (c + 1)
  have hm_sq : m ^ 2 ≤ n := by
    simpa [m, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.pow_two] using h
  have hm_le_sqrt : m ≤ Nat.sqrt n := (Nat.le_sqrt'.mpr hm_sq)
  have hmul : m * Nat.sqrt n ≤ Nat.sqrt n * Nat.sqrt n :=
    Nat.mul_le_mul_right _ hm_le_sqrt
  have hsquare : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
  have := hmul.trans hsquare
  simpa [m, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.succ_eq_add_one,
    two_mul] using this

/--
Control the logarithmic term `(c + 1) · log₂ n` via the inequality from
`two_mul_natSqrt_mul_le`.
-/
lemma log2_mul_le_half {n c : ℕ} (h₁ : 4 * (c + 1) ^ 2 ≤ n) (h₂ : 36 ≤ n) :
    (c + 1 : ℝ) * Real.log2 (n : ℝ) ≤ (n : ℝ) / 2 := by
  have hlog := log2_le_natSqrt h₂
  have hmul_nat : 2 * ((c + 1) * Nat.sqrt n) ≤ n :=
    two_mul_natSqrt_mul_le (n := n) (c := c) h₁
  -- Multiply the basic logarithmic bound by the positive factor `(c + 1)`.
  have hlog' : (c + 1 : ℝ) * Real.log2 (n : ℝ)
      ≤ (c + 1 : ℝ) * (Nat.sqrt n : ℝ) := by
    have hnonneg : 0 ≤ (c + 1 : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left hlog hnonneg
  -- Translate the natural inequality into reals and divide by two.
  have hmul_real : 2 * ((c + 1 : ℝ) * (Nat.sqrt n : ℝ)) ≤ (n : ℝ) := by
    exact_mod_cast hmul_nat
  have hhalf : (c + 1 : ℝ) * (Nat.sqrt n : ℝ) ≤ (n : ℝ) / 2 := by
    have hpos : 0 < (2 : ℝ) := by norm_num
    exact (le_div_iff hpos).mpr (by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul_real)
  exact hlog'.trans hhalf

/--
Elementary coarse bound: `log₂ 70 ≤ 7` because `70 < 2^7`.
-/
lemma log2_seventy_le_seven : Real.log2 (70 : ℝ) ≤ (7 : ℝ) := by
  have hpos : 0 < (70 : ℝ) := by norm_num
  have hpow_pos : 0 < (2 : ℝ) ^ 7 := by positivity
  have hle : (70 : ℕ) ≤ 2 ^ 7 := by decide
  have hlog := Real.log2_le_log2 hpos hpow_pos (by exact_mod_cast hle)
  simpa [Nat.cast_pow, Real.log2_pow, Nat.succ_eq_add_one] using hlog

/--
If the base-two logarithm of `a` is at most `k`, then `a` itself is bounded by
`2^k`.  This is a convenient rephrasing of the monotonicity of the logarithm
and will be used to convert the logarithmic estimate into an inequality on the
cardinality bound.
-/
lemma log2_le_pow {a : ℝ} {k : ℕ} (ha : 0 < a) (h : Real.log2 a ≤ k) :
    a ≤ (2 : ℝ) ^ k := by
  have hlog2 : Real.log a / Real.log 2 ≤ k := by
    simpa [Real.log2, div_eq_mul_inv] using h
  have hpos_log2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hlog : Real.log a ≤ (k : ℝ) * Real.log 2 :=
    (div_le_iff hpos_log2).1 hlog2
  have hbound := (Real.log_le_iff_le_exp ha).1 hlog
  -- Rewrite the exponential expression as `2^k`.
  have hexp : Real.exp ((k : ℝ) * Real.log 2) = (2 : ℝ) ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
        have : (Real.exp ((k : ℝ) * Real.log 2)) * Real.exp (Real.log 2)
            = Real.exp (((k : ℝ) + 1) * Real.log 2) := by
              have := Real.exp_add ((k : ℝ) * Real.log 2) (Real.log 2)
              simpa [mul_add, add_comm, add_left_comm, add_assoc, Nat.cast_succ,
                mul_comm, mul_left_comm, mul_assoc] using this.symm
        simp [Nat.succ_eq_add_one, pow_succ, ih, this, Real.exp_log (by norm_num : (0 : ℝ) < 2),
          mul_comm, mul_left_comm, mul_assoc]
  simpa [hexp] using hbound

/-!
### Double-exponential domination of the rectangle bound

The remaining lemmas in this section upgrade the coarse `2^{3n + 66 n^{c+1} + 2}`
estimate coming out of `powFamily_cover_for_member` into the asymptotic form
`2^{2^n - 2^{n/2}}` required by Lemma B-5.  The strategy is to absorb the
linear and constant terms into the main polynomial factor `n^{c+1}`, control its
logarithm via the auxiliary results above, and finally compare the exponents of
the two powers of two.  Everything is made explicit by fixing a concrete (albeit
very generous) threshold on `n`.
-/

/-!
`coverThreshold c` is a convenient concrete value of `n` beyond which all
numeric side-conditions used below hold automatically.  The lower bound `70`
absorbs the constant terms when estimating logarithms, while the quadratic
expression enforces the hypotheses of `log2_mul_le_half`.
-/
def coverThreshold (c : ℕ) : ℕ := max 70 (4 * (c + 1) ^ 2)

lemma seventy_le_coverThreshold (c : ℕ) : 70 ≤ coverThreshold c :=
  le_max_left _ _

lemma quadratic_le_coverThreshold (c : ℕ) : 4 * (c + 1) ^ 2 ≤ coverThreshold c :=
  le_max_right _ _

/--
Absorb the lower-order terms of the exponent into the dominant polynomial
`n^{c+1}`.  Once `n ≥ 2`, the inequalities `n ≤ n^{c+1}` and `2 ≤ n^{c+1}` allow
us to control the contributions of `3 · n` and the trailing constant respectively.
-/
lemma exponent_le_seventy_mul {n c : ℕ} (hn : 2 ≤ n) :
    3 * n + 11 * powFamilyEntropyBound n c + 2 ≤ 70 * n ^ (c + 1) := by
  have hn₁ : 1 ≤ n := le_trans (by decide : (1 : ℕ) ≤ 2) hn
  -- Relate `n` to the dominating power `n^{c+1}`.
  have hpow_pos : 0 < n := lt_of_le_of_lt hn₁ (by decide : (1 : ℕ) < 2)
  have hpow_ge_one : 1 ≤ n ^ c := by
    have hpos : 0 < n ^ c := Nat.pow_pos hpow_pos _
    exact Nat.succ_le_of_lt hpos
  have hn_le_pow : n ≤ n ^ (c + 1) := by
    simpa [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using Nat.mul_le_mul_left n hpow_ge_one
  have htwo_le_pow : 2 ≤ n ^ (c + 1) := le_trans hn hn_le_pow
  -- First absorb the linear term into the polynomial.
  have hstep₁ :
      3 * n + 66 * n ^ (c + 1) + 2 ≤ 3 * n ^ (c + 1) + 66 * n ^ (c + 1) + 2 := by
    have := add_le_add (Nat.mul_le_mul_left _ hn_le_pow) (le_of_eq rfl)
    exact Nat.add_le_add_right this 2
  -- Next absorb the trailing constant `2`.
  have hstep₂ :
      3 * n ^ (c + 1) + 66 * n ^ (c + 1) + 2
        ≤ 3 * n ^ (c + 1) + 66 * n ^ (c + 1) + n ^ (c + 1) :=
    Nat.add_le_add_left htwo_le_pow _
  -- Simplify both sides into multiples of `n^{c+1}`.
  have hrewrite₁ :
      3 * n + 11 * powFamilyEntropyBound n c + 2
        = 3 * n + 66 * n ^ (c + 1) + 2 := by
    simp [powFamilyEntropyBound, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have hrewrite₂ :
      70 * n ^ (c + 1)
        = 3 * n ^ (c + 1) + 66 * n ^ (c + 1) + n ^ (c + 1) := by
    ring
  refine (hrewrite₁ ▸ hstep₁.trans ?_)
  simpa [hrewrite₂, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, add_comm,
    add_left_comm, add_assoc]
    using hstep₂

/--
Upper-bound `log₂ (70 · n^{c+1})` by the linear function `n - 1` once `n` is
large.  The term `(c + 1) · log₂ n` is controlled by `log2_mul_le_half`, while
the constant contribution `log₂ 70` becomes negligible beyond `n ≥ 16`.
-/
lemma log2_seventy_mul_le {n c : ℕ}
    (h₁ : 4 * (c + 1) ^ 2 ≤ n) (h₂ : 36 ≤ n) :
    Real.log2 ((70 : ℝ) * (n : ℝ) ^ (c + 1)) ≤ (n : ℝ) - 1 := by
  have hpos70 : 0 < (70 : ℝ) := by norm_num
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast lt_of_le_of_lt h₂ (by decide : (36 : ℕ) < 37)
  have hpow_pos : 0 < (n : ℝ) ^ (c + 1) := by positivity
  -- Expand `log₂` of the product.
  have hlog_prod :
      Real.log2 ((70 : ℝ) * (n : ℝ) ^ (c + 1))
        = Real.log2 (70 : ℝ) + (c + 1 : ℝ) * Real.log2 (n : ℝ) := by
    have hlog_mul := Real.log_mul hpos70 hpow_pos
    have hlog_pow := Real.log_pow hn_pos (c + 1)
    have hlog70 : Real.log (70 : ℝ) = Real.log (70 : ℝ) := rfl
    have hpow_cast : ((n : ℝ) ^ (c + 1) : ℝ) = (n : ℝ) ^ (c + 1) := by rfl
    have hpow₂ :
        Real.log2 ((n : ℝ) ^ (c + 1)) = (c + 1 : ℝ) * Real.log2 (n : ℝ) := by
      simpa using Real.log2_pow hn_pos.ne' (c + 1)
    -- Convert everything back to base-`2` logarithms.
    have :
        Real.log2 ((70 : ℝ) * (n : ℝ) ^ (c + 1))
          = (Real.log (70 : ℝ) + Real.log ((n : ℝ) ^ (c + 1))) / Real.log 2 := by
      simp [Real.log2, hlog_mul, hpow_cast]
    have :
        (Real.log (70 : ℝ) + Real.log ((n : ℝ) ^ (c + 1))) / Real.log 2
          = Real.log2 (70 : ℝ) + (c + 1 : ℝ) * Real.log2 (n : ℝ) := by
      simp [Real.log2, hlog_pow, add_comm, add_left_comm, add_assoc, mul_comm,
        mul_left_comm, mul_assoc, div_eq_mul_inv]
    simpa [this]
  -- Bound the two components separately.
  have hsum :
      Real.log2 (70 : ℝ) + (c + 1 : ℝ) * Real.log2 (n : ℝ)
        ≤ 7 + (n : ℝ) / 2 := by
    have hconst := log2_seventy_le_seven
    have hlin := log2_mul_le_half (n := n) (c := c) h₁ h₂
    exact add_le_add hconst hlin
  -- Show that the right-hand side is at most `n - 1` for `n ≥ 36`.
  have h16 : (16 : ℕ) ≤ n := le_trans (by decide : (16 : ℕ) ≤ 36) h₂
  have h16_real : (16 : ℝ) ≤ n := by exact_mod_cast h16
  have htarget : 7 + (n : ℝ) / 2 ≤ (n : ℝ) - 1 := by
    have hhalf : (8 : ℝ) ≤ (n : ℝ) / 2 := by
      have hpos2 : (0 : ℝ) < (2 : ℝ) := by norm_num
      have := (div_le_div_right hpos2).mpr h16_real
      simpa using this
    have hnonneg : 0 ≤ (n : ℝ) / 2 - 8 := sub_nonneg.mpr hhalf
    have hrewrite : (n : ℝ) - 1 - (7 + (n : ℝ) / 2) = (n : ℝ) / 2 - 8 := by ring
    exact sub_nonneg.mp (by simpa [hrewrite, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc] using hnonneg)
  simpa [hlog_prod] using hsum.trans htarget

/--
From the previous lemmas we deduce that the exponent `3n + 66 n^{c+1} + 2`
stays below `2^{n-1}` once `n` dominates the threshold.  This is the key step
for comparing the sizes of the two powers of two.
-/
lemma exponent_le_two_pow_pred {n c : ℕ}
    (h₁ : 4 * (c + 1) ^ 2 ≤ n) (h₂ : 36 ≤ n) :
    3 * n + 11 * powFamilyEntropyBound n c + 2 ≤ Nat.pow 2 (n - 1) := by
  have hn₂ : 2 ≤ n := le_trans (by decide : (2 : ℕ) ≤ 36) h₂
  -- First compare the exponents on the natural level.
  have hpoly := exponent_le_seventy_mul (n := n) (c := c) hn₂
  -- Translate into reals to invoke the logarithmic control.
  have hreal :
      (3 * n + 11 * powFamilyEntropyBound n c + 2 : ℝ)
        ≤ (70 : ℝ) * (n : ℝ) ^ (c + 1) := by exact_mod_cast hpoly
  have hpos_left : 0 < (3 * n + 11 * powFamilyEntropyBound n c + 2 : ℝ) := by
    have : (0 : ℕ) < 3 * n + 11 * powFamilyEntropyBound n c + 2 := by decide
    exact_mod_cast this
  have hpos_right : 0 < (70 : ℝ) * (n : ℝ) ^ (c + 1) := by positivity
  have hlog := Real.log2_le_log2 hpos_left hpos_right hreal
  have hlin := log2_seventy_mul_le (n := n) (c := c) h₁ h₂
  have hfinal := hlog.trans hlin
  -- Convert back from reals to naturals.
  have hpow := log2_le_pow (a :=
      (3 * n + 11 * powFamilyEntropyBound n c + 2 : ℝ))
      (k := n - 1) hpos_left hfinal
  have :
      (3 * n + 11 * powFamilyEntropyBound n c + 2 : ℝ)
        ≤ (Nat.pow 2 (n - 1) : ℝ) := by simpa using hpow
  exact_mod_cast this

/--
For `n ≥ 2`, the quotient `n / 2` never reaches `n - 1`.
-/
lemma div_two_le_pred {n : ℕ} (hn : 2 ≤ n) : n / 2 ≤ n - 1 := by
  have hcases := Nat.mod_two_eq_zero_or_one n
  cases hcases with
  | inl hmod =>
      have hpos : 0 < n / 2 := Nat.div_pos (by decide : 0 < 2) hn
      have hge : 1 ≤ n / 2 := Nat.succ_le_of_lt hpos
      have hdecomp := Nat.mod_mul_left_div_self (n := n) (b := 2)
      have htwo : 2 * (n / 2) = n := by
        simpa [hmod, add_comm, add_left_comm, add_assoc] using hdecomp
      have hsucc : (n / 2) + (n / 2 - 1) + 1 = 2 * (n / 2) := by
        have hcancel : n / 2 - 1 + 1 = n / 2 := Nat.sub_add_cancel hge
        simpa [two_mul, add_comm, add_left_comm, add_assoc, hcancel]
          using congrArg (fun t => (n / 2) + t) (by simpa using hcancel)
      have hrewrite : (n / 2) + (n / 2 - 1) = 2 * (n / 2) - 1 := by
        have : Nat.succ ((n / 2) + (n / 2 - 1)) = 2 * (n / 2) := by
          simpa [add_comm, add_left_comm, add_assoc] using hsucc
        simpa using congrArg Nat.pred this
      have hk_le : n / 2 ≤ (n / 2) + (n / 2 - 1) := Nat.le_add_right _ _
      have : n / 2 ≤ 2 * (n / 2) - 1 := by simpa [hrewrite] using hk_le
      simpa [htwo] using this
  | inr hmod =>
      have hdecomp := Nat.mod_mul_left_div_self (n := n) (b := 2)
      have htwo : 2 * (n / 2) + 1 = n := by
        simpa [hmod, add_comm, add_left_comm, add_assoc] using hdecomp
      have : n / 2 ≤ 2 * (n / 2) := by
        simpa [two_mul, add_comm, add_left_comm, add_assoc]
          using Nat.le_add_left (n / 2) (n / 2)
      have htwo' : n - 1 = 2 * (n / 2) := by
        have := congrArg Nat.pred htwo
        simpa using this
      simpa [htwo'] using this

/--
For `n ≥ 2`, the difference `2^n - 2^{⌊n/2⌋}` dominates the simpler quantity
`2^{n-1}`.
-/
lemma two_pow_pred_le_difference {n : ℕ} (hn : 2 ≤ n) :
    Nat.pow 2 (n - 1) ≤ Nat.pow 2 n - Nat.pow 2 (n / 2) := by
  have hdiv := div_two_le_pred hn
  have hmono := Nat.pow_le_pow_of_le_right (by decide : 0 < (2 : ℕ)) hdiv
  have hpos : 0 < n := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hn
  have hrewrite : Nat.pow 2 n = 2 * Nat.pow 2 (n - 1) := by
    have := Nat.pow_succ 2 (n - 1)
    simpa [Nat.succ_eq_add_one, Nat.succ_pred_eq_of_pos hpos] using this
  have hsum : Nat.pow 2 (n - 1) + Nat.pow 2 (n / 2) ≤ Nat.pow 2 n := by
    have := add_le_add_left hmono (Nat.pow 2 (n - 1))
    simpa [hrewrite, two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using this
  have hdiff : Nat.pow 2 (n - 1) ≤ Nat.pow 2 n - Nat.pow 2 (n / 2) := by
    exact Nat.le_sub_of_add_le (Nat.pow 2 (n / 2)) hsum
  simpa using hdiff

/--
Main numeric comparison: beyond the threshold `coverThreshold c`, the exponent
provided by `powFamily_cover_for_member` is at most `2^n - 2^{⌊n/2⌋}`.
-/
lemma exponent_le_doubleExp {n c : ℕ} (hn : coverThreshold c ≤ n) :
    3 * n + 11 * powFamilyEntropyBound n c + 2
      ≤ Nat.pow 2 n - Nat.pow 2 (n / 2) := by
  have hquad : 4 * (c + 1) ^ 2 ≤ n :=
    (quadratic_le_coverThreshold c).trans hn
  have hlin : 36 ≤ n :=
    (le_trans (by decide : (36 : ℕ) ≤ 70) (seventy_le_coverThreshold c)).trans hn
  have hpred := exponent_le_two_pow_pred (n := n) (c := c) hquad hlin
  have hn₂ : 2 ≤ n := le_trans (by decide : (2 : ℕ) ≤ 36) hlin
  exact hpred.trans (two_pow_pred_le_difference hn₂)

end Numeric

/--
A convenient shorthand for the family of Boolean functions realised by circuits
of size at most `n^c`.  The underlying definition already lives in
`canonical_circuit.lean`; we merely re-expose it with a descriptive name for the
cover-related lemmas below.
-/
def powFamily (n c : ℕ) : Family n :=
  family n (n ^ c)

/--
Abbreviation for the (very coarse) entropy bound `6 · n^{c+1}` proved in
`pow_family_H₂_le`.  Exposing it as a dedicated definition keeps the statements
below pleasant to read and ensures that the numeric constant is centralised in a
single place.
-/
def powFamilyEntropyBound (n c : ℕ) : ℕ :=
  6 * n ^ (c + 1)

@[simp] lemma powFamilyEntropyBound_val (n c : ℕ) :
    powFamilyEntropyBound n c = 6 * n ^ (c + 1) := rfl

/--
The canonical circuit counting argument shows that the collision entropy of the
family `powFamily n c` is bounded by `6 · n^{c+1}` (interpreted as a real
number).  This repackages `pow_family_H₂_le` using the helper definitions above.
-/
lemma powFamily_H₂_le (n c : ℕ) (hn : 1 ≤ n) :
    Entropy.H₂ (powFamily n c) ≤ (powFamilyEntropyBound n c : ℝ) := by
  simpa [powFamily, powFamilyEntropyBound] using
    pow_family_H₂_le (n := n) (c := c) hn

/--
Instantiate `Bound.family_collision_entropy_lemma` with the family of
size-`≤ n^c` circuits.  The output is a finite collection of subcubes that are
simultaneously monochromatic for every function in the family and cover all
inputs on which any member evaluates to `1`.  The explicit bound on the number
of rectangles is inherited verbatim from `Bound`.
-/
lemma powFamily_cover (n c : ℕ) (hn : 0 < n) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, ∀ g ∈ powFamily n c, Subcube.monochromaticFor R g) ∧
      (∀ f ∈ powFamily n c, ∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Nat.pow 2 (3 * n + 11 * powFamilyEntropyBound n c + 2) := by
  classical
  -- Translate `0 < n` into the `1 ≤ n` assumption required by the entropy bound.
  have hn' : 1 ≤ n := Nat.succ_le_of_lt hn
  -- The collision-entropy bound from `canonical_circuit.lean`.
  have hH := powFamily_H₂_le (n := n) (c := c) hn'
  -- Direct application of the general covering lemma.
  simpa [powFamily, powFamilyEntropyBound] using
    Bound.family_collision_entropy_lemma
      (F := powFamily n c) (h := powFamilyEntropyBound n c)
      (hH := hH) (hn_pos := hn)

/--
A refined version of `powFamily_cover` tailored to a *single* function `f`
inside the circuit family.  By filtering the rectangles produced by
`powFamily_cover` we retain only those on which `f` takes the value `1`.  This
keeps the cover monochromatic with colour `1` and preserves the global bound on
the number of rectangles.
-/
lemma powFamily_cover_for_member {n c : ℕ} (hn : 0 < n)
    {f : BoolFunc.BFunc n} (hf : f ∈ powFamily n c) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, ∀ x, x ∈ₛ R → f x = true) ∧
      (∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Nat.pow 2 (3 * n + 11 * powFamilyEntropyBound n c + 2) := by
  classical
  -- Start with the global cover for the entire family of circuits.
  obtain ⟨Rset₀, hmono₀, hcover₀, hcard₀⟩ := powFamily_cover (n := n) (c := c) hn
  -- Filter out rectangles that are monochromatic of colour `0` for `f`.
  let Rset := Rset₀.filter fun R => ∃ x, x ∈ₛ R ∧ f x = true
  refine ⟨Rset, ?_, ?_, ?_⟩
  · -- Every rectangle retained by the filter is fully `1`-monochromatic for `f`.
    intro R hR x hx
    obtain ⟨hR₀, hx₁⟩ := Finset.mem_filter.mp hR
    rcases hx₁ with ⟨x₀, hx₀R, hx₀val⟩
    rcases hmono₀ R hR₀ f hf with ⟨b, hb⟩
    -- The witness `x₀` shows that the monochromatic colour must be `1`.
    have hxcolour : f x₀ = b := hb hx₀R
    have hbtrue : b = true := by
      have : true = b := by simpa [hx₀val] using hxcolour
      simpa using this.symm
    -- Propagate the colour to the arbitrary point `x` of the rectangle.
    have hfx : f x = b := hb hx
    simpa [hbtrue] using hfx
  · -- Coverage: every `1`-input of `f` lies in some filtered rectangle.
    intro x hx
    obtain ⟨R, hR, hxR⟩ := hcover₀ f hf x hx
    -- Use the witness `x` itself to justify that `R` survives the filter.
    have hmem : R ∈ Rset := by
      refine Finset.mem_filter.mpr ?_
      exact ⟨hR, ⟨x, hxR, hx⟩⟩
    exact ⟨R, hmem, hxR⟩
  · -- Cardinality: filtering can only reduce the size of the rectangle set.
    have hfilter : Rset.card ≤ Rset₀.card :=
      Finset.card_filter_le (fun R => ∃ x, x ∈ₛ R ∧ f x = true) Rset₀
    exact hfilter.trans hcard₀

/--
Specialised version of `powFamily_cover_for_member` where the rectangle
cardinality is already compared with the target double-exponential bound.  The
assumption `Numeric.coverThreshold c ≤ n` ensures that the numeric inequalities
developed earlier apply directly.
-/
lemma powFamily_cover_for_member_doubleExp {n c : ℕ}
    (hn : 0 < n) (hlarge : Numeric.coverThreshold c ≤ n)
    {f : BoolFunc.BFunc n} (hf : f ∈ powFamily n c) :
    ∃ Rset : Finset (Subcube n),
      (∀ R ∈ Rset, ∀ x, x ∈ₛ R → f x = true) ∧
      (∀ x, f x = true → ∃ R ∈ Rset, x ∈ₛ R) ∧
      Rset.card ≤ Nat.pow 2 (Nat.pow 2 n - Nat.pow 2 (n / 2)) := by
  classical
  obtain ⟨Rset, hmono, hcover, hcard⟩ :=
    powFamily_cover_for_member (n := n) (c := c) hn hf
  have hexp := Numeric.exponent_le_doubleExp (n := n) (c := c) hlarge
  have hpow := Nat.pow_le_pow_of_le_right (by decide : 0 < (2 : ℕ)) hexp
  exact ⟨Rset, hmono, hcover, hcard.trans hpow⟩

end Circuit
end Boolcube
