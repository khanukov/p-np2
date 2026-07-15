import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanRestrictionMoment
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDFourierFactorization
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Exact rational energy identities on a finite Boolean cube

This module supplies the Parseval/Bessel layer used after the exact finite
restriction-moment calculation.  All averages and coefficients are rational
finite sums.  In particular, the energy bounds below do not hide a real-valued
measure space or an asymptotic limiting argument.
-/

namespace FiniteBooleanFourierEnergy

open scoped BigOperators
open FiniteBooleanFourier FiniteBooleanRestrictionMoment

/-! ## Coefficients and orthogonality -/

/-- The coefficient definition is exactly a uniform finite average. -/
theorem coefficient_eq_finiteAverage_mul {n : Nat}
    (f : (Fin n → Bool) → ℚ) (alpha : Finset (Fin n)) :
    coefficient f alpha =
      finiteAverage (fun input : Fin n → Bool ↦
        f input * character alpha input) := by
  simp [FiniteBooleanFourier.coefficient,
    FiniteBooleanRestrictionMoment.finiteAverage]

/-- A character depends only on the coordinates in its support. -/
theorem character_dependsOnlyOn {n : Nat} (alpha : Finset (Fin n)) :
    FiniteBooleanFourier.DependsOnlyOn alpha (character alpha) := by
  intro input input' hagree
  apply Finset.prod_congr rfl
  intro queryIndex hqueryIndex
  rw [hagree queryIndex hqueryIndex]

/-- Exact orthogonality of distinct Walsh characters under the uniform cube
average. -/
theorem finiteAverage_character_mul_character {n : Nat}
    (alpha beta : Finset (Fin n)) :
    finiteAverage (fun input : Fin n → Bool ↦
      character alpha input * character beta input) =
      if alpha = beta then 1 else 0 := by
  rw [← coefficient_eq_finiteAverage_mul]
  by_cases heq : alpha = beta
  · subst beta
    simp [FiniteBooleanFourier.coefficient_character_self]
  · rw [if_neg heq]
    by_cases hsubset : beta ⊆ alpha
    · have hnsubset : ¬ alpha ⊆ beta := by
        intro hreverse
        exact heq (Finset.Subset.antisymm hreverse hsubset)
      have hzero : coefficient (character beta) alpha = 0 :=
        FiniteBooleanFourier.coefficient_eq_zero_of_not_subset_of_dependsOnlyOn
          (character_dependsOnlyOn beta) hnsubset
      rw [FiniteBooleanFourier.coefficient]
      rw [FiniteBooleanFourier.coefficient] at hzero
      convert hzero using 1
      apply congrArg (fun value : ℚ ↦ value / (2 : ℚ) ^ n)
      apply Finset.sum_congr rfl
      intro input _
      ring
    · exact
        FiniteBooleanFourier.coefficient_eq_zero_of_not_subset_of_dependsOnlyOn
          (character_dependsOnlyOn alpha) hsubset

/-- Unnormalized form of character orthogonality. -/
theorem sum_character_mul_character {n : Nat}
    (alpha beta : Finset (Fin n)) :
    (∑ input : Fin n → Bool,
      character alpha input * character beta input) =
      if alpha = beta then (2 : ℚ) ^ n else 0 := by
  have h := finiteAverage_character_mul_character alpha beta
  unfold finiteAverage at h
  rw [FiniteBooleanFourier.cube_card] at h
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at h
  by_cases heq : alpha = beta
  · rw [if_pos heq] at h ⊢
    have hpow : (2 : ℚ) ^ n ≠ 0 := by positivity
    exact (div_eq_one_iff_eq hpow).mp h
  · rw [if_neg heq] at h ⊢
    exact (div_eq_zero_iff).mp h |>.resolve_right (by positivity)

/-! ## Completeness and Parseval -/

/-- At two Boolean inputs, the sum over all Walsh characters is the exact
Kronecker kernel.  This is the completeness identity dual to character
orthogonality. -/
theorem sum_character_kernel {n : Nat} (left right : Fin n → Bool) :
    (∑ alpha : Finset (Fin n),
      character alpha left * character alpha right) =
      if left = right then (2 : ℚ) ^ n else 0 := by
  classical
  let weight : Fin n → ℚ := fun queryIndex ↦
    FiniteBooleanFourier.boolSign (left queryIndex) *
      FiniteBooleanFourier.boolSign (right queryIndex)
  have hterm (alpha : Finset (Fin n)) :
      character alpha left * character alpha right =
        ∏ queryIndex ∈ alpha, weight queryIndex := by
    simp only [character, FiniteBooleanFourier.character, weight]
    rw [Finset.prod_mul_distrib]
  simp_rw [hterm]
  have huniv : (Finset.univ : Finset (Finset (Fin n))) =
      (Finset.univ : Finset (Fin n)).powerset := by
    ext alpha
    simp
  change (∑ alpha ∈ (Finset.univ : Finset (Finset (Fin n))),
    ∏ queryIndex ∈ alpha, weight queryIndex) = _
  rw [huniv, ← Finset.prod_one_add]
  by_cases heq : left = right
  · subst right
    rw [if_pos rfl]
    simp only [weight, FiniteBooleanFourier.boolSign_square]
    norm_num
  · rw [if_neg heq]
    have hexists : ∃ queryIndex : Fin n,
        left queryIndex ≠ right queryIndex := by
      simpa [funext_iff] using heq
    obtain ⟨queryIndex, hqueryIndex⟩ := hexists
    have hweight : weight queryIndex = -1 := by
      cases hleft : left queryIndex <;>
        cases hright : right queryIndex <;>
        simp_all [weight, FiniteBooleanFourier.boolSign]
    have hmem : queryIndex ∈ (Finset.univ : Finset (Fin n)) :=
      Finset.mem_univ queryIndex
    rw [Finset.prod_eq_zero hmem]
    simp [hweight]

/-- Exact Fourier inversion on the Boolean cube. -/
theorem fourier_inversion {n : Nat} (f : (Fin n → Bool) → ℚ)
    (input : Fin n → Bool) :
    (∑ alpha : Finset (Fin n),
      coefficient f alpha * character alpha input) = f input := by
  classical
  have hpow : (2 : ℚ) ^ n ≠ 0 := by positivity
  simp only [coefficient, FiniteBooleanFourier.coefficient]
  calc
    (∑ alpha : Finset (Fin n),
        ((∑ source : Fin n → Bool,
            f source * character alpha source) /
          (2 : ℚ) ^ n) * character alpha input) =
        (∑ alpha : Finset (Fin n),
          (∑ source : Fin n → Bool,
            f source * character alpha source) * character alpha input) /
          (2 : ℚ) ^ n := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro alpha _
      ring
    _ =
        (∑ source : Fin n → Bool,
          f source *
            (∑ alpha : Finset (Fin n),
              character alpha source * character alpha input)) /
          (2 : ℚ) ^ n := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply congrArg (fun value : ℚ ↦ value / (2 : ℚ) ^ n)
      apply Finset.sum_congr rfl
      intro source _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro alpha _
      ring
    _ = f input := by
      simp_rw [sum_character_kernel]
      simp [hpow]

/-- Parseval's identity for exact rational Walsh coefficients. -/
theorem parseval {n : Nat} (f : (Fin n → Bool) → ℚ) :
    (∑ alpha : Finset (Fin n), (coefficient f alpha) ^ 2) =
      finiteAverage (fun input : Fin n → Bool ↦ (f input) ^ 2) := by
  classical
  calc
    (∑ alpha : Finset (Fin n), (coefficient f alpha) ^ 2) =
        ∑ alpha : Finset (Fin n),
          finiteAverage (fun input : Fin n → Bool ↦
            coefficient f alpha *
              (f input * character alpha input)) := by
      apply Finset.sum_congr rfl
      intro alpha _
      rw [FiniteBooleanRestrictionMoment.finiteAverage_const_mul,
        ← coefficient_eq_finiteAverage_mul]
      ring
    _ =
        finiteAverage (fun input : Fin n → Bool ↦
          f input *
            (∑ alpha : Finset (Fin n),
              coefficient f alpha * character alpha input)) := by
      rw [← FiniteBooleanRestrictionMoment.finiteAverage_finset_sum]
      apply FiniteBooleanRestrictionMoment.finiteAverage_congr
      intro input
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro alpha _
      ring
    _ = finiteAverage (fun input : Fin n → Bool ↦ (f input) ^ 2) := by
      apply FiniteBooleanRestrictionMoment.finiteAverage_congr
      intro input
      rw [fourier_inversion]
      ring

/-! ## Bessel and degree energy -/

/-- Bessel's inequality for any displayed finite family of Walsh supports. -/
theorem bessel {n : Nat} (f : (Fin n → Bool) → ℚ)
    (supports : Finset (Finset (Fin n))) :
    (∑ alpha ∈ supports, (coefficient f alpha) ^ 2) ≤
      finiteAverage (fun input : Fin n → Bool ↦ (f input) ^ 2) := by
  calc
    (∑ alpha ∈ supports, (coefficient f alpha) ^ 2) ≤
        ∑ alpha : Finset (Fin n), (coefficient f alpha) ^ 2 := by
      exact Finset.sum_le_univ_sum_of_nonneg fun alpha ↦
        sq_nonneg (coefficient f alpha)
    _ = finiteAverage (fun input : Fin n → Bool ↦ (f input) ^ 2) :=
      parseval f

/-- Fourier energy carried by the homogeneous degree-`k` slice. -/
noncomputable def degreeEnergy {n : Nat} (k : Nat)
    (f : (Fin n → Bool) → ℚ) : ℚ :=
  ∑ alpha ∈ degreeSupports n k, (coefficient f alpha) ^ 2

/-- A homogeneous slice has at most the full squared `L²` energy. -/
theorem degreeEnergy_le_average_sq {n k : Nat}
    (f : (Fin n → Bool) → ℚ) :
    degreeEnergy k f ≤
      finiteAverage (fun input : Fin n → Bool ↦ (f input) ^ 2) := by
  exact bessel f (degreeSupports n k)

/-- A pointwise absolute-value-bounded rational function has squared uniform
average at most one. -/
theorem finiteAverage_sq_le_one_of_abs_le_one
    {Seed : Type*} [Fintype Seed] [Nonempty Seed]
    (f : Seed → ℚ) (hbounded : ∀ seed, |f seed| ≤ 1) :
    finiteAverage (fun seed ↦ (f seed) ^ 2) ≤ 1 := by
  have hcard : (0 : ℚ) < (Fintype.card Seed : ℚ) := by
    exact_mod_cast Fintype.card_pos
  have hpointwise (seed : Seed) : (f seed) ^ 2 ≤ (1 : ℚ) := by
    have habsnonneg : (0 : ℚ) ≤ |f seed| := abs_nonneg _
    have hsquare : |f seed| ^ 2 ≤ (1 : ℚ) := by
      nlinarith [hbounded seed]
    simpa only [sq_abs] using hsquare
  unfold finiteAverage
  apply (div_le_one hcard).2
  calc
    (∑ seed : Seed, (f seed) ^ 2) ≤
        ∑ _seed : Seed, (1 : ℚ) := by
      exact Finset.sum_le_sum fun seed _ ↦ hpointwise seed
    _ = (Fintype.card Seed : ℚ) := by simp

/-- Every pointwise bounded Boolean-cube function has degree-`k` Fourier
energy at most one. -/
theorem degreeEnergy_le_one {n k : Nat}
    (f : (Fin n → Bool) → ℚ)
    (hbounded : ∀ input, |f input| ≤ 1) :
    degreeEnergy k f ≤ 1 := by
  exact (degreeEnergy_le_average_sq f).trans
    (finiteAverage_sq_le_one_of_abs_le_one f hbounded)

/-! ## Prefix-indicator specialization -/

/-- The rational uFBDD compatible-prefix indicator is pointwise bounded by
one. -/
theorem abs_ratCompatiblePrefixIndicator_le_one {n : Nat}
    (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex)
    (input : Fin n → Bool) :
    |B.ratCompatiblePrefixIndicator input vertex| ≤ (1 : ℚ) := by
  classical
  by_cases hprefix : B.HasCompatiblePrefix input vertex <;>
    simp [FiniteUnambiguousFBDD.ratCompatiblePrefixIndicator,
      FiniteUnambiguousFBDD.compatiblePrefixIndicator, hprefix]

/-- Every homogeneous slice of a compatible-prefix indicator has coefficient
energy at most one. -/
theorem ratCompatiblePrefixIndicator_degreeEnergy_le_one {n k : Nat}
    (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex) :
    degreeEnergy k
      (fun input ↦ B.ratCompatiblePrefixIndicator input vertex) ≤ 1 := by
  apply degreeEnergy_le_one
  exact abs_ratCompatiblePrefixIndicator_le_one B vertex

/-- Coefficients of a compatible-prefix indicator vanish outside the
syntactic prefix variables. -/
theorem ratCompatiblePrefixIndicator_coefficient_eq_zero_of_not_subset
    {n : Nat} (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex)
    {alpha : Finset (Fin n)} (hsubset : ¬ alpha ⊆ B.preVars vertex) :
    coefficient (fun input ↦
      B.ratCompatiblePrefixIndicator input vertex) alpha = 0 := by
  exact
    FiniteBooleanFourier.coefficient_eq_zero_of_not_subset_of_dependsOnlyOn
      (B.ratCompatiblePrefixIndicator_dependsOnlyOn_preVars vertex) hsubset

/-- Claim-18 specialization for the homogeneous Fourier slice of a uFBDD
compatible-prefix indicator.  The exact seed moment hypotheses are explicit;
Parseval/Bessel removes the coefficient-energy factor, leaving `p^k`. -/
theorem ratCompatiblePrefixIndicator_restriction_absMoment_sq_le_pow
    {n k : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex)
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool)
    (p : ℚ) (hp : 0 ≤ p)
    (hDOrthogonal :
      ∀ alpha ∈ degreeSupports n k, ∀ beta ∈ degreeSupports n k,
        alpha ≠ beta →
          finiteAverage (fun d : DSeed ↦
            character alpha (D d) * character beta (D d)) = 0)
    (hTMask :
      ∀ alpha ∈ degreeSupports n k,
        finiteAverage (fun t : TSeed ↦
          maskAllZeroIndicator alpha (T t)) = p ^ k) :
    (finiteAverage (fun seed : DSeed × TSeed ↦
      |finiteAverage (fun uniform : Fin n → Bool ↦
        homogeneousPolynomial k
          (coefficient (fun input ↦
            B.ratCompatiblePrefixIndicator input vertex))
          (maskedInput (D seed.1) (T seed.2) uniform))|)) ^ 2 ≤
      p ^ k := by
  calc
    (finiteAverage (fun seed : DSeed × TSeed ↦
        |finiteAverage (fun uniform : Fin n → Bool ↦
          homogeneousPolynomial k
            (coefficient (fun input ↦
              B.ratCompatiblePrefixIndicator input vertex))
            (maskedInput (D seed.1) (T seed.2) uniform))|)) ^ 2 ≤
        p ^ k *
          ∑ alpha ∈ degreeSupports n k,
            (coefficient (fun input ↦
              B.ratCompatiblePrefixIndicator input vertex) alpha) ^ 2 := by
      exact
        FiniteBooleanRestrictionMoment.homogeneousPolynomial_restriction_absMoment_sq_le
          D T p
            (coefficient (fun input ↦
              B.ratCompatiblePrefixIndicator input vertex))
          hDOrthogonal hTMask
    _ ≤ p ^ k * 1 := by
      apply mul_le_mul_of_nonneg_left
      · exact ratCompatiblePrefixIndicator_degreeEnergy_le_one B vertex
      · exact pow_nonneg hp k
    _ = p ^ k := mul_one _

end FiniteBooleanFourierEnergy
end OneTapeMagnification
end Frontier
end Pnp4
