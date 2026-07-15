import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDOneRoundFoolingBound
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Aggregate restriction bounds under full independence

The vertexwise uFBDD restriction argument loses a factor equal to the number
of vertices when it applies Cauchy--Schwarz or the triangle inequality after
the Fourier tail has been decomposed.  This module performs the restriction
calculation on the **entire** high-degree Fourier tail instead.

Under full `n`-wise pattern laws, every pair of distinct Fourier supports is
orthogonal, even when the two supports have different degrees.  Consequently
the exact second moment is the size-free weighted Fourier energy

`sum_{|alpha| > k} p ^ |alpha| * coefficient(f, alpha)^2`.

For `0 <= p <= 1` and `|f| <= 1`, this is at most `p ^ k`.  This conditional
high-tail moment is the nontrivial aggregate statement.  At the level of the
fully averaged output, full `n`-wise unbiasedness is even stronger but
degenerate as a PRG premise: it makes the base source exactly uniform and the
one-round expectation equals the uniform expectation with zero error.

The last section records explicit lower bounds on the cost of this endpoint.
A fully `n`-wise-unbiased finite source is surjective onto the entire Boolean
cube, so a Boolean seed needs at least `n` bits.  At an interior bias, the full
mask source is surjective as well; independent base and mask seeds therefore
have at least `2 ^ (2 * n)` joint states.  Thus the theorem is a genuine
aggregate diagnostic, but full independence cannot be the small-seed local
generator needed by the magnification argument.
-/

namespace FiniteBooleanFullIndependenceRestriction

open scoped BigOperators symmDiff
open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteBooleanBoundedIndependence
open FiniteBooleanFourierEnergy
open FiniteBooleanPerVertexRestrictionBound
open FiniteBooleanVertexSumRestrictionBound
open FiniteBooleanOneRoundFoolingBound
open FiniteUnambiguousFBDD

/-! ## All-degree restricted-character Gram matrix -/

/-- Full pattern unbiasedness makes distinct Walsh characters orthogonal,
without requiring the two supports to have the same degree. -/
theorem character_pair_average_eq_zero_of_fullPatternUnbiased
    {n : Nat} {DSeed : Type*} [Fintype DSeed] [Nonempty DSeed]
    (D : DSeed → Fin n → Bool) (hD : IsKWisePatternUnbiased n D)
    (alpha beta : Finset (Fin n)) (hne : alpha ≠ beta) :
    finiteAverage (fun d : DSeed =>
      character alpha (D d) * character beta (D d)) = 0 := by
  have hcard : (alpha ∆ beta).card ≤ n := by
    simpa using Finset.card_le_univ (alpha ∆ beta)
  have hnonempty : (alpha ∆ beta).Nonempty :=
    Finset.symmDiff_nonempty.mpr hne
  calc
    finiteAverage (fun d : DSeed =>
        character alpha (D d) * character beta (D d)) =
      finiteAverage (fun d : DSeed => character (alpha ∆ beta) (D d)) := by
        apply finiteAverage_congr
        intro d
        exact character_mul_character_eq_symmDiff alpha beta (D d)
    _ = 0 :=
      character_average_eq_zero_of_patternUnbiased
        D hD (alpha ∆ beta) hcard hnonempty

/-- Full false-biased pattern independence gives the exact survival
probability `p ^ |alpha|` for every Fourier support. -/
theorem maskAllZeroIndicator_average_eq_pow_of_fullPatternFalseBiased
    {n : Nat} {TSeed : Type*} [Fintype TSeed] [Nonempty TSeed]
    (T : TSeed → Fin n → Bool) (p : ℚ)
    (hT : IsKWisePatternFalseBiased n p T)
    (alpha : Finset (Fin n)) :
    finiteAverage (fun t : TSeed => maskAllZeroIndicator alpha (T t)) =
      p ^ alpha.card := by
  have hcard : alpha.card ≤ n := by
    simpa using Finset.card_le_univ alpha
  calc
    finiteAverage (fun t : TSeed => maskAllZeroIndicator alpha (T t)) =
      finiteAverage (fun t : TSeed =>
        localPatternIndicator alpha (allFalseAssignment alpha) (T t)) := by
          apply finiteAverage_congr
          intro t
          exact
            (localPatternIndicator_allFalse_eq_maskAllZeroIndicator
              alpha (T t)).symm
    _ = localPatternProductMass p (allFalseAssignment alpha) :=
      hT alpha hcard (allFalseAssignment alpha)
    _ = p ^ alpha.card := localPatternProductMass_allFalse alpha p

/-- Exact all-degree Gram matrix of uniformly filled restricted characters.
The diagonal weight depends on the support size; every off-diagonal entry is
zero. -/
theorem restrictedCharacterAverage_gram_of_fullPatternLaws
    {n : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool)
    (p : ℚ) (hD : IsKWisePatternUnbiased n D)
    (hT : IsKWisePatternFalseBiased n p T)
    (alpha beta : Finset (Fin n)) :
    finiteAverage (fun seed : DSeed × TSeed =>
      restrictedCharacterAverage alpha (D seed.1) (T seed.2) *
        restrictedCharacterAverage beta (D seed.1) (T seed.2)) =
      if alpha = beta then p ^ alpha.card else 0 := by
  calc
    finiteAverage (fun seed : DSeed × TSeed =>
        restrictedCharacterAverage alpha (D seed.1) (T seed.2) *
          restrictedCharacterAverage beta (D seed.1) (T seed.2)) =
      finiteAverage (fun d : DSeed =>
          character alpha (D d) * character beta (D d)) *
        finiteAverage (fun t : TSeed =>
          maskAllZeroIndicator alpha (T t) *
            maskAllZeroIndicator beta (T t)) := by
      rw [← finiteAverage_prod_mul]
      apply finiteAverage_congr
      intro seed
      rw [restrictedCharacterAverage_eq, restrictedCharacterAverage_eq]
      ring
    _ = if alpha = beta then p ^ alpha.card else 0 := by
      by_cases heq : alpha = beta
      · subst beta
        rw [if_pos rfl]
        have hDdiag :
            finiteAverage (fun d : DSeed =>
              character alpha (D d) * character alpha (D d)) = 1 := by
          calc
            finiteAverage (fun d : DSeed =>
                character alpha (D d) * character alpha (D d)) =
              finiteAverage (fun _ : DSeed => (1 : ℚ)) := by
                apply finiteAverage_congr
                intro d
                exact character_square alpha (D d)
            _ = 1 := finiteAverage_one
        have hTdiag :
            finiteAverage (fun t : TSeed =>
              maskAllZeroIndicator alpha (T t) *
                maskAllZeroIndicator alpha (T t)) = p ^ alpha.card := by
          calc
            finiteAverage (fun t : TSeed =>
                maskAllZeroIndicator alpha (T t) *
                  maskAllZeroIndicator alpha (T t)) =
              finiteAverage (fun t : TSeed =>
                maskAllZeroIndicator alpha (T t)) := by
                  apply finiteAverage_congr
                  intro t
                  exact maskAllZeroIndicator_mul_self alpha (T t)
            _ = p ^ alpha.card :=
              maskAllZeroIndicator_average_eq_pow_of_fullPatternFalseBiased
                T p hT alpha
        rw [hDdiag, hTdiag, one_mul]
      · rw [if_neg heq,
          character_pair_average_eq_zero_of_fullPatternUnbiased
            D hD alpha beta heq,
          zero_mul]

/-! ## Exact aggregate high-tail moment -/

/-- Fourier supports whose degree is strictly above `k`. -/
def highDegreeSupports (n k : Nat) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun alpha => k < alpha.card)

@[simp]
theorem mem_highDegreeSupports {n k : Nat} {alpha : Finset (Fin n)} :
    alpha ∈ highDegreeSupports n k ↔ k < alpha.card := by
  simp [highDegreeSupports]

/-- The existing if-then-else definition of the high Fourier tail is exactly
a sum over the filtered set of high-degree supports. -/
theorem ratHighDegreeFourierTail_eq_sum_highDegreeSupports
    {n : Nat} (f : (Fin n → Bool) → ℚ) (k : Nat)
    (input : Fin n → Bool) :
    ratHighDegreeFourierTail f k input =
      ∑ alpha ∈ highDegreeSupports n k,
        coefficient f alpha * character alpha input := by
  classical
  unfold ratHighDegreeFourierTail highDegreeSupports
  rw [Finset.sum_filter]

/-- Uniform filling commutes with the aggregate high-degree Fourier sum. -/
theorem finiteAverage_ratHighDegreeFourierTail_masked
    {n : Nat} (f : (Fin n → Bool) → ℚ) (k : Nat)
    (base mask : Fin n → Bool) :
    finiteAverage (fun uniform : Fin n → Bool =>
      ratHighDegreeFourierTail f k (maskedInput base mask uniform)) =
      ∑ alpha ∈ highDegreeSupports n k,
        coefficient f alpha *
          restrictedCharacterAverage alpha base mask := by
  rw [finiteAverage_congr
    (fun uniform =>
      ratHighDegreeFourierTail_eq_sum_highDegreeSupports
        f k (maskedInput base mask uniform))]
  rw [finiteAverage_finset_sum]
  apply Finset.sum_congr rfl
  intro alpha _
  rw [finiteAverage_const_mul]
  rfl

/-- A varying-weight Kronecker double sum collapses to its diagonal. -/
theorem sum_mul_ite_eq_weighted_diagonal
    {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (c weight : Index → ℚ) :
    (∑ alpha ∈ indices, ∑ beta ∈ indices,
      c alpha * c beta * (if alpha = beta then weight alpha else 0)) =
      ∑ alpha ∈ indices, weight alpha * (c alpha) ^ 2 := by
  calc
    (∑ alpha ∈ indices, ∑ beta ∈ indices,
        c alpha * c beta * (if alpha = beta then weight alpha else 0)) =
      ∑ alpha ∈ indices, c alpha * c alpha * weight alpha := by
        apply Finset.sum_congr rfl
        intro alpha halpha
        rw [Finset.sum_eq_single alpha]
        · simp
        · intro beta _ hbetaNe
          simp [Ne.symm hbetaNe]
        · intro halphaNot
          exact False.elim (halphaNot halpha)
    _ = ∑ alpha ∈ indices, weight alpha * (c alpha) ^ 2 := by
      apply Finset.sum_congr rfl
      intro alpha _
      ring

/-- Exact second moment of the **whole** high-degree Fourier tail after one
full-independence restriction.  No program decomposition and no cardinality
factor occurs. -/
theorem ratHighDegreeFourierTail_restriction_secondMoment_eq
    {n k : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (f : (Fin n → Bool) → ℚ)
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool)
    (p : ℚ) (hD : IsKWisePatternUnbiased n D)
    (hT : IsKWisePatternFalseBiased n p T) :
    finiteAverage (fun seed : DSeed × TSeed =>
      (finiteAverage (fun uniform : Fin n → Bool =>
        ratHighDegreeFourierTail f k
          (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2) =
      ∑ alpha ∈ highDegreeSupports n k,
        p ^ alpha.card * (coefficient f alpha) ^ 2 := by
  classical
  calc
    finiteAverage (fun seed : DSeed × TSeed =>
        (finiteAverage (fun uniform : Fin n → Bool =>
          ratHighDegreeFourierTail f k
            (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2) =
      finiteAverage (fun seed : DSeed × TSeed =>
        (∑ alpha ∈ highDegreeSupports n k,
            coefficient f alpha *
              restrictedCharacterAverage alpha
                (D seed.1) (T seed.2)) *
          (∑ beta ∈ highDegreeSupports n k,
            coefficient f beta *
              restrictedCharacterAverage beta
                (D seed.1) (T seed.2))) := by
        apply finiteAverage_congr
        intro seed
        rw [finiteAverage_ratHighDegreeFourierTail_masked]
        rw [pow_two]
    _ = finiteAverage (fun seed : DSeed × TSeed =>
        ∑ alpha ∈ highDegreeSupports n k,
          ∑ beta ∈ highDegreeSupports n k,
            (coefficient f alpha *
                restrictedCharacterAverage alpha
                  (D seed.1) (T seed.2)) *
              (coefficient f beta *
                restrictedCharacterAverage beta
                  (D seed.1) (T seed.2))) := by
      apply finiteAverage_congr
      intro seed
      rw [Finset.sum_mul_sum]
    _ = ∑ alpha ∈ highDegreeSupports n k,
        ∑ beta ∈ highDegreeSupports n k,
          finiteAverage (fun seed : DSeed × TSeed =>
            (coefficient f alpha *
                restrictedCharacterAverage alpha
                  (D seed.1) (T seed.2)) *
              (coefficient f beta *
                restrictedCharacterAverage beta
                  (D seed.1) (T seed.2))) := by
      rw [finiteAverage_finset_sum]
      apply Finset.sum_congr rfl
      intro alpha _
      rw [finiteAverage_finset_sum]
    _ = ∑ alpha ∈ highDegreeSupports n k,
        ∑ beta ∈ highDegreeSupports n k,
          coefficient f alpha * coefficient f beta *
            (if alpha = beta then p ^ alpha.card else 0) := by
      apply Finset.sum_congr rfl
      intro alpha _
      apply Finset.sum_congr rfl
      intro beta _
      calc
        finiteAverage (fun seed : DSeed × TSeed =>
            (coefficient f alpha *
                restrictedCharacterAverage alpha
                  (D seed.1) (T seed.2)) *
              (coefficient f beta *
                restrictedCharacterAverage beta
                  (D seed.1) (T seed.2))) =
          finiteAverage (fun seed : DSeed × TSeed =>
            (coefficient f alpha * coefficient f beta) *
              (restrictedCharacterAverage alpha
                  (D seed.1) (T seed.2) *
                restrictedCharacterAverage beta
                  (D seed.1) (T seed.2))) := by
            apply finiteAverage_congr
            intro seed
            ring
        _ = (coefficient f alpha * coefficient f beta) *
            finiteAverage (fun seed : DSeed × TSeed =>
              restrictedCharacterAverage alpha
                  (D seed.1) (T seed.2) *
                restrictedCharacterAverage beta
                  (D seed.1) (T seed.2)) :=
          finiteAverage_const_mul _ _
        _ = coefficient f alpha * coefficient f beta *
            (if alpha = beta then p ^ alpha.card else 0) := by
          rw [restrictedCharacterAverage_gram_of_fullPatternLaws
            D T p hD hT alpha beta]
    _ = ∑ alpha ∈ highDegreeSupports n k,
        p ^ alpha.card * (coefficient f alpha) ^ 2 :=
      sum_mul_ite_eq_weighted_diagonal
        (highDegreeSupports n k) (coefficient f)
        (fun alpha => p ^ alpha.card)

/-! ## Cardinality-free energy and one-round bounds -/

/-- The aggregate high-tail second moment is at most `p ^ k` for every
pointwise-one-bounded function.  This removes the program-size factor, at the
cost of full independence in both restriction sources. -/
theorem ratHighDegreeFourierTail_restriction_secondMoment_le_pow
    {n k : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (f : (Fin n → Bool) → ℚ)
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool)
    (p : ℚ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hD : IsKWisePatternUnbiased n D)
    (hT : IsKWisePatternFalseBiased n p T)
    (hbounded : ∀ input, |f input| ≤ 1) :
    finiteAverage (fun seed : DSeed × TSeed =>
      (finiteAverage (fun uniform : Fin n → Bool =>
        ratHighDegreeFourierTail f k
          (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2) ≤
      p ^ k := by
  rw [ratHighDegreeFourierTail_restriction_secondMoment_eq
    f D T p hD hT]
  calc
    (∑ alpha ∈ highDegreeSupports n k,
        p ^ alpha.card * (coefficient f alpha) ^ 2) ≤
      ∑ alpha ∈ highDegreeSupports n k,
        p ^ k * (coefficient f alpha) ^ 2 := by
          apply Finset.sum_le_sum
          intro alpha halpha
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          exact pow_le_pow_of_le_one hp0 hp1
            (Nat.le_of_lt (mem_highDegreeSupports.mp halpha))
    _ = p ^ k * ∑ alpha ∈ highDegreeSupports n k,
        (coefficient f alpha) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ p ^ k * ∑ alpha : Finset (Fin n),
        (coefficient f alpha) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hp0 k)
          exact Finset.sum_le_univ_sum_of_nonneg fun alpha =>
            sq_nonneg (coefficient f alpha)
    _ = p ^ k * finiteAverage (fun input : Fin n → Bool =>
        (f input) ^ 2) := by rw [parseval]
    _ ≤ p ^ k * 1 := by
      apply mul_le_mul_of_nonneg_left
      · exact finiteAverage_sq_le_one_of_abs_le_one f hbounded
      · exact pow_nonneg hp0 k
    _ = p ^ k := mul_one _

/-- Cauchy--Schwarz turns the exact aggregate second moment into the same
bound on the square of the mean absolute high tail. -/
theorem ratHighDegreeFourierTail_restriction_absMoment_sq_le_pow
    {n k : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (f : (Fin n → Bool) → ℚ)
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool)
    (p : ℚ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hD : IsKWisePatternUnbiased n D)
    (hT : IsKWisePatternFalseBiased n p T)
    (hbounded : ∀ input, |f input| ≤ 1) :
    (finiteAverage (fun seed : DSeed × TSeed =>
      |finiteAverage (fun uniform : Fin n → Bool =>
        ratHighDegreeFourierTail f k
          (maskedInput (D seed.1) (T seed.2) uniform))|)) ^ 2 ≤
      p ^ k := by
  calc
    (finiteAverage (fun seed : DSeed × TSeed =>
        |finiteAverage (fun uniform : Fin n → Bool =>
          ratHighDegreeFourierTail f k
            (maskedInput (D seed.1) (T seed.2) uniform))|)) ^ 2 ≤
      finiteAverage (fun seed : DSeed × TSeed =>
        (finiteAverage (fun uniform : Fin n → Bool =>
          ratHighDegreeFourierTail f k
            (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2) :=
        finiteAverage_abs_sq_le_average_sq _
    _ ≤ p ^ k :=
      ratHighDegreeFourierTail_restriction_secondMoment_le_pow
        f D T p hp0 hp1 hD hT hbounded

/-- There are no Fourier supports above the number of input coordinates. -/
theorem ratHighDegreeFourierTail_eq_zero_of_inputBits_le_cutoff
    {n k : Nat} (hcutoff : n ≤ k)
    (f : (Fin n → Bool) → ℚ) (input : Fin n → Bool) :
    ratHighDegreeFourierTail f k input = 0 := by
  classical
  unfold ratHighDegreeFourierTail
  apply Finset.sum_eq_zero
  intro alpha _
  have hcard : alpha.card ≤ n := by
    simpa using Finset.card_le_univ alpha
  simp [not_lt_of_ge (hcard.trans hcutoff)]

/-- Full `n`-wise unbiasedness makes the entire one-round output expectation
exactly uniform, independently of the mask distribution.  This is stronger
than an additive fooling bound, but it is not a short-seed PRG result: the
seed-size theorem below shows that the base source already covers the whole
Boolean cube. -/
theorem oneRoundAverage_eq_uniformAverage_of_fullPatternUnbiased
    {n : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (f : (Fin n → Bool) → ℚ)
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool)
    (hD : IsKWisePatternUnbiased n D) :
    finiteAverage (fun seed : DSeed × TSeed =>
        finiteAverage (fun uniform : Fin n → Bool =>
          f (maskedInput (D seed.1) (T seed.2) uniform))) =
      finiteAverage f := by
  have hexact :=
    oneRoundAverage_eq_uniformAverage_add_highDegreeAverage
      f D T hD
  have htail :
      finiteAverage (fun seed : DSeed × TSeed =>
        finiteAverage (fun uniform : Fin n → Bool =>
          ratHighDegreeFourierTail f n
            (maskedInput (D seed.1) (T seed.2) uniform))) = 0 := by
    calc
      finiteAverage (fun seed : DSeed × TSeed =>
          finiteAverage (fun uniform : Fin n → Bool =>
            ratHighDegreeFourierTail f n
              (maskedInput (D seed.1) (T seed.2) uniform))) =
        finiteAverage (fun _seed : DSeed × TSeed => (0 : ℚ)) := by
          apply finiteAverage_congr
          intro seed
          calc
            finiteAverage (fun uniform : Fin n → Bool =>
                ratHighDegreeFourierTail f n
                  (maskedInput (D seed.1) (T seed.2) uniform)) =
              finiteAverage (fun _uniform : Fin n → Bool => (0 : ℚ)) := by
                apply finiteAverage_congr
                intro uniform
                exact
                  ratHighDegreeFourierTail_eq_zero_of_inputBits_le_cutoff
                    le_rfl f (maskedInput (D seed.1) (T seed.2) uniform)
            _ = 0 :=
              FiniteBooleanPerVertexRestrictionBound.finiteAverage_const 0
      _ = 0 :=
        FiniteBooleanPerVertexRestrictionBound.finiteAverage_const 0
  rw [hexact, htail, add_zero]

/-! ## Exact seed-size barrier for full independence -/

/-- Restriction to the full coordinate set is injective as a map from
ambient Boolean strings to local assignments. -/
theorem eq_of_restrictAssignment_univ_eq
    {n : Nat} {left right : Fin n → Bool}
    (h : restrictAssignment (Finset.univ : Finset (Fin n)) left =
      restrictAssignment Finset.univ right) :
    left = right := by
  funext queryIndex
  have hvalue := congrFun h
    (⟨queryIndex, Finset.mem_univ queryIndex⟩ :
      ↥(Finset.univ : Finset (Fin n)))
  simpa [restrictAssignment] using hvalue

/-- A fully `n`-wise-unbiased finite source hits every Boolean string. -/
theorem surjective_of_fullPatternUnbiased
    {n : Nat} {Seed : Type*} [Fintype Seed] [Nonempty Seed]
    (source : Seed → Fin n → Bool)
    (hsource : IsKWisePatternUnbiased n source) :
    Function.Surjective source := by
  intro target
  let support : Finset (Fin n) := Finset.univ
  let pattern : LocalAssignment support :=
    restrictAssignment support target
  have hcard : support.card ≤ n := by
    simp [support]
  have hmass := hsource support hcard pattern
  have hpositive : (0 : ℚ) < 1 / (2 : ℚ) ^ support.card := by
    positivity
  by_contra hmiss
  push_neg at hmiss
  have hzero : finiteAverage (fun seed : Seed =>
      localPatternIndicator support pattern (source seed)) = 0 := by
    calc
      finiteAverage (fun seed : Seed =>
          localPatternIndicator support pattern (source seed)) =
        finiteAverage (fun _seed : Seed => (0 : ℚ)) := by
          apply finiteAverage_congr
          intro seed
          have hne : restrictAssignment support (source seed) ≠ pattern := by
            intro heq
            apply hmiss seed
            apply eq_of_restrictAssignment_univ_eq
            simpa [support, pattern] using heq
          simp [localPatternIndicator, hne]
      _ = 0 := FiniteBooleanPerVertexRestrictionBound.finiteAverage_const 0
  rw [hmass] at hzero
  linarith

/-- The seed type of a fully unbiased source has at least `2 ^ n` points. -/
theorem two_pow_le_card_seed_of_fullPatternUnbiased
    {n : Nat} {Seed : Type*} [Fintype Seed] [Nonempty Seed]
    (source : Seed → Fin n → Bool)
    (hsource : IsKWisePatternUnbiased n source) :
    2 ^ n ≤ Fintype.card Seed := by
  have hcard := Fintype.card_le_of_surjective source
    (surjective_of_fullPatternUnbiased source hsource)
  simpa using hcard

/-- In particular, a fully unbiased source generated by `seedBits` Boolean
bits needs at least `n` seed bits. -/
theorem inputBits_le_seedBits_of_fullPatternUnbiased
    {n seedBits : Nat}
    (source : (Fin seedBits → Bool) → Fin n → Bool)
    (hsource : IsKWisePatternUnbiased n source) :
    n ≤ seedBits := by
  have hpow : 2 ^ n ≤ 2 ^ seedBits := by
    simpa using
      (two_pow_le_card_seed_of_fullPatternUnbiased source hsource)
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hpow

/-- Every full-cube pattern has positive product mass when both Boolean
outcomes have positive probability. -/
theorem localPatternProductMass_pos_of_between
    {n : Nat} {support : Finset (Fin n)}
    (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1)
    (pattern : LocalAssignment support) :
    0 < localPatternProductMass p pattern := by
  classical
  unfold localPatternProductMass
  apply Finset.prod_pos
  intro queryIndex _
  by_cases hbit : pattern queryIndex
  · simp [hbit]
    linarith
  · simp [hbit, hp0]

/-- For an interior bias `0 < p < 1`, a fully `n`-wise false-biased source
also hits every Boolean string. -/
theorem surjective_of_fullPatternFalseBiased
    {n : Nat} {Seed : Type*} [Fintype Seed] [Nonempty Seed]
    (source : Seed → Fin n → Bool) (p : ℚ)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hsource : IsKWisePatternFalseBiased n p source) :
    Function.Surjective source := by
  intro target
  let support : Finset (Fin n) := Finset.univ
  let pattern : LocalAssignment support :=
    restrictAssignment support target
  have hcard : support.card ≤ n := by
    simp [support]
  have hmass := hsource support hcard pattern
  have hpositive : (0 : ℚ) < localPatternProductMass p pattern :=
    localPatternProductMass_pos_of_between p hp0 hp1 pattern
  by_contra hmiss
  push_neg at hmiss
  have hzero : finiteAverage (fun seed : Seed =>
      localPatternIndicator support pattern (source seed)) = 0 := by
    calc
      finiteAverage (fun seed : Seed =>
          localPatternIndicator support pattern (source seed)) =
        finiteAverage (fun _seed : Seed => (0 : ℚ)) := by
          apply finiteAverage_congr
          intro seed
          have hne : restrictAssignment support (source seed) ≠ pattern := by
            intro heq
            apply hmiss seed
            apply eq_of_restrictAssignment_univ_eq
            simpa [support, pattern] using heq
          simp [localPatternIndicator, hne]
      _ = 0 := FiniteBooleanPerVertexRestrictionBound.finiteAverage_const 0
  rw [hmass] at hzero
  linarith

/-- An interior fully biased mask source also needs at least `2 ^ n` seed
states. -/
theorem two_pow_le_card_seed_of_fullPatternFalseBiased
    {n : Nat} {Seed : Type*} [Fintype Seed] [Nonempty Seed]
    (source : Seed → Fin n → Bool) (p : ℚ)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hsource : IsKWisePatternFalseBiased n p source) :
    2 ^ n ≤ Fintype.card Seed := by
  have hcard := Fintype.card_le_of_surjective source
    (surjective_of_fullPatternFalseBiased source p hp0 hp1 hsource)
  simpa using hcard

/-- With independent base and mask seed types, full laws at an interior bias
require at least `2 ^ (2 * n)` joint seed states.  This is only a lower bound;
rational probability denominators may force larger seed spaces. -/
theorem two_pow_two_mul_le_card_prod_seed_of_fullPatternLaws
    {n : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool)
    (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1)
    (hD : IsKWisePatternUnbiased n D)
    (hT : IsKWisePatternFalseBiased n p T) :
    2 ^ (2 * n) ≤ Fintype.card (DSeed × TSeed) := by
  have hDcard : 2 ^ n ≤ Fintype.card DSeed :=
    two_pow_le_card_seed_of_fullPatternUnbiased D hD
  have hTcard : 2 ^ n ≤ Fintype.card TSeed :=
    two_pow_le_card_seed_of_fullPatternFalseBiased T p hp0 hp1 hT
  calc
    2 ^ (2 * n) = 2 ^ n * 2 ^ n := by
      rw [show 2 * n = n + n by omega, pow_add]
    _ ≤ Fintype.card DSeed * Fintype.card TSeed :=
      Nat.mul_le_mul hDcard hTcard
    _ = Fintype.card (DSeed × TSeed) := by simp

end FiniteBooleanFullIndependenceRestriction
end OneTapeMagnification
end Frontier
end Pnp4
