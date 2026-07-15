import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanFourier
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Exact finite restriction moments for homogeneous Walsh polynomials

This module isolates the finite, rational core of the homogeneous restriction
estimate used in switching-style pseudorandomness arguments.  The seed spaces
are arbitrary finite nonempty types.  Orthogonality of distinct degree-`k`
characters is an explicit hypothesis on the `D` distribution, and exact
degree-`k` mask survival is an explicit hypothesis on the `T` distribution.

There are no asymptotics or measure-theoretic probability spaces here: every
expectation is a normalized finite sum in `ℚ`.
-/

namespace FiniteBooleanRestrictionMoment

open scoped BigOperators

/-- The exact uniform average of a rational-valued function on a finite type. -/
noncomputable def finiteAverage {Seed : Type*} [Fintype Seed]
    (value : Seed → ℚ) : ℚ :=
  (∑ seed : Seed, value seed) / (Fintype.card Seed : ℚ)

/-- Pointwise equality may be used under a finite average. -/
theorem finiteAverage_congr {Seed : Type*} [Fintype Seed]
    {f g : Seed → ℚ} (h : ∀ seed, f seed = g seed) :
    finiteAverage f = finiteAverage g := by
  unfold finiteAverage
  congr 1
  apply Finset.sum_congr rfl
  intro seed _
  exact h seed

/-- Constants factor through a finite average. -/
theorem finiteAverage_const_mul {Seed : Type*} [Fintype Seed]
    (constant : ℚ) (f : Seed → ℚ) :
    finiteAverage (fun seed => constant * f seed) =
      constant * finiteAverage f := by
  unfold finiteAverage
  rw [← Finset.mul_sum]
  ring

/-- Finite averages commute with finite sums. -/
theorem finiteAverage_finset_sum {Seed Index : Type*} [Fintype Seed]
    (indices : Finset Index) (f : Index → Seed → ℚ) :
    finiteAverage (fun seed => ∑ index ∈ indices, f index seed) =
      ∑ index ∈ indices, finiteAverage (f index) := by
  unfold finiteAverage
  rw [Finset.sum_comm]
  simp only [Finset.sum_div]

/-- A normalized finite average of `1` is `1` on a nonempty seed space. -/
@[simp]
theorem finiteAverage_one {Seed : Type*} [Fintype Seed] [Nonempty Seed] :
    finiteAverage (fun _ : Seed => (1 : ℚ)) = 1 := by
  simp [finiteAverage, Fintype.card_ne_zero]

/-- Independent finite averages factor on a product seed space. -/
theorem finiteAverage_prod_mul {Left Right : Type*}
    [Fintype Left] [Fintype Right] (f : Left → ℚ) (g : Right → ℚ) :
    finiteAverage (fun seed : Left × Right => f seed.1 * g seed.2) =
      finiteAverage f * finiteAverage g := by
  unfold finiteAverage
  rw [Fintype.sum_prod_type, ← Fintype.sum_mul_sum]
  simp only [Fintype.card_prod, Nat.cast_mul]
  ring

/-- Averaging on a product seed type is the same as iterated averaging. -/
theorem finiteAverage_prod_eq_iterated {Left Right : Type*}
    [Fintype Left] [Fintype Right] (f : Left → Right → ℚ) :
    finiteAverage (fun seed : Left × Right => f seed.1 seed.2) =
      finiteAverage (fun left : Left =>
        finiteAverage (fun right : Right => f left right)) := by
  unfold finiteAverage
  rw [Fintype.sum_prod_type]
  simp only [Fintype.card_prod, Nat.cast_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  ring

/-- Cauchy--Schwarz for an exact normalized finite rational average. -/
theorem finiteAverage_sq_le_average_sq {Seed : Type*}
    [Fintype Seed] [Nonempty Seed] (f : Seed → ℚ) :
    (finiteAverage f) ^ 2 ≤ finiteAverage (fun seed => (f seed) ^ 2) := by
  have hcard : (0 : ℚ) < (Fintype.card Seed : ℚ) := by
    exact_mod_cast Fintype.card_pos
  have hcauchy :
      (∑ seed : Seed, f seed) ^ 2 ≤
        (Fintype.card Seed : ℚ) * ∑ seed : Seed, (f seed) ^ 2 := by
    simpa using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset Seed)) (f := f))
  unfold finiteAverage
  calc
    ((∑ seed : Seed, f seed) / (Fintype.card Seed : ℚ)) ^ 2 =
        (∑ seed : Seed, f seed) ^ 2 /
          (Fintype.card Seed : ℚ) ^ 2 := by ring
    _ ≤ ((Fintype.card Seed : ℚ) * ∑ seed : Seed, (f seed) ^ 2) /
          (Fintype.card Seed : ℚ) ^ 2 := by
      exact (div_le_div_iff_of_pos_right (sq_pos_of_pos hcard)).2 hcauchy
    _ = (∑ seed : Seed, (f seed) ^ 2) /
          (Fintype.card Seed : ℚ) := by
      field_simp [ne_of_gt hcard]
      ring

/-- The absolute first moment is bounded by the square root form of the second
moment, stated without introducing square roots. -/
theorem finiteAverage_abs_sq_le_average_sq {Seed : Type*}
    [Fintype Seed] [Nonempty Seed] (f : Seed → ℚ) :
    (finiteAverage (fun seed => |f seed|)) ^ 2 ≤
      finiteAverage (fun seed => (f seed) ^ 2) := by
  simpa only [sq_abs] using
    (finiteAverage_sq_le_average_sq (fun seed => |f seed|))

/-- XOR a base string with the live coordinates of a uniform string.  A false
mask bit freezes the coordinate at `base`; a true mask bit leaves it live. -/
def maskedInput {n : Nat} (base mask uniform : Fin n → Bool) :
    Fin n → Bool :=
  fun queryIndex => Bool.xor (base queryIndex)
    (Bool.and (mask queryIndex) (uniform queryIndex))

/-- The rational indicator that every coordinate in `alpha` is frozen. -/
def maskAllZeroIndicator {n : Nat} (alpha : Finset (Fin n))
    (mask : Fin n → Bool) : ℚ :=
  if ∀ queryIndex ∈ alpha, mask queryIndex = false then 1 else 0

/-- The set of all Walsh supports of degree exactly `k`. -/
def degreeSupports (n k : Nat) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun alpha : Finset (Fin n) => alpha.card = k)

@[simp]
theorem mem_degreeSupports {n k : Nat} {alpha : Finset (Fin n)} :
    alpha ∈ degreeSupports n k ↔ alpha.card = k := by
  simp [degreeSupports]

/-- A Walsh polynomial whose displayed terms all have degree exactly `k`. -/
def homogeneousPolynomial {n : Nat} (k : Nat)
    (coefficient : Finset (Fin n) → ℚ) (input : Fin n → Bool) : ℚ :=
  ∑ alpha ∈ degreeSupports n k,
    coefficient alpha * FiniteBooleanFourier.character alpha input

@[simp]
theorem boolSign_xor (left right : Bool) :
    FiniteBooleanFourier.boolSign (Bool.xor left right) =
      FiniteBooleanFourier.boolSign left *
        FiniteBooleanFourier.boolSign right := by
  cases left <;> cases right <;>
    norm_num [FiniteBooleanFourier.boolSign]

/-- Walsh characters are multiplicative under coordinatewise XOR. -/
theorem character_xor {n : Nat} (alpha : Finset (Fin n))
    (left right : Fin n → Bool) :
    FiniteBooleanFourier.character alpha (fun queryIndex =>
      Bool.xor (left queryIndex) (right queryIndex)) =
      FiniteBooleanFourier.character alpha left *
        FiniteBooleanFourier.character alpha right := by
  unfold FiniteBooleanFourier.character
  simp_rw [boolSign_xor]
  exact Finset.prod_mul_distrib

/-- A character of a masked input separates into its base character and its
live-uniform character. -/
theorem character_maskedInput {n : Nat} (alpha : Finset (Fin n))
    (base mask uniform : Fin n → Bool) :
    FiniteBooleanFourier.character alpha (maskedInput base mask uniform) =
      FiniteBooleanFourier.character alpha base *
        FiniteBooleanFourier.character alpha (fun queryIndex =>
          Bool.and (mask queryIndex) (uniform queryIndex)) := by
  simpa [maskedInput] using
    character_xor alpha base
      (fun queryIndex => Bool.and (mask queryIndex) (uniform queryIndex))

@[simp]
theorem maskAllZeroIndicator_mul_self {n : Nat}
    (alpha : Finset (Fin n)) (mask : Fin n → Bool) :
    maskAllZeroIndicator alpha mask * maskAllZeroIndicator alpha mask =
      maskAllZeroIndicator alpha mask := by
  unfold maskAllZeroIndicator
  split_ifs <;> norm_num

/-- Before normalization, the uniform sum of the live part of a character is
the cube cardinality exactly when every support coordinate is frozen, and is
zero otherwise. -/
theorem sum_character_and_eq_card_mul_indicator {n : Nat}
    (alpha : Finset (Fin n)) (mask : Fin n → Bool) :
    (∑ uniform : Fin n → Bool,
        FiniteBooleanFourier.character alpha (fun queryIndex =>
          Bool.and (mask queryIndex) (uniform queryIndex))) =
      (Fintype.card (Fin n → Bool) : ℚ) *
        maskAllZeroIndicator alpha mask := by
  classical
  by_cases hzero : ∀ queryIndex ∈ alpha, mask queryIndex = false
  · have hcharacter (uniform : Fin n → Bool) :
        FiniteBooleanFourier.character alpha (fun queryIndex =>
          Bool.and (mask queryIndex) (uniform queryIndex)) = 1 := by
      unfold FiniteBooleanFourier.character
      apply Finset.prod_eq_one
      intro queryIndex hqueryIndex
      simp [hzero queryIndex hqueryIndex]
    simp_rw [hcharacter]
    rw [maskAllZeroIndicator, if_pos hzero]
    simp
  · have hexists : ∃ queryIndex ∈ alpha, mask queryIndex = true := by
      by_contra hnone
      apply hzero
      intro queryIndex hqueryIndex
      cases hmask : mask queryIndex
      · rfl
      · exact False.elim (hnone ⟨queryIndex, hqueryIndex, hmask⟩)
    obtain ⟨coordinate, hcoordinate, hmaskCoordinate⟩ := hexists
    let summand : (Fin n → Bool) → ℚ := fun uniform =>
      FiniteBooleanFourier.character alpha (fun queryIndex =>
        Bool.and (mask queryIndex) (uniform queryIndex))
    have hmaskedFlip (uniform : Fin n → Bool) :
        (fun queryIndex =>
          Bool.and (mask queryIndex)
            (FiniteBooleanFourier.flipCoordinate uniform coordinate queryIndex)) =
          FiniteBooleanFourier.flipCoordinate
            (fun queryIndex => Bool.and (mask queryIndex) (uniform queryIndex))
            coordinate := by
      funext queryIndex
      by_cases hqueryIndex : queryIndex = coordinate
      · subst queryIndex
        simp [hmaskCoordinate]
      · simp [FiniteBooleanFourier.flipCoordinate, hqueryIndex]
    have hflip (uniform : Fin n → Bool) :
        summand (FiniteBooleanFourier.flipCoordinate uniform coordinate) =
          -summand uniform := by
      dsimp only [summand]
      rw [hmaskedFlip]
      exact FiniteBooleanFourier.character_flip_of_mem hcoordinate _
    have hpermute :
        (∑ uniform : Fin n → Bool,
            summand (FiniteBooleanFourier.flipCoordinate uniform coordinate)) =
          ∑ uniform : Fin n → Bool, summand uniform := by
      exact (FiniteBooleanFourier.flipEquiv coordinate).sum_comp summand
    have hneg :
        (∑ uniform : Fin n → Bool,
            summand (FiniteBooleanFourier.flipCoordinate uniform coordinate)) =
          -(∑ uniform : Fin n → Bool, summand uniform) := by
      simp_rw [hflip]
      simp
    have hsum : (∑ uniform : Fin n → Bool, summand uniform) = 0 := by
      linarith
    change (∑ uniform : Fin n → Bool, summand uniform) = _
    rw [hsum, maskAllZeroIndicator, if_neg hzero]
    simp

/-- Exact uniform cancellation of a masked Walsh character. -/
theorem finiteAverage_character_and_eq_indicator {n : Nat}
    (alpha : Finset (Fin n)) (mask : Fin n → Bool) :
    finiteAverage (fun uniform : Fin n → Bool =>
      FiniteBooleanFourier.character alpha (fun queryIndex =>
        Bool.and (mask queryIndex) (uniform queryIndex))) =
      maskAllZeroIndicator alpha mask := by
  unfold finiteAverage
  rw [sum_character_and_eq_card_mul_indicator]
  have hcard : (Fintype.card (Fin n → Bool) : ℚ) ≠ 0 := by
    positivity
  field_simp [hcard]

/-- The uniform average of one restricted character. -/
noncomputable def restrictedCharacterAverage {n : Nat}
    (alpha : Finset (Fin n)) (base mask : Fin n → Bool) : ℚ :=
  finiteAverage (fun uniform : Fin n → Bool =>
    FiniteBooleanFourier.character alpha (maskedInput base mask uniform))

/-- A restricted character is the base character times the indicator that its
whole support was frozen. -/
theorem restrictedCharacterAverage_eq {n : Nat}
    (alpha : Finset (Fin n)) (base mask : Fin n → Bool) :
    restrictedCharacterAverage alpha base mask =
      FiniteBooleanFourier.character alpha base *
        maskAllZeroIndicator alpha mask := by
  unfold restrictedCharacterAverage
  calc
    finiteAverage (fun uniform : Fin n → Bool =>
        FiniteBooleanFourier.character alpha
          (maskedInput base mask uniform)) =
      finiteAverage (fun uniform : Fin n → Bool =>
        FiniteBooleanFourier.character alpha base *
          FiniteBooleanFourier.character alpha (fun queryIndex =>
            Bool.and (mask queryIndex) (uniform queryIndex))) := by
        apply finiteAverage_congr
        intro uniform
        exact character_maskedInput alpha base mask uniform
    _ = FiniteBooleanFourier.character alpha base *
        finiteAverage (fun uniform : Fin n → Bool =>
          FiniteBooleanFourier.character alpha (fun queryIndex =>
            Bool.and (mask queryIndex) (uniform queryIndex))) :=
      finiteAverage_const_mul _ _
    _ = FiniteBooleanFourier.character alpha base *
        maskAllZeroIndicator alpha mask := by
      rw [finiteAverage_character_and_eq_indicator]

/-- Uniform averaging of a homogeneous polynomial is the corresponding finite
sum of restricted-character averages. -/
theorem finiteAverage_homogeneousPolynomial_masked {n k : Nat}
    (coefficient : Finset (Fin n) → ℚ)
    (base mask : Fin n → Bool) :
    finiteAverage (fun uniform : Fin n → Bool =>
      homogeneousPolynomial k coefficient (maskedInput base mask uniform)) =
      ∑ alpha ∈ degreeSupports n k,
        coefficient alpha * restrictedCharacterAverage alpha base mask := by
  unfold homogeneousPolynomial
  rw [finiteAverage_finset_sum]
  apply Finset.sum_congr rfl
  intro alpha _
  rw [finiteAverage_const_mul]
  rfl

/-- Only diagonal terms survive a Kronecker-delta double sum. -/
theorem sum_mul_ite_eq_diagonal {Index : Type*} [DecidableEq Index]
    (indices : Finset Index) (coefficient : Index → ℚ) (weight : ℚ) :
    (∑ alpha ∈ indices, ∑ beta ∈ indices,
        coefficient alpha * coefficient beta *
          (if alpha = beta then weight else 0)) =
      weight * ∑ alpha ∈ indices, (coefficient alpha) ^ 2 := by
  calc
    (∑ alpha ∈ indices, ∑ beta ∈ indices,
        coefficient alpha * coefficient beta *
          (if alpha = beta then weight else 0)) =
      ∑ alpha ∈ indices,
        coefficient alpha * coefficient alpha * weight := by
      apply Finset.sum_congr rfl
      intro alpha halpha
      rw [Finset.sum_eq_single alpha]
      · simp
      · intro beta hbeta hbetaNe
        simp [Ne.symm hbetaNe]
      · intro halphaNot
        exact False.elim (halphaNot halpha)
    _ = weight * ∑ alpha ∈ indices, (coefficient alpha) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro alpha _
      ring

/-- Exact Gram matrix of the restricted degree-`k` characters.  Distinct
supports vanish by the stated `D` orthogonality hypothesis; diagonal terms are
the stated exact mask-survival probability. -/
theorem restrictedCharacterAverage_gram
    {n k : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool)
    (p : ℚ)
    (hDOrthogonal :
      ∀ alpha ∈ degreeSupports n k, ∀ beta ∈ degreeSupports n k,
        alpha ≠ beta →
          finiteAverage (fun d : DSeed =>
            FiniteBooleanFourier.character alpha (D d) *
              FiniteBooleanFourier.character beta (D d)) = 0)
    (hTMask :
      ∀ alpha ∈ degreeSupports n k,
        finiteAverage (fun t : TSeed =>
          maskAllZeroIndicator alpha (T t)) = p ^ k)
    (alpha beta : Finset (Fin n))
    (halpha : alpha ∈ degreeSupports n k)
    (hbeta : beta ∈ degreeSupports n k) :
    finiteAverage (fun seed : DSeed × TSeed =>
      restrictedCharacterAverage alpha (D seed.1) (T seed.2) *
        restrictedCharacterAverage beta (D seed.1) (T seed.2)) =
      if alpha = beta then p ^ k else 0 := by
  calc
    finiteAverage (fun seed : DSeed × TSeed =>
        restrictedCharacterAverage alpha (D seed.1) (T seed.2) *
          restrictedCharacterAverage beta (D seed.1) (T seed.2)) =
      finiteAverage (fun d : DSeed =>
          FiniteBooleanFourier.character alpha (D d) *
            FiniteBooleanFourier.character beta (D d)) *
        finiteAverage (fun t : TSeed =>
          maskAllZeroIndicator alpha (T t) *
            maskAllZeroIndicator beta (T t)) := by
      rw [← finiteAverage_prod_mul]
      apply finiteAverage_congr
      intro seed
      rw [restrictedCharacterAverage_eq, restrictedCharacterAverage_eq]
      ring
    _ = if alpha = beta then p ^ k else 0 := by
      by_cases heq : alpha = beta
      · subst beta
        rw [if_pos rfl]
        have hDdiag :
            finiteAverage (fun d : DSeed =>
              FiniteBooleanFourier.character alpha (D d) *
                FiniteBooleanFourier.character alpha (D d)) = 1 := by
          calc
            finiteAverage (fun d : DSeed =>
                FiniteBooleanFourier.character alpha (D d) *
                  FiniteBooleanFourier.character alpha (D d)) =
              finiteAverage (fun _ : DSeed => (1 : ℚ)) := by
                apply finiteAverage_congr
                intro d
                exact FiniteBooleanFourier.character_square alpha (D d)
            _ = 1 := finiteAverage_one
        have hTdiag :
            finiteAverage (fun t : TSeed =>
              maskAllZeroIndicator alpha (T t) *
                maskAllZeroIndicator alpha (T t)) = p ^ k := by
          calc
            finiteAverage (fun t : TSeed =>
                maskAllZeroIndicator alpha (T t) *
                  maskAllZeroIndicator alpha (T t)) =
              finiteAverage (fun t : TSeed =>
                maskAllZeroIndicator alpha (T t)) := by
                  apply finiteAverage_congr
                  intro t
                  exact maskAllZeroIndicator_mul_self alpha (T t)
            _ = p ^ k := hTMask alpha halpha
        rw [hDdiag, hTdiag, one_mul]
      · rw [if_neg heq, hDOrthogonal alpha halpha beta hbeta heq,
          zero_mul]

/-- Exact second moment of the uniformly restricted homogeneous polynomial.
This is the finite rational form of the orthogonality calculation underlying
Claim 18: all off-diagonal Walsh terms vanish, and every diagonal degree-`k`
term survives with weight exactly `p^k`. -/
theorem homogeneousPolynomial_restriction_secondMoment_eq
    {n k : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool)
    (p : ℚ) (coefficient : Finset (Fin n) → ℚ)
    (hDOrthogonal :
      ∀ alpha ∈ degreeSupports n k, ∀ beta ∈ degreeSupports n k,
        alpha ≠ beta →
          finiteAverage (fun d : DSeed =>
            FiniteBooleanFourier.character alpha (D d) *
              FiniteBooleanFourier.character beta (D d)) = 0)
    (hTMask :
      ∀ alpha ∈ degreeSupports n k,
        finiteAverage (fun t : TSeed =>
          maskAllZeroIndicator alpha (T t)) = p ^ k) :
    finiteAverage (fun seed : DSeed × TSeed =>
      (finiteAverage (fun uniform : Fin n → Bool =>
        homogeneousPolynomial k coefficient
          (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2) =
      p ^ k * ∑ alpha ∈ degreeSupports n k,
        (coefficient alpha) ^ 2 := by
  calc
    finiteAverage (fun seed : DSeed × TSeed =>
        (finiteAverage (fun uniform : Fin n → Bool =>
          homogeneousPolynomial k coefficient
            (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2) =
      finiteAverage (fun seed : DSeed × TSeed =>
        (∑ alpha ∈ degreeSupports n k,
            coefficient alpha *
              restrictedCharacterAverage alpha (D seed.1) (T seed.2)) *
          (∑ beta ∈ degreeSupports n k,
            coefficient beta *
              restrictedCharacterAverage beta (D seed.1) (T seed.2))) := by
        apply finiteAverage_congr
        intro seed
        rw [finiteAverage_homogeneousPolynomial_masked]
        rw [pow_two]
    _ = finiteAverage (fun seed : DSeed × TSeed =>
        ∑ alpha ∈ degreeSupports n k,
          ∑ beta ∈ degreeSupports n k,
            (coefficient alpha *
                restrictedCharacterAverage alpha (D seed.1) (T seed.2)) *
              (coefficient beta *
                restrictedCharacterAverage beta (D seed.1) (T seed.2))) := by
      apply finiteAverage_congr
      intro seed
      rw [Finset.sum_mul_sum]
    _ = ∑ alpha ∈ degreeSupports n k,
        ∑ beta ∈ degreeSupports n k,
          finiteAverage (fun seed : DSeed × TSeed =>
            (coefficient alpha *
                restrictedCharacterAverage alpha (D seed.1) (T seed.2)) *
              (coefficient beta *
                restrictedCharacterAverage beta (D seed.1) (T seed.2))) := by
      rw [finiteAverage_finset_sum]
      apply Finset.sum_congr rfl
      intro alpha _
      rw [finiteAverage_finset_sum]
    _ = ∑ alpha ∈ degreeSupports n k,
        ∑ beta ∈ degreeSupports n k,
          coefficient alpha * coefficient beta *
            (if alpha = beta then p ^ k else 0) := by
      apply Finset.sum_congr rfl
      intro alpha halpha
      apply Finset.sum_congr rfl
      intro beta hbeta
      calc
        finiteAverage (fun seed : DSeed × TSeed =>
            (coefficient alpha *
                restrictedCharacterAverage alpha (D seed.1) (T seed.2)) *
              (coefficient beta *
                restrictedCharacterAverage beta (D seed.1) (T seed.2))) =
          finiteAverage (fun seed : DSeed × TSeed =>
            (coefficient alpha * coefficient beta) *
              (restrictedCharacterAverage alpha (D seed.1) (T seed.2) *
                restrictedCharacterAverage beta (D seed.1) (T seed.2))) := by
            apply finiteAverage_congr
            intro seed
            ring
        _ = (coefficient alpha * coefficient beta) *
            finiteAverage (fun seed : DSeed × TSeed =>
              restrictedCharacterAverage alpha (D seed.1) (T seed.2) *
                restrictedCharacterAverage beta (D seed.1) (T seed.2)) :=
          finiteAverage_const_mul _ _
        _ = coefficient alpha * coefficient beta *
            (if alpha = beta then p ^ k else 0) := by
          rw [restrictedCharacterAverage_gram D T p hDOrthogonal hTMask
            alpha beta halpha hbeta]
    _ = p ^ k * ∑ alpha ∈ degreeSupports n k,
        (coefficient alpha) ^ 2 :=
      sum_mul_ite_eq_diagonal (degreeSupports n k) coefficient (p ^ k)

/-- Finite rational Claim-18 square-moment bound.  No sign assumption on `p`
is needed: its occurrence on the right is forced by the exact mask hypothesis
and the preceding second-moment identity. -/
theorem homogeneousPolynomial_restriction_absMoment_sq_le
    {n k : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (D : DSeed → Fin n → Bool) (T : TSeed → Fin n → Bool)
    (p : ℚ) (coefficient : Finset (Fin n) → ℚ)
    (hDOrthogonal :
      ∀ alpha ∈ degreeSupports n k, ∀ beta ∈ degreeSupports n k,
        alpha ≠ beta →
          finiteAverage (fun d : DSeed =>
            FiniteBooleanFourier.character alpha (D d) *
              FiniteBooleanFourier.character beta (D d)) = 0)
    (hTMask :
      ∀ alpha ∈ degreeSupports n k,
        finiteAverage (fun t : TSeed =>
          maskAllZeroIndicator alpha (T t)) = p ^ k) :
    (finiteAverage (fun seed : DSeed × TSeed =>
      |finiteAverage (fun uniform : Fin n → Bool =>
        homogeneousPolynomial k coefficient
          (maskedInput (D seed.1) (T seed.2) uniform))|)) ^ 2 ≤
      p ^ k * ∑ alpha ∈ degreeSupports n k,
        (coefficient alpha) ^ 2 := by
  calc
    (finiteAverage (fun seed : DSeed × TSeed =>
        |finiteAverage (fun uniform : Fin n → Bool =>
          homogeneousPolynomial k coefficient
            (maskedInput (D seed.1) (T seed.2) uniform))|)) ^ 2 ≤
      finiteAverage (fun seed : DSeed × TSeed =>
        (finiteAverage (fun uniform : Fin n → Bool =>
          homogeneousPolynomial k coefficient
            (maskedInput (D seed.1) (T seed.2) uniform))) ^ 2) :=
        finiteAverage_abs_sq_le_average_sq _
    _ = p ^ k * ∑ alpha ∈ degreeSupports n k,
        (coefficient alpha) ^ 2 :=
      homogeneousPolynomial_restriction_secondMoment_eq
        D T p coefficient hDOrthogonal hTMask

end FiniteBooleanRestrictionMoment
end OneTapeMagnification
end Frontier
end Pnp4
