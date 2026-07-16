import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanAffineRoundsLocality
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorFourierFactorization

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Prefix-stable Fourier factorization of the mandatory canonical selector

The affine prefixes used by the concrete DPTW hybrid are iterated
coordinatewise masked restrictions.  They preserve every advertised block
dependency support.  Hence the exact disjoint block-product coefficient
formula for an installed canonical-alpha component remains valid after an
arbitrary fixed affine prefix.

The whole prefixed selector is still the sum of those prefixed component
functions, and distinct components remain pointwise disjoint after the common
precomposition.  This gives prefix-stable coefficient, full-alias
cancellation, and weighted high/high transfer identities.  No estimate on
the remaining low boundary or nonconstant weight variation is asserted.
-/

open scoped BigOperators symmDiff

open FiniteBooleanFourier
open FiniteBooleanDisjointProductFourierFactorization
open FiniteBooleanDualAliasConvolutionTransfer
open FiniteBooleanAffineRoundsLocality
open FiniteUnambiguousFBDD

namespace FiniteLayeredQueryProgramFamily

local instance cachedInputMachineStateDecidableEqForPrefixedSelectorFourier
    (machine : DeterministicMachine) [DecidableEq machine.State] :
    DecidableEq (cachedInputMachine machine).State :=
  cachedInputStateDecidableEq machine

/-- One selector component after precomposition by a fixed list of affine
restriction rounds. -/
noncomputable def prefixedMandatoryCanonicalComponentIndicator
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (rounds : List (AffineRestrictionRound n))
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b) :
    (Fin n -> Bool) -> Rat :=
  fun input =>
    let family := mandatoryFiniteRejectingGuardedCanonicalFamily
      machine n T b
    family.ratComponentAcceptanceIndicator index
      (applyAffineRestrictionRounds rounds input)

/-- The block-product Fourier term of one installed component after a common
fixed affine prefix.  The advertised supports are unchanged; only each local
factor is precomposed by the prefix. -/
noncomputable def prefixedMandatoryCanonicalBlockProjectionFourierTerm
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound n))
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b)
    (frequency : Finset (Fin n)) : Rat :=
  let scheduled := builtTimedAlphaVisitSchedule
    (cachedInputMachine machine) index.1
  if frequency ⊆
      (Finset.univ : Finset (Fin (T / b + 1))).biUnion
        (fun block =>
          finiteCachedTimedScheduleBlockQuerySupport n scheduled block)
  then
    ∏ block : Fin (T / b + 1),
      coefficient
        (fun input =>
          finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor
            machine hb index.1 scheduled block
              (applyAffineRestrictionRounds rounds input))
        (frequency ∩
          finiteCachedTimedScheduleBlockQuerySupport n scheduled block)
  else 0

/-- Pointwise block-product factorization of one component after the fixed
affine prefix. -/
theorem prefixedMandatoryCanonicalComponentIndicator_eq_blockProjectionProduct
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound n))
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b)
    (input : Fin n -> Bool) :
    prefixedMandatoryCanonicalComponentIndicator
        machine n T b rounds index input =
      ∏ block : Fin (T / b + 1),
        finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor
          machine hb index.1
            (builtTimedAlphaVisitSchedule
              (cachedInputMachine machine) index.1)
            block (applyAffineRestrictionRounds rounds input) := by
  classical
  simpa [prefixedMandatoryCanonicalComponentIndicator] using
    (mandatoryCanonical_ratComponentAcceptanceIndicator_eq_blockProjectionProduct_fin
      machine n T b hb index (applyAffineRestrictionRounds rounds input))

/-- Every Fourier coefficient of a prefixed component is the product of its
prefixed local block coefficients, with zero outside the unchanged union of
advertised supports. -/
theorem prefixedMandatoryCanonicalComponent_coefficient_eq_blockProjectionTerm
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound n))
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b)
    (frequency : Finset (Fin n)) :
    coefficient
        (prefixedMandatoryCanonicalComponentIndicator
          machine n T b rounds index) frequency =
      prefixedMandatoryCanonicalBlockProjectionFourierTerm
        machine n T b hb rounds index frequency := by
  classical
  let scheduled := builtTimedAlphaVisitSchedule
    (cachedInputMachine machine) index.1
  let support : Fin (T / b + 1) -> Finset (Fin n) := fun block =>
    finiteCachedTimedScheduleBlockQuerySupport n scheduled block
  let factor : Fin (T / b + 1) -> (Fin n -> Bool) -> Rat := fun block input =>
    finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor
      machine hb index.1 scheduled block
        (applyAffineRestrictionRounds rounds input)
  have hfunction :
      prefixedMandatoryCanonicalComponentIndicator
          machine n T b rounds index =
        fun input => ∏ block ∈ (Finset.univ : Finset (Fin (T / b + 1))),
          factor block input := by
    funext input
    simpa [scheduled, factor] using
      (prefixedMandatoryCanonicalComponentIndicator_eq_blockProjectionProduct
        machine n T b hb rounds index input)
  rw [hfunction]
  simpa [prefixedMandatoryCanonicalBlockProjectionFourierTerm, scheduled,
    support, factor] using
    (coefficient_finset_prod_eq_if_subset
      (Finset.univ : Finset (Fin (T / b + 1))) support factor
      (by
        intro block _hblock
        exact dependsOnlyOn_applyAffineRestrictionRounds
          (finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor_dependsOnlyOn
            machine hb index.1 scheduled block)
          rounds)
      (by
        intro left _hleft right _hright hne
        exact finiteCachedTimedScheduleBlockQuerySupport_disjoint_of_ne
          scheduled
            (builtRejectingGuardedCanonicalIndex_chained machine index)
            (builtRejectingGuardedCanonicalIndexMonotone machine index) hne)
      frequency)

/-- Exact Fourier table of the whole prefixed selector: an outer sum over the
same eligible canonical alphas of prefixed block-product coefficient terms. -/
theorem prefixedMandatoryCanonicalSelector_coefficient_eq_sum_blockProjectionTerms
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound n))
    (frequency : Finset (Fin n)) :
    coefficient
        ((mandatoryCanonicalUFBDD machine n T b)
          |>.affinePaddedRestrictByRounds rounds
          |>.ratAcceptanceIndicator)
        frequency =
      ∑ index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
        prefixedMandatoryCanonicalBlockProjectionFourierTerm
          machine n T b hb rounds index frequency := by
  classical
  let family := mandatoryFiniteRejectingGuardedCanonicalFamily machine n T b
  letI : Fintype family.Index := family.indexFintype
  have hfunction :
      ((mandatoryCanonicalUFBDD machine n T b)
        |>.affinePaddedRestrictByRounds rounds
        |>.ratAcceptanceIndicator) =
        fun input => ∑ index : family.Index,
          prefixedMandatoryCanonicalComponentIndicator
            machine n T b rounds index input := by
    funext input
    rw [FiniteUnambiguousFBDD.affinePaddedRestrictByRounds_ratAcceptanceIndicator_eq]
    exact family.selector_ratAcceptanceIndicator_eq_sum_components
      (mandatoryFiniteRejectingGuardedCanonicalFamily_isUnambiguous
        machine n T b hb)
      (applyAffineRestrictionRounds rounds input)
  rw [hfunction]
  rw [coefficient_fintype_sum]
  apply Finset.sum_congr rfl
  intro index _hindex
  exact
    prefixedMandatoryCanonicalComponent_coefficient_eq_blockProjectionTerm
      machine n T b hb rounds index frequency

/-- The diagonal full-alias convolution of a prefixed selector component
returns that component's prefixed Fourier coefficient. -/
theorem prefixedMandatoryCanonical_sameComponent_fullAliasCorrelation_eq_coefficient
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (rounds : List (AffineRestrictionRound n))
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b)
    (dual : Finset (Fin n)) :
    (∑ frequency : Finset (Fin n),
      coefficient
          (prefixedMandatoryCanonicalComponentIndicator
            machine n T b rounds index) frequency *
        coefficient
          (prefixedMandatoryCanonicalComponentIndicator
            machine n T b rounds index) (frequency ∆ dual)) =
      coefficient
        (prefixedMandatoryCanonicalComponentIndicator
          machine n T b rounds index) dual := by
  classical
  apply idempotent_symmDiff_convolution
  intro input
  simp [prefixedMandatoryCanonicalComponentIndicator,
    ratComponentAcceptanceIndicator]

/-- Distinct installed components remain pointwise disjoint after their
common affine precomposition, so their full unweighted alias convolution is
still exactly zero.  Both coefficient tables are displayed in prefixed local
block-product form. -/
theorem prefixedMandatoryCanonical_distinctBlockProjection_fullAliasCorrelation_eq_zero
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound n))
    (left right : BuiltRejectingGuardedCanonicalAlphaIndex machine T b)
    (hne : left ≠ right) (dual : Finset (Fin n)) :
    (∑ frequency : Finset (Fin n),
      prefixedMandatoryCanonicalBlockProjectionFourierTerm
          machine n T b hb rounds left frequency *
        prefixedMandatoryCanonicalBlockProjectionFourierTerm
          machine n T b hb rounds right (frequency ∆ dual)) = 0 := by
  classical
  let family := mandatoryFiniteRejectingGuardedCanonicalFamily machine n T b
  let leftFunction := prefixedMandatoryCanonicalComponentIndicator
    machine n T b rounds left
  let rightFunction := prefixedMandatoryCanonicalComponentIndicator
    machine n T b rounds right
  have hdisjoint : ∀ input, leftFunction input * rightFunction input = 0 := by
    intro input
    have hunambiguous :=
      mandatoryFiniteRejectingGuardedCanonicalFamily_isUnambiguous
        machine n T b hb
    change
      (if (family.program left).eval
          (applyAffineRestrictionRounds rounds input) = true
        then (1 : Rat) else 0) *
        (if (family.program right).eval
          (applyAffineRestrictionRounds rounds input) = true
        then (1 : Rat) else 0) = 0
    by_cases hleft : (family.program left).eval
        (applyAffineRestrictionRounds rounds input) = true
    · have hright : (family.program right).eval
          (applyAffineRestrictionRounds rounds input) ≠ true := by
        intro hright
        exact hne (hunambiguous
          (applyAffineRestrictionRounds rounds input)
          left right hleft hright)
      simp [hleft, hright]
    · simp [hleft]
  have hfull :
      (∑ frequency : Finset (Fin n),
        coefficient leftFunction frequency *
          coefficient rightFunction (frequency ∆ dual)) = 0 :=
    disjoint_symmDiff_convolution_eq_zero
      leftFunction rightFunction hdisjoint dual
  simpa [leftFunction, rightFunction,
    prefixedMandatoryCanonicalComponent_coefficient_eq_blockProjectionTerm
      machine n T b hb rounds left,
    prefixedMandatoryCanonicalComponent_coefficient_eq_blockProjectionTerm
      machine n T b hb rounds right] using hfull

/-- In prefixed block-product coordinates, the diagonal full-alias
convolution is the prefixed block term at the dual support. -/
theorem prefixedMandatoryCanonical_sameBlockProjection_fullAliasCorrelation_eq_term
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound n))
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b)
    (dual : Finset (Fin n)) :
    (∑ frequency : Finset (Fin n),
      prefixedMandatoryCanonicalBlockProjectionFourierTerm
          machine n T b hb rounds index frequency *
        prefixedMandatoryCanonicalBlockProjectionFourierTerm
          machine n T b hb rounds index (frequency ∆ dual)) =
      prefixedMandatoryCanonicalBlockProjectionFourierTerm
        machine n T b hb rounds index dual := by
  classical
  have hfull :=
    prefixedMandatoryCanonical_sameComponent_fullAliasCorrelation_eq_coefficient
      machine n T b rounds index dual
  simp_rw [
    prefixedMandatoryCanonicalComponent_coefficient_eq_blockProjectionTerm
      machine n T b hb rounds index] at hfull
  exact hfull

/-- Summing the prefixed full-alias convolution over every ordered component
pair leaves exactly the diagonal component sum. -/
theorem prefixedMandatoryCanonical_allBlockProjectionPairs_fullAliasCorrelation_eq_diagonalSum
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound n)) (dual : Finset (Fin n)) :
    (∑ left : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
      ∑ right : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
        ∑ frequency : Finset (Fin n),
          prefixedMandatoryCanonicalBlockProjectionFourierTerm
              machine n T b hb rounds left frequency *
            prefixedMandatoryCanonicalBlockProjectionFourierTerm
              machine n T b hb rounds right (frequency ∆ dual)) =
      ∑ index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
        prefixedMandatoryCanonicalBlockProjectionFourierTerm
          machine n T b hb rounds index dual := by
  classical
  apply Finset.sum_congr rfl
  intro left _hleft
  rw [Finset.sum_eq_single left]
  · exact
      prefixedMandatoryCanonical_sameBlockProjection_fullAliasCorrelation_eq_term
        machine n T b hb rounds left dual
  · intro right _hright hright
    exact
      prefixedMandatoryCanonical_distinctBlockProjection_fullAliasCorrelation_eq_zero
        machine n T b hb rounds left right (Ne.symm hright) dual
  · intro hleftMissing
    exact (hleftMissing (Finset.mem_univ left)).elim

/-- The full alias convolution of the prefixed selector acceptance indicator
returns its prefixed Fourier coefficient at the dual support. -/
theorem prefixedMandatoryCanonicalSelector_fullAliasCorrelation_eq_coefficient
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (rounds : List (AffineRestrictionRound n))
    (dual : Finset (Fin n)) :
    let selector := (mandatoryCanonicalUFBDD machine n T b)
      |>.affinePaddedRestrictByRounds rounds
      |>.ratAcceptanceIndicator
    (∑ frequency : Finset (Fin n),
      coefficient selector frequency *
        coefficient selector (frequency ∆ dual)) =
      coefficient selector dual := by
  classical
  dsimp only
  apply idempotent_symmDiff_convolution
  intro input
  simp [FiniteUnambiguousFBDD.ratAcceptanceIndicator]

/-- One fixed-dual alias term for two prefixed block-product component
coefficient tables. -/
noncomputable def prefixedMandatoryCanonicalBlockProjectionAliasTerm
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound n))
    (left right : BuiltRejectingGuardedCanonicalAlphaIndex machine T b)
    (dual frequency : Finset (Fin n)) : Rat :=
  prefixedMandatoryCanonicalBlockProjectionFourierTerm
      machine n T b hb rounds left frequency *
    prefixedMandatoryCanonicalBlockProjectionFourierTerm
      machine n T b hb rounds right (frequency ∆ dual)

/-- Exact weighted high/high transfer for a distinct component pair after an
arbitrary fixed affine prefix.  The identity retains the low-boundary term
together with the explicitly displayed nonconstant variation. -/
theorem prefixedMandatoryCanonical_distinctBlockProjection_weightedHighHighAlias_decomposition
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b)
    (rounds : List (AffineRestrictionRound n))
    (left right : BuiltRejectingGuardedCanonicalAlphaIndex machine T b)
    (hne : left ≠ right) (cutoff : Nat) (dual : Finset (Fin n))
    (weight : Finset (Fin n) -> Rat) (baseWeight : Rat) :
    weightedSelectedSum (highHighAlias cutoff dual) weight
        (prefixedMandatoryCanonicalBlockProjectionAliasTerm
          machine n T b hb rounds left right dual) =
      -baseWeight *
          rejectedSum (highHighAlias cutoff dual)
            (prefixedMandatoryCanonicalBlockProjectionAliasTerm
              machine n T b hb rounds left right dual) +
        selectedWeightVariation (highHighAlias cutoff dual) weight
          (prefixedMandatoryCanonicalBlockProjectionAliasTerm
            machine n T b hb rounds left right dual) baseWeight := by
  apply weightedSelectedSum_eq_neg_base_mul_rejectedSum_add_variation
  simpa [prefixedMandatoryCanonicalBlockProjectionAliasTerm] using
    (prefixedMandatoryCanonical_distinctBlockProjection_fullAliasCorrelation_eq_zero
      machine n T b hb rounds left right hne dual)

end FiniteLayeredQueryProgramFamily

end OneTapeMagnification
end Frontier
end Pnp4
