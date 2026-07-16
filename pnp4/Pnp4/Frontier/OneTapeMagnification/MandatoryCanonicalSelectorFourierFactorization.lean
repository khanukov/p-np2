import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanDualAliasConvolutionTransfer
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorBlockProjectionCorrelation
import Pnp4.Frontier.OneTapeMagnification.TimedAlphaCanonicalFiberFourierFactorization

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Fourier and pair-kernel factorization of the mandatory canonical selector

Each eligible canonical-alpha component is an exact product on disjoint block
paths.  This module inserts that rectangle structure into the Fourier table of
the actual mandatory selector.  It also proves exact cancellation of the full
unweighted alias correlation between two distinct alpha components after
expanding both into block-projection coefficients.

The cancellation is deliberately for the **full** alias sum.  The structured
DPTW target keeps only high/high pairs and gives them rank-dependent mask
weights; those two operations are exactly what prevent the theorem here from
being the final selector-pair bound.
-/

open scoped BigOperators symmDiff

open FiniteBooleanFourier
open FiniteBooleanDisjointProductFourierFactorization
open FiniteBooleanDualAliasConvolutionTransfer
open FiniteUnambiguousFBDD

namespace FiniteLayeredQueryProgramFamily

local instance cachedInputMachineStateDecidableEqForSelectorFourier
    (machine : DeterministicMachine) [DecidableEq machine.State] :
    DecidableEq (cachedInputMachine machine).State :=
  cachedInputStateDecidableEq machine

/-- The explicit block-product Fourier coefficient contributed by one
installed canonical-alpha component. -/
noncomputable def mandatoryCanonicalBlockProjectionFourierTerm
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b)
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
        (finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor
          machine hb index.1 scheduled block)
        (frequency ∩
          finiteCachedTimedScheduleBlockQuerySupport n scheduled block)
  else 0

/-- Arity-stable pointwise form of the selector component rectangle.  This
removes the list-length transport from downstream Fourier statements. -/
theorem mandatoryCanonical_ratComponentAcceptanceIndicator_eq_blockProjectionProduct_fin
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b)
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b)
    (candidate : Fin n → Bool) :
    let family := mandatoryFiniteRejectingGuardedCanonicalFamily machine n T b
    family.ratComponentAcceptanceIndicator index candidate =
      ∏ block : Fin (T / b + 1),
        finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor
          machine hb index.1
            (builtTimedAlphaVisitSchedule
              (cachedInputMachine machine) index.1)
            block candidate := by
  classical
  dsimp only
  let statement : (Σ arity : Nat, Fin arity → Bool) → Prop := fun tuple =>
    let family := mandatoryFiniteRejectingGuardedCanonicalFamily
      machine tuple.1 T b
    family.ratComponentAcceptanceIndicator index tuple.2 =
      ∏ block : Fin (T / b + 1),
        finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor
          machine hb index.1
            (builtTimedAlphaVisitSchedule
              (cachedInputMachine machine) index.1)
            block tuple.2
  have hlist : statement (List.equivSigmaTuple (List.ofFn candidate)) := by
    exact mandatoryCanonical_ratComponentAcceptanceIndicator_eq_blockProjectionProduct
      machine (List.ofFn candidate) T b hb index
  have hsigma : List.equivSigmaTuple (List.ofFn candidate) =
      (⟨n, candidate⟩ : Σ arity : Nat, Fin arity → Bool) :=
    (List.equivSigmaTuple (α := Bool)).apply_symm_apply ⟨n, candidate⟩
  have htuple : statement
      (⟨n, candidate⟩ : Σ arity : Nat, Fin arity → Bool) :=
    hsigma ▸ hlist
  simpa [statement] using htuple

/-- Every coefficient of one installed selector component is exactly its
block-projection Fourier term. -/
theorem mandatoryCanonical_ratComponentAcceptanceIndicator_coefficient_eq_blockProjectionTerm
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b)
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b)
    (frequency : Finset (Fin n)) :
    let family := mandatoryFiniteRejectingGuardedCanonicalFamily machine n T b
    coefficient (family.ratComponentAcceptanceIndicator index) frequency =
      mandatoryCanonicalBlockProjectionFourierTerm
        machine n T b hb index frequency := by
  classical
  dsimp only
  let family := mandatoryFiniteRejectingGuardedCanonicalFamily machine n T b
  let scheduled := builtTimedAlphaVisitSchedule
    (cachedInputMachine machine) index.1
  let support : Fin (T / b + 1) → Finset (Fin n) := fun block =>
    finiteCachedTimedScheduleBlockQuerySupport n scheduled block
  let factor : Fin (T / b + 1) → (Fin n → Bool) → Rat := fun block =>
    finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor
      machine hb index.1 scheduled block
  have hfunction : family.ratComponentAcceptanceIndicator index =
      fun input => ∏ block ∈ (Finset.univ : Finset (Fin (T / b + 1))),
        factor block input := by
    funext input
    simpa [family, scheduled, factor] using
      (mandatoryCanonical_ratComponentAcceptanceIndicator_eq_blockProjectionProduct_fin
        machine n T b hb index input)
  rw [hfunction]
  simpa [mandatoryCanonicalBlockProjectionFourierTerm, scheduled,
    support, factor] using
    (coefficient_finset_prod_eq_if_subset
      (Finset.univ : Finset (Fin (T / b + 1))) support factor
      (by
        intro block _hblock
        exact
          finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor_dependsOnlyOn
            machine hb index.1 scheduled block)
      (by
        intro left _hleft right _hright hne
        exact finiteCachedTimedScheduleBlockQuerySupport_disjoint_of_ne
          scheduled
            (builtRejectingGuardedCanonicalIndex_chained machine index)
            (builtRejectingGuardedCanonicalIndexMonotone machine index) hne)
      frequency)

/-- Exact Fourier table of the whole selector: an outer sum over eligible
alphas of explicit products of local block coefficients. -/
theorem mandatoryCanonicalSelector_coefficient_eq_sum_blockProjectionTerms
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b)
    (frequency : Finset (Fin n)) :
    let family := mandatoryFiniteRejectingGuardedCanonicalFamily machine n T b
    coefficient family.selectorFBDD.ratAcceptanceIndicator frequency =
      ∑ index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
        mandatoryCanonicalBlockProjectionFourierTerm
          machine n T b hb index frequency := by
  classical
  dsimp only
  let family := mandatoryFiniteRejectingGuardedCanonicalFamily machine n T b
  letI : Fintype family.Index := family.indexFintype
  have hfunction : family.selectorFBDD.ratAcceptanceIndicator =
      fun input => ∑ index : family.Index,
        family.ratComponentAcceptanceIndicator index input := by
    funext input
    exact family.selector_ratAcceptanceIndicator_eq_sum_components
      (mandatoryFiniteRejectingGuardedCanonicalFamily_isUnambiguous
        machine n T b hb) input
  rw [hfunction]
  rw [coefficient_fintype_sum]
  apply Finset.sum_congr rfl
  intro index _hindex
  exact
    mandatoryCanonical_ratComponentAcceptanceIndicator_coefficient_eq_blockProjectionTerm
      machine n T b hb index frequency

/-- Exact ordered alpha-pair expansion of a product of two selector Fourier
coefficients.  No triangle inequality or component-count bound is used. -/
theorem mandatoryCanonicalSelector_coefficient_mul_coefficient_eq_sum_pairProjectionTerms
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b)
    (leftFrequency rightFrequency : Finset (Fin n)) :
    let family := mandatoryFiniteRejectingGuardedCanonicalFamily machine n T b
    coefficient family.selectorFBDD.ratAcceptanceIndicator leftFrequency *
        coefficient family.selectorFBDD.ratAcceptanceIndicator rightFrequency =
      ∑ left : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
        ∑ right : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
          mandatoryCanonicalBlockProjectionFourierTerm
              machine n T b hb left leftFrequency *
            mandatoryCanonicalBlockProjectionFourierTerm
              machine n T b hb right rightFrequency := by
  classical
  dsimp only
  rw [mandatoryCanonicalSelector_coefficient_eq_sum_blockProjectionTerms,
    mandatoryCanonicalSelector_coefficient_eq_sum_blockProjectionTerms]
  rw [Finset.sum_mul_sum]

/-- The diagonal selector-component alias convolution returns that component's
Fourier coefficient.  This is the diagonal counterpart to the exact
off-diagonal cancellation below. -/
theorem mandatoryCanonical_sameComponent_fullAliasCorrelation_eq_coefficient
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat)
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b)
    (dual : Finset (Fin n)) :
    let family := mandatoryFiniteRejectingGuardedCanonicalFamily machine n T b
    (∑ frequency : Finset (Fin n),
      coefficient (family.ratComponentAcceptanceIndicator index) frequency *
        coefficient (family.ratComponentAcceptanceIndicator index)
          (frequency ∆ dual)) =
      coefficient (family.ratComponentAcceptanceIndicator index) dual := by
  classical
  dsimp only
  apply idempotent_symmDiff_convolution
  intro input
  simp [ratComponentAcceptanceIndicator]

/-- Distinct selector components have zero full unweighted alias correlation.
This is the exact Fourier image of pointwise unambiguity. -/
theorem mandatoryCanonical_distinctComponents_fullAliasCorrelation_eq_zero
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b)
    (left right : BuiltRejectingGuardedCanonicalAlphaIndex machine T b)
    (hne : left ≠ right) (dual : Finset (Fin n)) :
    let family := mandatoryFiniteRejectingGuardedCanonicalFamily machine n T b
    (∑ frequency : Finset (Fin n),
      coefficient (family.ratComponentAcceptanceIndicator left) frequency *
        coefficient (family.ratComponentAcceptanceIndicator right)
          (frequency ∆ dual)) = 0 := by
  classical
  dsimp only
  let family := mandatoryFiniteRejectingGuardedCanonicalFamily machine n T b
  apply disjoint_symmDiff_convolution_eq_zero
  intro input
  have hunambiguous :=
    mandatoryFiniteRejectingGuardedCanonicalFamily_isUnambiguous
      machine n T b hb
  change
    (if (family.program left).eval input = true then (1 : Rat) else 0) *
      (if (family.program right).eval input = true then (1 : Rat) else 0) = 0
  by_cases hleft : (family.program left).eval input = true
  · have hright : (family.program right).eval input ≠ true := by
      intro hright
      exact hne (hunambiguous input left right hleft hright)
    simp [hleft, hright]
  · simp [hleft]

/-- The same full-alias cancellation after both component coefficients are
expanded into their local block-projection products.  This is the concrete
fixed-alpha selector-pair correlation identity. -/
theorem mandatoryCanonical_distinctBlockProjection_fullAliasCorrelation_eq_zero
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b)
    (left right : BuiltRejectingGuardedCanonicalAlphaIndex machine T b)
    (hne : left ≠ right) (dual : Finset (Fin n)) :
    (∑ frequency : Finset (Fin n),
      mandatoryCanonicalBlockProjectionFourierTerm
          machine n T b hb left frequency *
        mandatoryCanonicalBlockProjectionFourierTerm
          machine n T b hb right (frequency ∆ dual)) = 0 := by
  classical
  have hfull :=
    mandatoryCanonical_distinctComponents_fullAliasCorrelation_eq_zero
      machine n T b hb left right hne dual
  dsimp only at hfull
  simp_rw [
    mandatoryCanonical_ratComponentAcceptanceIndicator_coefficient_eq_blockProjectionTerm
      machine n T b hb left] at hfull
  simp_rw [
    mandatoryCanonical_ratComponentAcceptanceIndicator_coefficient_eq_blockProjectionTerm
      machine n T b hb right] at hfull
  exact hfull

/-- After expanding into local block coefficients, the diagonal full-alias
convolution is exactly the block-projection Fourier term at the dual support. -/
theorem mandatoryCanonical_sameBlockProjection_fullAliasCorrelation_eq_term
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b)
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b)
    (dual : Finset (Fin n)) :
    (∑ frequency : Finset (Fin n),
      mandatoryCanonicalBlockProjectionFourierTerm
          machine n T b hb index frequency *
        mandatoryCanonicalBlockProjectionFourierTerm
          machine n T b hb index (frequency ∆ dual)) =
      mandatoryCanonicalBlockProjectionFourierTerm
        machine n T b hb index dual := by
  classical
  have hfull :=
    mandatoryCanonical_sameComponent_fullAliasCorrelation_eq_coefficient
      machine n T b index dual
  dsimp only at hfull
  simp_rw [
    mandatoryCanonical_ratComponentAcceptanceIndicator_coefficient_eq_blockProjectionTerm
      machine n T b hb index] at hfull
  exact hfull

/-- Summing the full alias convolution over every ordered alpha pair leaves
exactly the diagonal alpha sum: all off-diagonal terms vanish before any
triangle inequality or component-count estimate is introduced. -/
theorem mandatoryCanonical_allBlockProjectionPairs_fullAliasCorrelation_eq_diagonalSum
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b) (dual : Finset (Fin n)) :
    (∑ left : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
      ∑ right : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
        ∑ frequency : Finset (Fin n),
          mandatoryCanonicalBlockProjectionFourierTerm
              machine n T b hb left frequency *
            mandatoryCanonicalBlockProjectionFourierTerm
              machine n T b hb right (frequency ∆ dual)) =
      ∑ index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
        mandatoryCanonicalBlockProjectionFourierTerm
          machine n T b hb index dual := by
  classical
  apply Finset.sum_congr rfl
  intro left _hleft
  rw [Finset.sum_eq_single left]
  · exact mandatoryCanonical_sameBlockProjection_fullAliasCorrelation_eq_term
      machine n T b hb left dual
  · intro right _hright hright
    exact mandatoryCanonical_distinctBlockProjection_fullAliasCorrelation_eq_zero
      machine n T b hb left right (Ne.symm hright) dual
  · intro hleftMissing
    exact (hleftMissing (Finset.mem_univ left)).elim

/-- Expanding both selector coefficients and commuting the three finite sums
turns the selector-wide full alias convolution into the ordered alpha-pair
sum. -/
theorem mandatoryCanonicalSelector_fullAliasCorrelation_eq_allBlockProjectionPairs
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b) (dual : Finset (Fin n)) :
    let family := mandatoryFiniteRejectingGuardedCanonicalFamily machine n T b
    (∑ frequency : Finset (Fin n),
      coefficient family.selectorFBDD.ratAcceptanceIndicator frequency *
        coefficient family.selectorFBDD.ratAcceptanceIndicator
          (frequency ∆ dual)) =
      ∑ left : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
        ∑ right : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
          ∑ frequency : Finset (Fin n),
            mandatoryCanonicalBlockProjectionFourierTerm
                machine n T b hb left frequency *
              mandatoryCanonicalBlockProjectionFourierTerm
                machine n T b hb right (frequency ∆ dual) := by
  classical
  dsimp only
  simp_rw [mandatoryCanonicalSelector_coefficient_eq_sum_blockProjectionTerms
    machine n T b hb]
  calc
    (∑ frequency : Finset (Fin n),
        (∑ left : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
            mandatoryCanonicalBlockProjectionFourierTerm
              machine n T b hb left frequency) *
          (∑ right : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
            mandatoryCanonicalBlockProjectionFourierTerm
              machine n T b hb right (frequency ∆ dual))) =
        ∑ frequency : Finset (Fin n),
          ∑ left : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
            ∑ right : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
              mandatoryCanonicalBlockProjectionFourierTerm
                  machine n T b hb left frequency *
                mandatoryCanonicalBlockProjectionFourierTerm
                  machine n T b hb right (frequency ∆ dual) := by
      apply Finset.sum_congr rfl
      intro frequency _hfrequency
      rw [Finset.sum_mul_sum]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro left _hleft
      rw [Finset.sum_comm]

/-- The selector-wide full alias convolution is precisely its diagonal
block-projection sum.  Thus the preceding pair expansion has no residual
off-diagonal contribution. -/
theorem mandatoryCanonicalSelector_fullAliasCorrelation_eq_diagonalSum
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b) (dual : Finset (Fin n)) :
    let family := mandatoryFiniteRejectingGuardedCanonicalFamily machine n T b
    (∑ frequency : Finset (Fin n),
      coefficient family.selectorFBDD.ratAcceptanceIndicator frequency *
        coefficient family.selectorFBDD.ratAcceptanceIndicator
          (frequency ∆ dual)) =
      ∑ index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
        mandatoryCanonicalBlockProjectionFourierTerm
          machine n T b hb index dual := by
  classical
  dsimp only
  calc
    (∑ frequency : Finset (Fin n),
        coefficient
            (mandatoryFiniteRejectingGuardedCanonicalFamily
              machine n T b).selectorFBDD.ratAcceptanceIndicator frequency *
          coefficient
            (mandatoryFiniteRejectingGuardedCanonicalFamily
              machine n T b).selectorFBDD.ratAcceptanceIndicator
            (frequency ∆ dual)) =
        ∑ left : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
          ∑ right : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
            ∑ frequency : Finset (Fin n),
              mandatoryCanonicalBlockProjectionFourierTerm
                  machine n T b hb left frequency *
                mandatoryCanonicalBlockProjectionFourierTerm
                  machine n T b hb right (frequency ∆ dual) :=
      mandatoryCanonicalSelector_fullAliasCorrelation_eq_allBlockProjectionPairs
        machine n T b hb dual
    _ = _ :=
      mandatoryCanonical_allBlockProjectionPairs_fullAliasCorrelation_eq_diagonalSum
        machine n T b hb dual

/-- Equivalently, the complete selector alias convolution returns the selector
Fourier coefficient at the dual support. -/
theorem mandatoryCanonicalSelector_fullAliasCorrelation_eq_coefficient
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b) (dual : Finset (Fin n)) :
    let family := mandatoryFiniteRejectingGuardedCanonicalFamily machine n T b
    (∑ frequency : Finset (Fin n),
      coefficient family.selectorFBDD.ratAcceptanceIndicator frequency *
        coefficient family.selectorFBDD.ratAcceptanceIndicator
          (frequency ∆ dual)) =
      coefficient family.selectorFBDD.ratAcceptanceIndicator dual := by
  classical
  dsimp only
  calc
    (∑ frequency : Finset (Fin n),
        coefficient
            (mandatoryFiniteRejectingGuardedCanonicalFamily
              machine n T b).selectorFBDD.ratAcceptanceIndicator frequency *
          coefficient
            (mandatoryFiniteRejectingGuardedCanonicalFamily
              machine n T b).selectorFBDD.ratAcceptanceIndicator
            (frequency ∆ dual)) =
        ∑ index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
          mandatoryCanonicalBlockProjectionFourierTerm
            machine n T b hb index dual :=
      mandatoryCanonicalSelector_fullAliasCorrelation_eq_diagonalSum
        machine n T b hb dual
    _ = coefficient
          (mandatoryFiniteRejectingGuardedCanonicalFamily
            machine n T b).selectorFBDD.ratAcceptanceIndicator dual :=
      (mandatoryCanonicalSelector_coefficient_eq_sum_blockProjectionTerms
        machine n T b hb dual).symm

/-- One fixed-dual alias term after both distinct selector components have
been expanded into block-projection Fourier products. -/
noncomputable def mandatoryCanonicalBlockProjectionAliasTerm
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b)
    (left right : BuiltRejectingGuardedCanonicalAlphaIndex machine T b)
    (dual frequency : Finset (Fin n)) : Rat :=
  mandatoryCanonicalBlockProjectionFourierTerm
      machine n T b hb left frequency *
    mandatoryCanonicalBlockProjectionFourierTerm
      machine n T b hb right (frequency ∆ dual)

/-- **Exact weighted high/high transfer for a distinct alpha pair.**

The constant part of any frequency weight cancels against the complementary
low-boundary aliases, while a nonconstant weight-variation term remains.  The
actual DPTW rank-survival weight is a specialization of `weight`; obtaining a
small one-sided bound on the displayed variation remains the quantitative
problem. -/
theorem mandatoryCanonical_distinctBlockProjection_weightedHighHighAlias_decomposition
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b)
    (left right : BuiltRejectingGuardedCanonicalAlphaIndex machine T b)
    (hne : left ≠ right) (cutoff : Nat) (dual : Finset (Fin n))
    (weight : Finset (Fin n) → Rat) (baseWeight : Rat) :
    weightedSelectedSum (highHighAlias cutoff dual) weight
        (mandatoryCanonicalBlockProjectionAliasTerm
          machine n T b hb left right dual) =
      -baseWeight *
          rejectedSum (highHighAlias cutoff dual)
            (mandatoryCanonicalBlockProjectionAliasTerm
              machine n T b hb left right dual) +
        selectedWeightVariation (highHighAlias cutoff dual) weight
          (mandatoryCanonicalBlockProjectionAliasTerm
            machine n T b hb left right dual) baseWeight := by
  apply weightedSelectedSum_eq_neg_base_mul_rejectedSum_add_variation
  simpa [mandatoryCanonicalBlockProjectionAliasTerm] using
    (mandatoryCanonical_distinctBlockProjection_fullAliasCorrelation_eq_zero
      machine n T b hb left right hne dual)

end FiniteLayeredQueryProgramFamily

end OneTapeMagnification
end Frontier
end Pnp4
