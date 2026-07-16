import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanDisjointProductFourierFactorization
import Pnp4.Frontier.OneTapeMagnification.TimedAlphaCanonicalFiberMaskedCorrelation
import Pnp4.Frontier.OneTapeMagnification.FiniteRejectingGuardedCanonicalFamily

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Fourier factorization of a fixed timed-alpha canonical fiber

The exact canonical-fiber rectangle is upgraded here from a masked-mean
identity to a coefficient-by-coefficient identity.  Every Fourier frequency
inside the union of the advertised block paths splits uniquely over those
paths; the coefficient is the product of the local block-projection
coefficients.  Frequencies outside that union vanish.

This exposes the fixed-alpha terms that enter the structured selector-pair
kernel.  It does not estimate the remaining signed sum between distinct
alphas.
-/

open scoped BigOperators

open FiniteBooleanFourier
open FiniteBooleanDisjointProductFourierFactorization

local instance cachedInputMachineStateDecidableEqForCanonicalFiberFourier
    (machine : DeterministicMachine) [DecidableEq machine.State] :
    DecidableEq (cachedInputMachine machine).State :=
  cachedInputStateDecidableEq machine

/-- Complete Fourier table of one canonical fiber.  The static hypotheses are
exactly those which make the advertised block-query paths disjoint. -/
theorem coefficient_inPlaceCanonicalCutCheck_eq_if_projectionProduct
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat} (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hchained : TimedAlphaScheduledVisitsChained scheduled)
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled)
    (frequency : Finset (Fin n)) :
    coefficient
        (fun input : Fin n → Bool =>
          finiteRatPropIndicator
            (timedAlphaVisitScheduleInPlaceCanonicalCutCheck
              (cachedInputMachine machine) (List.ofFn input)
                alpha scheduled = true))
        frequency =
      if frequency ⊆
          (Finset.univ : Finset (Fin (T / b + 1))).biUnion
            (fun block =>
              finiteCachedTimedScheduleBlockQuerySupport n scheduled block)
      then
        ∏ block : Fin (T / b + 1),
          coefficient
            (finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor
              machine hb alpha scheduled block)
            (frequency ∩
              finiteCachedTimedScheduleBlockQuerySupport n scheduled block)
      else 0 := by
  classical
  let support : Fin (T / b + 1) → Finset (Fin n) := fun block =>
    finiteCachedTimedScheduleBlockQuerySupport n scheduled block
  let factor : Fin (T / b + 1) → (Fin n → Bool) → Rat := fun block =>
    finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor
      machine hb alpha scheduled block
  have hfunction :
      (fun input : Fin n → Bool =>
        finiteRatPropIndicator
          (timedAlphaVisitScheduleInPlaceCanonicalCutCheck
            (cachedInputMachine machine) (List.ofFn input)
              alpha scheduled = true)) =
        fun input => ∏ block ∈ (Finset.univ : Finset (Fin (T / b + 1))),
          factor block input := by
    funext input
    simpa [factor, finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor]
      using
        (finiteRatPropIndicator_inPlaceCanonicalCutCheck_eq_blockProjectionProduct
          machine hb alpha scheduled input)
  rw [hfunction]
  simpa [support, factor] using
    (coefficient_finset_prod_eq_if_subset
      (Finset.univ : Finset (Fin (T / b + 1))) support factor
      (by
        intro block _hblock
        exact
          finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor_dependsOnlyOn
            machine hb alpha scheduled block)
      (by
        intro left _hleft right _hright hne
        exact finiteCachedTimedScheduleBlockQuerySupport_disjoint_of_ne
          scheduled hchained hmonotone hne)
      frequency)

/-- Installed specialization: eligibility of a mandatory canonical alpha
index supplies schedule chaining and input monotonicity, so the coefficient
factorization has no semantic replay premise. -/
theorem coefficient_builtInPlaceCanonicalCutCheck_eq_if_projectionProduct
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat} (hb : 0 < b)
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b)
    (frequency : Finset (Fin n)) :
    let scheduled := builtTimedAlphaVisitSchedule
      (cachedInputMachine machine) index.1
    coefficient
        (fun input : Fin n → Bool =>
          finiteRatPropIndicator
            (timedAlphaVisitScheduleInPlaceCanonicalCutCheck
              (cachedInputMachine machine) (List.ofFn input)
                index.1 scheduled = true))
        frequency =
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
      else 0 := by
  dsimp only
  let scheduled := builtTimedAlphaVisitSchedule
    (cachedInputMachine machine) index.1
  have hvalid : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) index.1 scheduled :=
    (timedAlphaVisitScheduleCheck_eq_true_iff
      (cachedInputMachine machine) index.1 scheduled).1 index.2.1
  obtain ⟨_hword, _finalCursor, _visitsSoFar, _hfold, _hfinish,
    hchained⟩ := hvalid
  exact coefficient_inPlaceCanonicalCutCheck_eq_if_projectionProduct
    machine hb index.1 scheduled hchained
      (builtRejectingGuardedCanonicalIndexMonotone machine index) frequency

end OneTapeMagnification
end Frontier
end Pnp4
