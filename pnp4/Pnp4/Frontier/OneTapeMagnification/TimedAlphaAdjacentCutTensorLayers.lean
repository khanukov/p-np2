import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.TimedAlphaAdjacentCutFactorization

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Three tensor layers for the timed-alpha nearest-neighbour factor graph

The fixed-alpha component is a path factor graph.  Guarding every edge by its
two endpoint replay indicators makes the edge unconditionally local.  The
graph then splits into three tensor layers: all unary block factors, the even
edges, and the odd edges.  Factors inside one layer have disjoint block
indices; coordinate disjointness is supplied by the separate scheduled-query
support theorem.

This file proves the exact pointwise algebra.  It does not infer a global
small-seed Fourier bound from the three-layer representation.
-/

open scoped BigOperators

local instance cachedInputMachineStateDecidableEqForAdjacentTensorLayers
    (machine : DeterministicMachine) [DecidableEq machine.State] :
    DecidableEq (cachedInputMachine machine).State :=
  cachedInputStateDecidableEq machine

/-- Even adjacent buckets of the path. -/
def timedScheduleEvenAdjacentBuckets (T b : Nat) : Finset (Fin (T / b)) :=
  Finset.univ.filter fun bucket => Even bucket.val

/-- Odd adjacent buckets, represented as the complementary parity class. -/
def timedScheduleOddAdjacentBuckets (T b : Nat) : Finset (Fin (T / b)) :=
  Finset.univ.filter fun bucket => ¬ Even bucket.val

/-- Product of every unary scheduled-block replay factor. -/
noncomputable def finiteCachedTimedScheduleUnaryTensorLayer
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b)) :
    (Fin n → Bool) → Rat :=
  fun input => ∏ block : Fin (T / b + 1),
    finiteCachedTimedScheduleBlockReplayRatFactor
      machine alpha scheduled block input

/-- Product of guarded selector-pair factors on even path edges. -/
noncomputable def finiteCachedTimedScheduleEvenSelectorPairTensorLayer
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b)) :
    (Fin n → Bool) → Rat :=
  fun input => ∏ bucket ∈ timedScheduleEvenAdjacentBuckets T b,
    finiteCachedTimedScheduleGuardedAdjacentCutRatFactor
      machine alpha scheduled bucket input

/-- Product of guarded selector-pair factors on odd path edges. -/
noncomputable def finiteCachedTimedScheduleOddSelectorPairTensorLayer
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b)) :
    (Fin n → Bool) → Rat :=
  fun input => ∏ bucket ∈ timedScheduleOddAdjacentBuckets T b,
    finiteCachedTimedScheduleGuardedAdjacentCutRatFactor
      machine alpha scheduled bucket input

/-- Multiplying by the complete unary layer makes insertion of the two unary
guards at every edge algebraically exact.  This formulation also covers the
empty-edge path without a special case. -/
theorem finiteCachedTimedSchedule_unary_mul_guardedEdges_eq_rawEdges
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (input : Fin n → Bool) :
    (∏ block : Fin (T / b + 1),
        finiteCachedTimedScheduleBlockReplayRatFactor
          machine alpha scheduled block input) *
      (∏ bucket : Fin (T / b),
        finiteCachedTimedScheduleGuardedAdjacentCutRatFactor
          machine alpha scheduled bucket input) =
    (∏ block : Fin (T / b + 1),
        finiteCachedTimedScheduleBlockReplayRatFactor
          machine alpha scheduled block input) *
      (∏ bucket : Fin (T / b),
        finiteCachedTimedScheduleAdjacentCutRatFactor
          machine alpha scheduled bucket input) := by
  classical
  by_cases hall : ∀ block : Fin (T / b + 1),
      TimedScheduleBlockReplayAcceptedFromBlank
        (cachedInputMachine machine) (List.ofFn input) alpha scheduled block
  · simp [finiteCachedTimedScheduleGuardedAdjacentCutRatFactor,
      finiteCachedTimedScheduleBlockReplayRatFactor,
      finiteRatPropIndicator, hall]
  · have hunary :
        (∏ block : Fin (T / b + 1),
          finiteCachedTimedScheduleBlockReplayRatFactor
            machine alpha scheduled block input) = 0 := by
      change
        (∏ block : Fin (T / b + 1), finiteRatPropIndicator
          (TimedScheduleBlockReplayAcceptedFromBlank
            (cachedInputMachine machine) (List.ofFn input) alpha scheduled
              block)) = 0
      rw [← finiteRatPropIndicator_forall_eq_prod]
      simp [finiteRatPropIndicator, hall]
    simp [hunary]

/-- **Exact three-layer selector factorization.**  The cached fixed-alpha
component indicator is a static schedule bit times a unary tensor layer, an
even selector-pair tensor layer, and an odd selector-pair tensor layer. -/
theorem finiteRatPropIndicator_cachedInPlaceCanonicalCutCheck_eq_threeLayers
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n : Nat} (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (input : Fin n → Bool) :
    finiteRatPropIndicator
        (timedAlphaVisitScheduleInPlaceCanonicalCutCheck
          (cachedInputMachine machine) (List.ofFn input) alpha scheduled =
            true) =
      finiteRatPropIndicator
          (TimedAlphaVisitScheduleValid
            (cachedInputMachine machine) alpha scheduled) *
        finiteCachedTimedScheduleUnaryTensorLayer
          machine alpha scheduled input *
        finiteCachedTimedScheduleEvenSelectorPairTensorLayer
          machine alpha scheduled input *
        finiteCachedTimedScheduleOddSelectorPairTensorLayer
          machine alpha scheduled input := by
  classical
  rw [finiteRatPropIndicator_inPlaceCanonicalCutCheck_eq_factorGraph
    (cachedInputMachine machine) (List.ofFn input) T b hb alpha scheduled]
  have hguard :=
    finiteCachedTimedSchedule_unary_mul_guardedEdges_eq_rawEdges
      machine alpha scheduled input
  change
    finiteRatPropIndicator
          (TimedAlphaVisitScheduleValid
            (cachedInputMachine machine) alpha scheduled) *
        (∏ block : Fin (T / b + 1),
          finiteCachedTimedScheduleBlockReplayRatFactor
            machine alpha scheduled block input) *
        (∏ bucket : Fin (T / b),
          finiteCachedTimedScheduleAdjacentCutRatFactor
            machine alpha scheduled bucket input) =
      finiteRatPropIndicator
          (TimedAlphaVisitScheduleValid
            (cachedInputMachine machine) alpha scheduled) *
        (∏ block : Fin (T / b + 1),
          finiteCachedTimedScheduleBlockReplayRatFactor
            machine alpha scheduled block input) *
        (∏ bucket ∈ timedScheduleEvenAdjacentBuckets T b,
          finiteCachedTimedScheduleGuardedAdjacentCutRatFactor
            machine alpha scheduled bucket input) *
        (∏ bucket ∈ timedScheduleOddAdjacentBuckets T b,
          finiteCachedTimedScheduleGuardedAdjacentCutRatFactor
            machine alpha scheduled bucket input)
  have hparity :
      (∏ bucket : Fin (T / b),
        finiteCachedTimedScheduleGuardedAdjacentCutRatFactor
          machine alpha scheduled bucket input) =
      (∏ bucket ∈ timedScheduleEvenAdjacentBuckets T b,
        finiteCachedTimedScheduleGuardedAdjacentCutRatFactor
          machine alpha scheduled bucket input) *
      (∏ bucket ∈ timedScheduleOddAdjacentBuckets T b,
        finiteCachedTimedScheduleGuardedAdjacentCutRatFactor
          machine alpha scheduled bucket input) := by
    exact (Finset.prod_filter_mul_prod_filter_not
      (Finset.univ : Finset (Fin (T / b)))
      (fun bucket => Even bucket.val)
      (fun bucket => finiteCachedTimedScheduleGuardedAdjacentCutRatFactor
        machine alpha scheduled bucket input)).symm
  calc
    _ = finiteRatPropIndicator
          (TimedAlphaVisitScheduleValid
            (cachedInputMachine machine) alpha scheduled) *
        ((∏ block : Fin (T / b + 1),
          finiteCachedTimedScheduleBlockReplayRatFactor
            machine alpha scheduled block input) *
        (∏ bucket : Fin (T / b),
          finiteCachedTimedScheduleAdjacentCutRatFactor
            machine alpha scheduled bucket input)) := by ring
    _ = finiteRatPropIndicator
          (TimedAlphaVisitScheduleValid
            (cachedInputMachine machine) alpha scheduled) *
        ((∏ block : Fin (T / b + 1),
          finiteCachedTimedScheduleBlockReplayRatFactor
            machine alpha scheduled block input) *
        (∏ bucket : Fin (T / b),
          finiteCachedTimedScheduleGuardedAdjacentCutRatFactor
            machine alpha scheduled bucket input)) := by rw [hguard]
    _ = _ := by rw [hparity]; ring

end OneTapeMagnification
end Frontier
end Pnp4
