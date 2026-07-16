import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.TimedAlphaAdjacentCutTensorLayers
import Pnp4.Frontier.OneTapeMagnification.TimedAlphaAdjacentCutSupportDisjointness

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Exact masked correlations inside the timed-alpha tensor layers

For a valid schedule with one accepted replay source, distinct block query
supports are disjoint, as are distinct same-parity adjacent-edge supports.
Combining that semantic fact with local path congruence gives exact
factorization of the fixed-mask uniform correlation inside each of the three
tensor layers.

This is the concrete selector-pair correlation lemma available from path
locality alone.  It deliberately makes no assertion that the product of the
three overlapping layers has a small structured-seed high-tail correlation;
that additional signed/rank estimate is a separate obligation.
-/

open scoped BigOperators

open FiniteBooleanRestrictionMoment
open FiniteBooleanMaskedProductFactorization

/-- The masked uniform mean of the unary block layer is the product of its
local masked means. -/
theorem finiteAverage_unaryTensorLayer_maskedInput_eq_prod
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (source : Fin n → Bool)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hschedule : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha scheduled)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      (cachedInputMachine machine) (List.ofFn source) alpha scheduled)
    (base mask : Fin n → Bool) :
    finiteAverage (fun uniform : Fin n → Bool =>
        finiteCachedTimedScheduleUnaryTensorLayer machine alpha scheduled
          (maskedInput base mask uniform)) =
      ∏ block : Fin (T / b + 1),
        finiteAverage (fun uniform : Fin n → Bool =>
          finiteCachedTimedScheduleBlockReplayRatFactor
            machine alpha scheduled block
              (maskedInput base mask uniform)) := by
  classical
  simpa [finiteCachedTimedScheduleUnaryTensorLayer] using
    (finiteAverage_finset_prod_maskedInput_eq_prod
      (Finset.univ : Finset (Fin (T / b + 1)))
      (fun block =>
        finiteCachedTimedScheduleBlockQuerySupport n scheduled block)
      (fun block =>
        finiteCachedTimedScheduleBlockReplayRatFactor
          machine alpha scheduled block)
      (by
        intro block _hblock
        exact finiteCachedTimedScheduleBlockReplayRatFactor_dependsOnlyOn
          machine alpha scheduled block)
      (by
        intro left _hleft right _hright hne
        exact
          finiteCachedTimedScheduleBlockQuerySupport_disjoint_of_scheduleReplay
            (cachedInputMachine machine) (List.ofFn source) alpha scheduled
              hschedule haccepted hne)
      base mask)

/-- The masked uniform mean of the even selector-pair layer is the product of
its local masked means. -/
theorem finiteAverage_evenSelectorPairTensorLayer_maskedInput_eq_prod
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (source : Fin n → Bool)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hschedule : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha scheduled)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      (cachedInputMachine machine) (List.ofFn source) alpha scheduled)
    (base mask : Fin n → Bool) :
    finiteAverage (fun uniform : Fin n → Bool =>
        finiteCachedTimedScheduleEvenSelectorPairTensorLayer
          machine alpha scheduled (maskedInput base mask uniform)) =
      ∏ bucket ∈ timedScheduleEvenAdjacentBuckets T b,
        finiteAverage (fun uniform : Fin n → Bool =>
          finiteCachedTimedScheduleGuardedAdjacentCutRatFactor
            machine alpha scheduled bucket
              (maskedInput base mask uniform)) := by
  classical
  simpa [finiteCachedTimedScheduleEvenSelectorPairTensorLayer] using
    (finiteAverage_finset_prod_maskedInput_eq_prod
      (timedScheduleEvenAdjacentBuckets T b)
      (fun bucket =>
        finiteCachedTimedScheduleAdjacentCutQuerySupport n scheduled bucket)
      (fun bucket =>
        finiteCachedTimedScheduleGuardedAdjacentCutRatFactor
          machine alpha scheduled bucket)
      (by
        intro bucket _hbucket
        exact
          finiteCachedTimedScheduleGuardedAdjacentCutRatFactor_dependsOnlyOn
            machine alpha scheduled bucket)
      (by
        intro left hleft right hright hne
        have hleftEven : Even left.val :=
          (Finset.mem_filter.mp hleft).2
        have hrightEven : Even right.val :=
          (Finset.mem_filter.mp hright).2
        have hparity : left.val % 2 = right.val % 2 := by
          rw [Nat.even_iff.mp hleftEven, Nat.even_iff.mp hrightEven]
        exact
          finiteCachedTimedScheduleAdjacentCutQuerySupport_disjoint_of_scheduleReplay_sameParity
            (cachedInputMachine machine) (List.ofFn source) alpha scheduled
              hschedule haccepted left right hne hparity)
      base mask)

/-- The masked uniform mean of the odd selector-pair layer is the product of
its local masked means. -/
theorem finiteAverage_oddSelectorPairTensorLayer_maskedInput_eq_prod
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (source : Fin n → Bool)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hschedule : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha scheduled)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      (cachedInputMachine machine) (List.ofFn source) alpha scheduled)
    (base mask : Fin n → Bool) :
    finiteAverage (fun uniform : Fin n → Bool =>
        finiteCachedTimedScheduleOddSelectorPairTensorLayer
          machine alpha scheduled (maskedInput base mask uniform)) =
      ∏ bucket ∈ timedScheduleOddAdjacentBuckets T b,
        finiteAverage (fun uniform : Fin n → Bool =>
          finiteCachedTimedScheduleGuardedAdjacentCutRatFactor
            machine alpha scheduled bucket
              (maskedInput base mask uniform)) := by
  classical
  simpa [finiteCachedTimedScheduleOddSelectorPairTensorLayer] using
    (finiteAverage_finset_prod_maskedInput_eq_prod
      (timedScheduleOddAdjacentBuckets T b)
      (fun bucket =>
        finiteCachedTimedScheduleAdjacentCutQuerySupport n scheduled bucket)
      (fun bucket =>
        finiteCachedTimedScheduleGuardedAdjacentCutRatFactor
          machine alpha scheduled bucket)
      (by
        intro bucket _hbucket
        exact
          finiteCachedTimedScheduleGuardedAdjacentCutRatFactor_dependsOnlyOn
            machine alpha scheduled bucket)
      (by
        intro left hleft right hright hne
        have hleftOdd : Odd left.val :=
          Nat.not_even_iff_odd.mp (Finset.mem_filter.mp hleft).2
        have hrightOdd : Odd right.val :=
          Nat.not_even_iff_odd.mp (Finset.mem_filter.mp hright).2
        have hparity : left.val % 2 = right.val % 2 := by
          rw [Nat.odd_iff.mp hleftOdd, Nat.odd_iff.mp hrightOdd]
        exact
          finiteCachedTimedScheduleAdjacentCutQuerySupport_disjoint_of_scheduleReplay_sameParity
            (cachedInputMachine machine) (List.ofFn source) alpha scheduled
              hschedule haccepted left right hne hparity)
      base mask)

end OneTapeMagnification
end Frontier
end Pnp4
