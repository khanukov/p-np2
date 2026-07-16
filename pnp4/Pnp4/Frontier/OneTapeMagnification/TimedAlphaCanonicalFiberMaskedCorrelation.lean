import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.TimedAlphaCanonicalFiberSplicing
import Pnp4.Frontier.OneTapeMagnification.TimedAlphaAdjacentCutSupportDisjointness
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanMaskedProductFactorization

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Exact masked correlation of one fixed-alpha canonical fiber

The canonical fiber is not merely a product of three overlapping tensor
layers.  The block-splicing theorem proves that it is exactly the product of
its existential block projections.  Each projection depends only on one
advertised block path, and the paths of distinct blocks are disjoint under
the static chaining and input-monotonicity conditions of the installed
schedule.

Consequently the complete fixed-alpha canonical indicator, including every
leftmost-cut condition, has an exact fixed-mask uniform correlation formula:
its masked mean is the product of the masked means of the block projections.
No independence, PRG, Fourier-tail, or cut-stability premise is assumed.
-/

open scoped BigOperators

open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteBooleanMaskedProductFactorization

local instance cachedInputMachineStateDecidableEqForCanonicalFiberCorrelation
    (machine : DeterministicMachine) [DecidableEq machine.State] :
    DecidableEq (cachedInputMachine machine).State :=
  cachedInputStateDecidableEq machine

/-- Rational indicator of one canonical block projection. -/
noncomputable def finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat} (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (block : Fin (T / b + 1)) : (Fin n → Bool) → Rat :=
  fun input => finiteRatPropIndicator
    (TimedAlphaCanonicalBlockProjection
      machine hb alpha scheduled block input)

/-- A canonical block projection depends only on that block's advertised
query path.  The canonical witness itself is retained; only its agreement
with the candidate is transported between the two inputs. -/
theorem finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor_dependsOnlyOn
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat} (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (block : Fin (T / b + 1)) :
    DependsOnlyOn
      (finiteCachedTimedScheduleBlockQuerySupport n scheduled block)
      (finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor
        machine hb alpha scheduled block) := by
  intro left right hagree
  have hiff :
      TimedAlphaCanonicalBlockProjection
          machine hb alpha scheduled block left ↔
        TimedAlphaCanonicalBlockProjection
          machine hb alpha scheduled block right := by
    constructor
    · rintro ⟨source, hsource, hsourceLeft⟩
      refine ⟨source, hsource, ?_⟩
      intro coordinate hcoordinate
      calc
        right coordinate = left coordinate := by
          symm
          exact hagree coordinate (by
            simpa [finiteCachedTimedScheduleBlockQuerySupport] using
              hcoordinate)
        _ = source coordinate := hsourceLeft coordinate hcoordinate
    · rintro ⟨source, hsource, hsourceRight⟩
      refine ⟨source, hsource, ?_⟩
      intro coordinate hcoordinate
      calc
        left coordinate = right coordinate :=
          hagree coordinate (by
            simpa [finiteCachedTimedScheduleBlockQuerySupport] using
              hcoordinate)
        _ = source coordinate := hsourceRight coordinate hcoordinate
  unfold finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor
  by_cases hleft : TimedAlphaCanonicalBlockProjection
      machine hb alpha scheduled block left
  · have hright := hiff.1 hleft
    simp [finiteRatPropIndicator, hleft, hright]
  · have hright : ¬ TimedAlphaCanonicalBlockProjection
        machine hb alpha scheduled block right :=
      fun h => hleft (hiff.2 h)
    simp [finiteRatPropIndicator, hleft, hright]

/-- **Whole-component small-seed selector correlation identity.**

For every fixed base and mask, the exact uniform conditional mean of the
complete fixed-alpha canonical indicator factors over the advertised block
paths.  Chaining and input monotonicity are precisely the static hypotheses
needed to make those paths disjoint. -/
theorem finiteAverage_inPlaceCanonicalCutCheck_maskedInput_eq_projectionProd
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat} (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hchained : TimedAlphaScheduledVisitsChained scheduled)
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled)
    (base mask : Fin n → Bool) :
    finiteAverage (fun uniform : Fin n → Bool =>
        finiteRatPropIndicator
          (timedAlphaVisitScheduleInPlaceCanonicalCutCheck
            (cachedInputMachine machine)
            (List.ofFn (maskedInput base mask uniform))
              alpha scheduled = true)) =
      ∏ block : Fin (T / b + 1),
        finiteAverage (fun uniform : Fin n → Bool =>
          finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor
            machine hb alpha scheduled block
              (maskedInput base mask uniform)) := by
  classical
  calc
    finiteAverage (fun uniform : Fin n → Bool =>
        finiteRatPropIndicator
          (timedAlphaVisitScheduleInPlaceCanonicalCutCheck
            (cachedInputMachine machine)
            (List.ofFn (maskedInput base mask uniform))
              alpha scheduled = true)) =
      finiteAverage (fun uniform : Fin n → Bool =>
        ∏ block : Fin (T / b + 1),
          finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor
            machine hb alpha scheduled block
              (maskedInput base mask uniform)) := by
        apply finiteAverage_congr
        intro uniform
        simpa [finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor] using
          (finiteRatPropIndicator_inPlaceCanonicalCutCheck_eq_blockProjectionProduct
            machine hb alpha scheduled (maskedInput base mask uniform))
    _ = ∏ block : Fin (T / b + 1),
        finiteAverage (fun uniform : Fin n → Bool =>
          finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor
            machine hb alpha scheduled block
              (maskedInput base mask uniform)) := by
      simpa using
        (finiteAverage_finset_prod_maskedInput_eq_prod
          (Finset.univ : Finset (Fin (T / b + 1)))
          (fun block =>
            finiteCachedTimedScheduleBlockQuerySupport n scheduled block)
          (fun block =>
            finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor
              machine hb alpha scheduled block)
          (by
            intro block _hblock
            exact
              finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor_dependsOnlyOn
                machine hb alpha scheduled block)
          (by
            intro left _hleft right _hright hne
            exact finiteCachedTimedScheduleBlockQuerySupport_disjoint_of_ne
              scheduled hchained hmonotone hne)
          base mask)

/-- Semantic specialization: a valid schedule and one simultaneous accepted
replay discharge chaining and input monotonicity. -/
theorem finiteAverage_inPlaceCanonicalCutCheck_maskedInput_eq_projectionProd_of_replay
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat} (hb : 0 < b)
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
        finiteRatPropIndicator
          (timedAlphaVisitScheduleInPlaceCanonicalCutCheck
            (cachedInputMachine machine)
            (List.ofFn (maskedInput base mask uniform))
              alpha scheduled = true)) =
      ∏ block : Fin (T / b + 1),
        finiteAverage (fun uniform : Fin n → Bool =>
          finiteCachedTimedAlphaCanonicalBlockProjectionRatFactor
            machine hb alpha scheduled block
              (maskedInput base mask uniform)) := by
  have hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled :=
    allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
      (cachedInputMachine machine) (List.ofFn source) alpha scheduled
        haccepted
  obtain ⟨_hword, _finalCursor, _visitsSoFar, _hfold, _hfinish,
    hchained⟩ := hschedule
  exact
    finiteAverage_inPlaceCanonicalCutCheck_maskedInput_eq_projectionProd
      machine hb alpha scheduled hchained hmonotone base mask

end OneTapeMagnification
end Frontier
end Pnp4
