import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.ExecutableTimedAlphaComponent
import Pnp4.Frontier.OneTapeMagnification.TimedAlphaInputPermutation

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Static query-order extraction from timed alpha

For a fixed alpha the schedule builder and all advertised input endpoints are
input-independent data.  This file turns that observation into an executable
optional query-order builder.  It rejects a malformed schedule or an endpoint
that moves left before any input is queried.

Whenever the canonical component accepts on an input, the static builder
returns a stable grouped order which is a permutation of
`range alpha.terminal.inputHead.val` and is duplicate-free.  Thus the query
order can be hardwired into an individual fixed-alpha program; no actual-run
profile or input value appears in the builder definition.
-/

/-- Finite Boolean check that every advertised visit has monotone input
endpoints. -/
def timedAlphaScheduledVisitsInputMonotoneCheck
    {State : Type} {T b : Nat}
    (visits : List (TimedAlphaScheduledVisit State T b)) : Bool :=
  visits.all fun scheduled =>
    decide (scheduled.visit.entry.inputHead.val ≤
      scheduled.visit.exit.inputHead.val)

/-- Exact reflection of the finite endpoint-monotonicity check. -/
theorem timedAlphaScheduledVisitsInputMonotoneCheck_eq_true_iff
    {State : Type} {T b : Nat}
    (visits : List (TimedAlphaScheduledVisit State T b)) :
    timedAlphaScheduledVisitsInputMonotoneCheck visits = true ↔
      TimedAlphaScheduledVisitsInputMonotone visits := by
  simp only [timedAlphaScheduledVisitsInputMonotoneCheck,
    List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h scheduled hscheduled
    exact h scheduled hscheduled
  · intro h scheduled hscheduled
    exact h scheduled hscheduled

/-- Build the stable grouped query order using only the fixed machine and
alpha.  Input monotonicity is checked before the order is exposed. -/
def buildTimedAlphaStableGroupedQueryOrder?
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b) :
    Option (List Nat) :=
  match buildTimedAlphaVisitSchedule machine alpha with
  | none => none
  | some visits =>
      if hmonotone :
          timedAlphaScheduledVisitsInputMonotoneCheck visits = true then
        some (timedAlphaStableGroupedQueryOrder visits
          ((timedAlphaScheduledVisitsInputMonotoneCheck_eq_true_iff
            visits).1 hmonotone))
      else none

/-- Successful canonical-component validation certifies that the entirely
static builder returns one fixed duplicate-free permutation of the advertised
fresh-input interval. -/
theorem exists_staticTimedAlphaQueryOrder_of_componentCheck
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (hcheck : timedAlphaCanonicalComponentCheck
      machine input T b hb alpha = true) :
    ∃ order : List Nat,
      buildTimedAlphaStableGroupedQueryOrder? machine alpha = some order ∧
        List.Perm order (List.range alpha.terminal.inputHead.val) ∧
        order.Nodup := by
  unfold timedAlphaCanonicalComponentCheck at hcheck
  split at hcheck
  · simp at hcheck
  · rename_i visits hbuild
    have hall : timedAlphaVisitScheduleAllBlockVisitsCheck
        machine input alpha visits = true := by
      have hparts :
          timedAlphaVisitScheduleAllBlockVisitsCheck
                machine input alpha visits = true ∧
            replayedTimedAlphaCutMinimalityCheck
                machine input alpha visits = true := by
        simpa [timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck] using
          hcheck
      exact hparts.1
    have hvalid :=
      (timedAlphaVisitScheduleAllBlockVisitsCheck_eq_true_iff
        machine input alpha visits).1 hall
    have hmonotone : TimedAlphaScheduledVisitsInputMonotone visits :=
      allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
        machine input alpha visits hvalid.2
    have hmonotoneCheck :
        timedAlphaScheduledVisitsInputMonotoneCheck visits = true :=
      (timedAlphaScheduledVisitsInputMonotoneCheck_eq_true_iff visits).2
        hmonotone
    let order := timedAlphaStableGroupedQueryOrder visits hmonotone
    refine ⟨order, ?_, ?_, ?_⟩
    · simp [buildTimedAlphaStableGroupedQueryOrder?, hbuild,
        hmonotoneCheck, order]
    · simpa [order, acceptedTimedAlphaStableGroupedQueryOrder] using
        (acceptedTimedAlphaStableGroupedQueryOrder_perm_range
          machine input alpha visits hvalid.1 hvalid.2)
    · simpa [order, acceptedTimedAlphaStableGroupedQueryOrder] using
        (acceptedTimedAlphaStableGroupedQueryOrder_nodup
          machine input alpha visits hvalid.1 hvalid.2)

/-- A malformed static alpha is rejected by query-order construction without
consulting an input value. -/
theorem buildTimedAlphaStableGroupedQueryOrder?_eq_none_of_schedule_none
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (hbuild : buildTimedAlphaVisitSchedule machine alpha = none) :
    buildTimedAlphaStableGroupedQueryOrder? machine alpha = none := by
  simp [buildTimedAlphaStableGroupedQueryOrder?, hbuild]

/-- Complete the static natural-number order to a permutation of all
length-`n` input variables.  This remains an input-independent computation:
the only data are the fixed machine, alpha, and input length. -/
def buildTimedAlphaFiniteInputQueryOrder?
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b) :
    Option (List (Fin n)) :=
  (buildTimedAlphaStableGroupedQueryOrder? machine alpha).map
    (finiteInputQueryOrderWithDummySuffix n)

/-- Every accepted canonical component therefore exposes one statically
computable, duplicate-free permutation of the entire finite input.  Positions
not reached by the advertised terminal head occur only in the canonical dummy
suffix. -/
theorem exists_staticTimedAlphaFiniteInputQueryOrder_of_componentCheck
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b) (n : Nat)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (hcheck : timedAlphaCanonicalComponentCheck
      machine input T b hb alpha = true) :
    ∃ order : List (Fin n),
      buildTimedAlphaFiniteInputQueryOrder? machine n alpha = some order ∧
        List.Perm order (List.finRange n) ∧ order.Nodup := by
  obtain ⟨rawOrder, hrawOrder, hperm, hnodup⟩ :=
    exists_staticTimedAlphaQueryOrder_of_componentCheck
      machine input T b hb alpha hcheck
  let order := finiteInputQueryOrderWithDummySuffix n rawOrder
  refine ⟨order, ?_, ?_, ?_⟩
  · simp [buildTimedAlphaFiniteInputQueryOrder?, hrawOrder, order]
  · exact finiteInputQueryOrderWithDummySuffix_perm_finRange
      n alpha.terminal.inputHead.val rawOrder hperm
  · exact finiteInputQueryOrderWithDummySuffix_nodup
      n alpha.terminal.inputHead.val rawOrder hperm

/-- Schedule failure is also visible before any input bit is read in the
finite-input builder. -/
theorem buildTimedAlphaFiniteInputQueryOrder?_eq_none_of_schedule_none
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (hbuild : buildTimedAlphaVisitSchedule machine alpha = none) :
    buildTimedAlphaFiniteInputQueryOrder? machine n alpha = none := by
  simp [buildTimedAlphaFiniteInputQueryOrder?,
    buildTimedAlphaStableGroupedQueryOrder?_eq_none_of_schedule_none
      machine alpha hbuild]

end OneTapeMagnification
end Frontier
end Pnp4
