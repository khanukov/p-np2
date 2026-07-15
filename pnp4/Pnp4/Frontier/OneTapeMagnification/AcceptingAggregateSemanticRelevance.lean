import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.GuardedCanonicalAggregateEndpoint

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Semantic relevance of accepting canonical components

The accepting aggregate is extensionally just the bounded acceptance bit.
Consequently, it cannot by itself remember which canonical route produced an
accepting run.  The individual canonical components retain more information.

This file makes that distinction exact.  After fixing any common input
prefix, distinct accepting timed alphas that are reachable under extensions
of that prefix induce distinct residual component functions.  The premise is
plain accepting reachability, not a circuit lower bound or another hidden
assumption.

A two-state machine then gives a concrete counterarchitecture for the
aggregate: its first transition routes the work head differently on `false`
and `true`, both routes immediately accept, and the accepting aggregate is
the constant-true function.  Thus semantic injectivity survives at the
component level but is destroyed by the existential aggregate.

This is an infrastructure/obstruction result.  It does not reduce
`SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`.
-/

/-! ## Prefix residuals and reachable accepting alphas -/

/-- The residual accepting-component function after fixing an input prefix.
The remaining argument is an arbitrary suffix of the one-way input tape. -/
def timedAlphaInPlaceAcceptingComponentPrefixResidual
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (T b : Nat) (hb : 0 < b) (fixedPrefix : List Bool)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b) :
    List Bool -> Bool :=
  fun suffix => timedAlphaInPlaceAcceptingComponentCheck
    machine (fixedPrefix ++ suffix) T b hb alpha

/-- A timed alpha is accepting-reachable after `prefix` when some suffix
produces exactly that canonical alpha and is accepting at horizon `T`. -/
def AcceptingTimedAlphaReachableAfterPrefix
    (machine : DeterministicMachine) (T b : Nat) (hb : 0 < b)
    (fixedPrefix : List Bool)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b) : Prop :=
  exists suffix : List Bool,
    alpha = chronologicalTimedCanonicalAlpha
      machine (fixedPrefix ++ suffix) T b hb /\
    IsAccepting machine (run machine (fixedPrefix ++ suffix) T)

/-- Accepting reachability is exactly nonemptiness of the corresponding
component residual. -/
theorem acceptingTimedAlphaReachableAfterPrefix_iff_exists_residual_true
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (T b : Nat) (hb : 0 < b) (fixedPrefix : List Bool)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b) :
    AcceptingTimedAlphaReachableAfterPrefix
        machine T b hb fixedPrefix alpha <->
      exists suffix : List Bool,
        timedAlphaInPlaceAcceptingComponentPrefixResidual
          machine T b hb fixedPrefix alpha suffix = true := by
  constructor
  · rintro ⟨suffix, halpha, haccept⟩
    refine ⟨suffix, ?_⟩
    unfold timedAlphaInPlaceAcceptingComponentPrefixResidual
    exact (timedAlphaInPlaceAcceptingComponentCheck_eq_true_iff
      machine (fixedPrefix ++ suffix) T b hb alpha).2 ⟨halpha, haccept⟩
  · rintro ⟨suffix, hresidual⟩
    unfold timedAlphaInPlaceAcceptingComponentPrefixResidual at hresidual
    exact ⟨suffix,
      (timedAlphaInPlaceAcceptingComponentCheck_eq_true_iff
        machine (fixedPrefix ++ suffix) T b hb alpha).1 hresidual⟩

/-- Semantic relevance after a partial prefix assignment: on the accepting
reachable timed alphas, the map from alpha to residual component function is
injective.  A witness suffix for the left alpha separates it from every
distinct right alpha. -/
theorem timedAlphaInPlaceAcceptingComponentPrefixResidual_injectiveOn_reachable
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (T b : Nat) (hb : 0 < b) (fixedPrefix : List Bool) :
    Set.InjOn
      (timedAlphaInPlaceAcceptingComponentPrefixResidual
        machine T b hb fixedPrefix)
      {alpha | AcceptingTimedAlphaReachableAfterPrefix
        machine T b hb fixedPrefix alpha} := by
  intro left hleft right _hright hfunctions
  rcases hleft with ⟨suffix, hleftAlpha, hleftAccept⟩
  have hleftTrue :
      timedAlphaInPlaceAcceptingComponentPrefixResidual
        machine T b hb fixedPrefix left suffix = true := by
    unfold timedAlphaInPlaceAcceptingComponentPrefixResidual
    exact (timedAlphaInPlaceAcceptingComponentCheck_eq_true_iff
      machine (fixedPrefix ++ suffix) T b hb left).2
        ⟨hleftAlpha, hleftAccept⟩
  have hrightTrue :
      timedAlphaInPlaceAcceptingComponentPrefixResidual
        machine T b hb fixedPrefix right suffix = true := by
    rw [← hfunctions]
    exact hleftTrue
  have hrightAlpha :
      right = chronologicalTimedCanonicalAlpha
        machine (fixedPrefix ++ suffix) T b hb := by
    unfold timedAlphaInPlaceAcceptingComponentPrefixResidual at hrightTrue
    exact ((timedAlphaInPlaceAcceptingComponentCheck_eq_true_iff
      machine (fixedPrefix ++ suffix) T b hb right).1 hrightTrue).1
  exact hleftAlpha.trans hrightAlpha.symm

/-- Projecting the terminal endpoint shows that distinct bounded endpoints
force distinct timed canonical alphas. -/
theorem chronologicalTimedCanonicalAlpha_ne_of_terminalEndpoint_ne
    (machine : DeterministicMachine) (left right : List Bool)
    (T b : Nat) (hb : 0 < b)
    (hterminal : boundedTerminalEndpointAtRun machine left T ≠
      boundedTerminalEndpointAtRun machine right T) :
    chronologicalTimedCanonicalAlpha machine left T b hb ≠
      chronologicalTimedCanonicalAlpha machine right T b hb := by
  intro halpha
  apply hterminal
  simpa [chronologicalTimedCanonicalAlpha] using
    congrArg (fun alpha => alpha.terminal) halpha

/-- In particular, a different final work-head coordinate is already a
locally checkable sufficient condition for distinct timed alphas. -/
theorem chronologicalTimedCanonicalAlpha_ne_of_finalWorkHead_ne
    (machine : DeterministicMachine) (left right : List Bool)
    (T b : Nat) (hb : 0 < b)
    (hwork : (run machine left T).workHead ≠
      (run machine right T).workHead) :
    chronologicalTimedCanonicalAlpha machine left T b hb ≠
      chronologicalTimedCanonicalAlpha machine right T b hb := by
  apply chronologicalTimedCanonicalAlpha_ne_of_terminalEndpoint_ne
  intro hterminal
  apply hwork
  simpa using congrArg (fun endpoint => endpoint.workHead.val) hterminal

/-! ## The aggregate residual -/

/-- The corresponding residual of the existential accepting aggregate. -/
def timedAlphaInPlaceAcceptingAggregatePrefixResidual
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (T b : Nat) (hb : 0 < b) (fixedPrefix : List Bool) :
    List Bool -> Bool :=
  fun suffix => timedAlphaInPlaceAcceptingAggregateCheck
    machine (fixedPrefix ++ suffix) T b hb

/-! ## A concrete accepting route-collapse counterarchitecture -/

/-- A two-state accepting machine whose first input symbol controls only the
work-head route.  Reading `true` moves the work head right; reading `false` or
the right endmarker leaves it at zero.  Every first transition enters the same
accepting state. -/
def routeBranchAcceptMachine : DeterministicMachine where
  State := Bool
  stateFintype := inferInstance
  startState := false
  halt := fun state => if state then some .accept else none
  transition := fun _state symbol work =>
    { nextState := true
      write := work
      inputMove := .right
      workMove := match symbol with
        | .bit true => .right
        | .bit false => .stay
        | .rightEnd => .stay }

local instance routeBranchAcceptMachineStateDecidableEq :
    DecidableEq routeBranchAcceptMachine.State := by
  change DecidableEq Bool
  infer_instance

@[simp]
theorem routeBranchAcceptMachine_run_one_state (input : List Bool) :
    (run routeBranchAcceptMachine input 1).state = true := by
  rfl

@[simp]
theorem routeBranchAcceptMachine_run_false_workHead :
    (run routeBranchAcceptMachine [false] 1).workHead = 0 := by
  rfl

@[simp]
theorem routeBranchAcceptMachine_run_true_workHead :
    (run routeBranchAcceptMachine [true] 1).workHead = 1 := by
  rfl

/-- The machine accepts every input after exactly one transition. -/
theorem routeBranchAcceptMachine_accepts_one (input : List Bool) :
    IsAccepting routeBranchAcceptMachine
      (run routeBranchAcceptMachine input 1) := by
  unfold IsAccepting outcome
  change (if (run routeBranchAcceptMachine input 1).state = true then
    some HaltOutcome.accept else none) = some HaltOutcome.accept
  rw [routeBranchAcceptMachine_run_one_state]
  rfl

/-- Hence its accepting aggregate is the constant-true function, including
on the empty input (the right endmarker takes the stay route). -/
theorem routeBranchAcceptMachine_aggregate_one_eq_true (input : List Bool) :
    timedAlphaInPlaceAcceptingAggregateCheck
      routeBranchAcceptMachine input 1 1 (by omega) = true := by
  exact (timedAlphaInPlaceAcceptingAggregateCheck_eq_true_iff
    routeBranchAcceptMachine input 1 1 (by omega)).2
      (routeBranchAcceptMachine_accepts_one input)

private theorem one_pos : 0 < 1 := by omega

/-- Canonical alpha of the stay route. -/
noncomputable def routeBranchFalseAlpha :
    AmbientTimedCanonicalAlpha Bool 1 1 :=
  chronologicalTimedCanonicalAlpha
    routeBranchAcceptMachine [false] 1 1 one_pos

/-- Canonical alpha of the right-moving route. -/
noncomputable def routeBranchTrueAlpha :
    AmbientTimedCanonicalAlpha Bool 1 1 :=
  chronologicalTimedCanonicalAlpha
    routeBranchAcceptMachine [true] 1 1 one_pos

/-- The two accepting routes have different canonical alphas solely because
their final work-head coordinates differ. -/
theorem routeBranchFalseAlpha_ne_routeBranchTrueAlpha :
    routeBranchFalseAlpha ≠ routeBranchTrueAlpha := by
  unfold routeBranchFalseAlpha routeBranchTrueAlpha
  apply chronologicalTimedCanonicalAlpha_ne_of_finalWorkHead_ne
  simp

private theorem routeBranchFalseAlpha_reachable :
    AcceptingTimedAlphaReachableAfterPrefix
      routeBranchAcceptMachine 1 1 one_pos [] routeBranchFalseAlpha := by
  refine ⟨[false], ?_, ?_⟩
  · simp [routeBranchFalseAlpha]
  · simpa using routeBranchAcceptMachine_accepts_one [false]

private theorem routeBranchTrueAlpha_reachable :
    AcceptingTimedAlphaReachableAfterPrefix
      routeBranchAcceptMachine 1 1 one_pos [] routeBranchTrueAlpha := by
  refine ⟨[true], ?_, ?_⟩
  · simp [routeBranchTrueAlpha]
  · simpa using routeBranchAcceptMachine_accepts_one [true]

/-- The individual component residuals still distinguish the two accepting
routes. -/
theorem routeBranch_componentPrefixResiduals_ne :
    timedAlphaInPlaceAcceptingComponentPrefixResidual
        routeBranchAcceptMachine 1 1 one_pos [] routeBranchFalseAlpha ≠
      timedAlphaInPlaceAcceptingComponentPrefixResidual
        routeBranchAcceptMachine 1 1 one_pos [] routeBranchTrueAlpha := by
  intro hfunctions
  apply routeBranchFalseAlpha_ne_routeBranchTrueAlpha
  exact timedAlphaInPlaceAcceptingComponentPrefixResidual_injectiveOn_reachable
    routeBranchAcceptMachine 1 1 one_pos []
      routeBranchFalseAlpha_reachable routeBranchTrueAlpha_reachable hfunctions

/-- By contrast, every prefix residual of the aggregate is constant true. -/
theorem routeBranch_aggregatePrefixResidual_eq_const_true
    (fixedPrefix : List Bool) :
    timedAlphaInPlaceAcceptingAggregatePrefixResidual
        routeBranchAcceptMachine 1 1 one_pos fixedPrefix =
      fun _suffix => true := by
  funext suffix
  exact routeBranchAcceptMachine_aggregate_one_eq_true (fixedPrefix ++ suffix)

/-- Exact counterarchitecture: two accepting canonical routes and their
component residuals are distinct, while the master existential aggregate has
the same constant residual on every partial input prefix. -/
theorem routeBranch_acceptingAggregate_erases_route_semantics :
    routeBranchFalseAlpha ≠ routeBranchTrueAlpha /\
      timedAlphaInPlaceAcceptingComponentPrefixResidual
          routeBranchAcceptMachine 1 1 one_pos [] routeBranchFalseAlpha ≠
        timedAlphaInPlaceAcceptingComponentPrefixResidual
          routeBranchAcceptMachine 1 1 one_pos [] routeBranchTrueAlpha /\
      timedAlphaInPlaceAcceptingAggregatePrefixResidual
          routeBranchAcceptMachine 1 1 one_pos [] =
        fun _suffix => true := by
  exact ⟨routeBranchFalseAlpha_ne_routeBranchTrueAlpha,
    routeBranch_componentPrefixResiduals_ne,
    routeBranch_aggregatePrefixResidual_eq_const_true []⟩

end OneTapeMagnification
end Frontier
end Pnp4
