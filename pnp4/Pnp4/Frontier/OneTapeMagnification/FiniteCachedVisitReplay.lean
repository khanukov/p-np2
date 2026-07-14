import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FiniteLocalCachedStep
import Pnp4.Frontier.OneTapeMagnification.FixedAlphaBlockVisitReplay

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Finite cached replay of one advertised visit

This module iterates `finiteLocalCachedStep` through all but the last step of
one nonempty visit and uses `finiteLocalCachedFinalStep` for the last step.
The executable runner receives only the next unread symbols, a finite local
state, and finite arithmetic parameters.  In particular, neither a full
`WorkTape` nor a full `Configuration` occurs in its live state.

Intermediate successor heads must remain in the current slab.  The final
successor may leave it and is retained as an absolute bounded endpoint.  A
halted local state is treated as the stuttering transition of `step`, rather
than as a replay failure.
-/

/-- Finite result of replaying a nonempty list of cached-machine steps. -/
inductive FiniteCachedVisitReplayResult (State : Type) (H w : Nat) where
  | completed (state : FiniteLocalFinalState State H w)
  | emptyTrace
  | intermediateWorkHeadExit
  | inputHorizonExceeded
  | finalWorkHorizonExceeded
deriving Fintype

/-- Disjoint-sum presentation of the visit result. -/
def finiteCachedVisitReplayResultEquiv (State : Type) (H w : Nat) :
    FiniteCachedVisitReplayResult State H w ≃
      Sum (FiniteLocalFinalState State H w) (Fin 4) where
  toFun
    | .completed state => .inl state
    | .emptyTrace => .inr 0
    | .intermediateWorkHeadExit => .inr 1
    | .inputHorizonExceeded => .inr 2
    | .finalWorkHorizonExceeded => .inr 3
  invFun
    | .inl state => .completed state
    | .inr tag =>
        Fin.cases .emptyTrace (fun tag =>
          Fin.cases .intermediateWorkHeadExit (fun tag =>
            Fin.cases .inputHorizonExceeded
              (fun _ => .finalWorkHorizonExceeded) tag) tag) tag
  left_inv result := by cases result <;> rfl
  right_inv result := by
    rcases result with state | tag
    · rfl
    · fin_cases tag <;> rfl

/-- Exact cardinality of the finite visit-result carrier. -/
theorem card_finiteCachedVisitReplayResult
    (State : Type) [Fintype State] (H w : Nat) :
    Fintype.card (FiniteCachedVisitReplayResult State H w) =
      Fintype.card State * (H + 1) * (H + 1) * 2 ^ w + 4 := by
  rw [Fintype.card_congr (finiteCachedVisitReplayResultEquiv State H w)]
  rw [Fintype.card_sum, card_finiteLocalFinalState]
  simp

/-- Regard an inside-slab local state as a retained absolute endpoint.  The
slab bound guarantees that every relative head denotes an absolute position
inside the declared horizon. -/
def finiteLocalFinalStateOfReplayState
    {State : Type} {H w : Nat} (base : Nat)
    (hbound : base + w ≤ H + 1)
    (state : LocalReplayState State H w) :
    FiniteLocalFinalState State H w where
  control := state.control
  inputHead := state.inputHead
  workHead := ⟨base + state.relativeWorkHead.val, by
    have hrel := state.relativeWorkHead.isLt
    omega⟩
  workSlab := state.workSlab

@[simp]
theorem materialize_finalStateOfReplayState
    {State : Type} {H w base : Nat}
    (hbound : base + w ≤ H + 1)
    (state : LocalReplayState State H w) :
    materializeFiniteLocalFinalState base
        (finiteLocalFinalStateOfReplayState base hbound state) =
      materializeLocalReplayState base state := by
  rfl

/-- Replay a finite list of explicitly supplied unread symbols.  The list is
read chronologically.  Its last symbol is processed with the endpoint-
retaining final-step API; hence a permitted final work-head exit is not lost.
-/
def finiteCachedVisitReplay
    (machine : DeterministicMachine) (H w base : Nat)
    (hbound : base + w ≤ H + 1) :
    List ReadOnlySymbol →
      LocalReplayState (cachedInputMachine machine).State H w →
      FiniteCachedVisitReplayResult
        (cachedInputMachine machine).State H w
  | [], _ => .emptyTrace
  | [unread], state =>
      match finiteLocalCachedFinalStep machine H w base unread state with
      | .stepped next => .completed next
      | .halted _ =>
          .completed (finiteLocalFinalStateOfReplayState base hbound state)
      | .inputHorizonExceeded => .inputHorizonExceeded
      | .workHorizonExceeded => .finalWorkHorizonExceeded
  | unread :: nextUnread :: rest, state =>
      match finiteLocalCachedStep machine H w base unread state with
      | .inside next =>
          finiteCachedVisitReplay machine H w base hbound
            (nextUnread :: rest) next
      | .halted _ =>
          finiteCachedVisitReplay machine H w base hbound
            (nextUnread :: rest) state
      | .workHeadExit => .intermediateWorkHeadExit
      | .inputHorizonExceeded => .inputHorizonExceeded

/-- One-step unfolding equation for a trace with at least two symbols. -/
theorem finiteCachedVisitReplay_cons_cons
    (machine : DeterministicMachine) (H w base : Nat)
    (hbound : base + w ≤ H + 1)
    (unread nextUnread : ReadOnlySymbol) (rest : List ReadOnlySymbol)
    (state : LocalReplayState (cachedInputMachine machine).State H w) :
    finiteCachedVisitReplay machine H w base hbound
        (unread :: nextUnread :: rest) state =
      match finiteLocalCachedStep machine H w base unread state with
      | .inside next => finiteCachedVisitReplay machine H w base hbound
          (nextUnread :: rest) next
      | .halted _ => finiteCachedVisitReplay machine H w base hbound
          (nextUnread :: rest) state
      | .workHeadExit => .intermediateWorkHeadExit
      | .inputHorizonExceeded => .inputHorizonExceeded := by
  rfl

/-- Exact result size after specializing the control to the cached machine. -/
theorem card_cachedFiniteVisitReplayResult
    (machine : DeterministicMachine) (H w : Nat) :
    letI := (cachedInputMachine machine).stateFintype
    Fintype.card
        (FiniteCachedVisitReplayResult
          (cachedInputMachine machine).State H w) =
      (1 + 3 * @Fintype.card machine.State machine.stateFintype) *
          (H + 1) * (H + 1) * 2 ^ w + 4 := by
  letI := (cachedInputMachine machine).stateFintype
  rw [card_finiteCachedVisitReplayResult]
  rw [cachedInputMachine_state_card]

/-- Exact live-state size of the finite cached visit replay. -/
theorem card_cachedFiniteVisitReplayState
    (machine : DeterministicMachine) (H w : Nat) :
    letI := (cachedInputMachine machine).stateFintype
    Fintype.card
        (LocalReplayState (cachedInputMachine machine).State H w) =
      (1 + 3 * @Fintype.card machine.State machine.stateFintype) *
        (H + 1) * w * 2 ^ w := by
  letI := (cachedInputMachine machine).stateFintype
  rw [card_localReplayState]
  rw [cachedInputMachine_state_card]

/-- A halted result from the ordinary local API is equivalent to the cached
control itself being halted with that outcome. -/
theorem finiteLocalCachedStep_eq_halted_iff
    (machine : DeterministicMachine) {H w base : Nat}
    (unread : ReadOnlySymbol)
    (state : LocalReplayState (cachedInputMachine machine).State H w)
    (halted : HaltOutcome) :
    finiteLocalCachedStep machine H w base unread state = .halted halted ↔
      (cachedInputMachine machine).halt state.control = some halted := by
  constructor
  · intro hresult
    unfold finiteLocalCachedStep at hresult
    split at hresult
    · rename_i hhalt
      cases hresult
      exact hhalt
    · dsimp only at hresult
      split at hresult
      · split at hresult <;> contradiction
      · contradiction
  · intro hhalt
    unfold finiteLocalCachedStep
    rw [hhalt]

/-- The endpoint-retaining API has the same exact halted characterization. -/
theorem finiteLocalCachedFinalStep_eq_halted_iff
    (machine : DeterministicMachine) {H w base : Nat}
    (unread : ReadOnlySymbol)
    (state : LocalReplayState (cachedInputMachine machine).State H w)
    (halted : HaltOutcome) :
    finiteLocalCachedFinalStep machine H w base unread state =
        .halted halted ↔
      (cachedInputMachine machine).halt state.control = some halted := by
  constructor
  · intro hresult
    unfold finiteLocalCachedFinalStep at hresult
    split at hresult
    · rename_i hhalt
      cases hresult
      exact hhalt
    · dsimp only at hresult
      split at hresult
      · split at hresult <;> contradiction
      · contradiction
  · intro hhalt
    unfold finiteLocalCachedFinalStep
    rw [hhalt]

/-- A halted deterministic configuration stutters for every remaining step. -/
theorem runFrom_eq_self_of_halted
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration machine.State) (halted : HaltOutcome)
    (hhalt : machine.halt config.state = some halted) (steps : Nat) :
    runFrom machine input config steps = config := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
      rw [runFrom_succ, step_of_halted machine input config halted hhalt, ih]

/-- Every materialized local state scans a cell in its represented slab. -/
theorem materializeLocalReplayState_workHead_in_slab
    {State : Type} {H w base : Nat}
    (state : LocalReplayState State H w) :
    WorkCellInSlab base w
      (materializeLocalReplayState base state).workHead := by
  constructor <;> simp only [materializeLocalReplayState]
  · omega
  · exact Nat.add_lt_add_left state.relativeWorkHead.isLt base

/-- Chronological unread symbols of a concrete cached-machine segment.  This
is used only to state completeness against the old semantics; the finite
runner itself accepts an explicit list and never stores the input. -/
def cachedRunUnreadSymbols
    (machine : DeterministicMachine) (input : List Bool) :
    Configuration (cachedInputMachine machine).State → Nat →
      List ReadOnlySymbol
  | _, 0 => []
  | config, steps + 1 =>
      readOnlySymbol input config.inputHead ::
        cachedRunUnreadSymbols machine input
          (step (cachedInputMachine machine) input config) steps

@[simp]
theorem cachedRunUnreadSymbols_length
    (machine : DeterministicMachine) (input : List Bool)
    (config : Configuration (cachedInputMachine machine).State)
    (steps : Nat) :
    (cachedRunUnreadSymbols machine input config steps).length = steps := by
  induction steps generalizing config with
  | zero => rfl
  | succ steps ih =>
      simp [cachedRunUnreadSymbols, ih]

/-- At a nonhalting materialized local state, the global cached-machine step
uses exactly the local transition on the current slab symbol. -/
theorem step_cached_materialized_eq_applyInstruction
    (machine : DeterministicMachine) (input : List Bool)
    {H w base : Nat}
    (state : LocalReplayState (cachedInputMachine machine).State H w)
    (hnonhalting : (cachedInputMachine machine).halt state.control = none) :
    step (cachedInputMachine machine) input
        (materializeLocalReplayState base state) =
      applyInstruction (materializeLocalReplayState base state)
        (cachedInputTransition machine state.control
          (readOnlySymbol input state.inputHead.val)
          (state.workSlab state.relativeWorkHead)) := by
  unfold step
  change
    (match (cachedInputMachine machine).halt state.control with
    | some _ => materializeLocalReplayState base state
    | none =>
        applyInstruction (materializeLocalReplayState base state)
          ((cachedInputMachine machine).transition state.control
            (readOnlySymbol input state.inputHead.val)
            (WorkTape.read
              (materializeLocalReplayState base state).workTape
              (materializeLocalReplayState base state).workHead))) = _
  rw [hnonhalting]
  change applyInstruction (materializeLocalReplayState base state)
      (cachedInputTransition machine state.control
        (readOnlySymbol input state.inputHead.val)
        (WorkTape.read (materializeLocalReplayState base state).workTape
          (materializeLocalReplayState base state).workHead)) = _
  rw [materializeLocalReplayState_work_read]

/-- Exact symbol-agreement condition for an input-free finite replay.

At every live finite state, the explicitly supplied symbol must equal the
symbol of the external immutable input at that state's bounded input head.
The definition follows the finite transition itself and therefore stores no
input, work tape, or global configuration in the replay state.  A local
failure makes a non-final trace incompatible.
-/
def FiniteCachedVisitSymbolsAgree
    (machine : DeterministicMachine) (input : List Bool)
    (H w base : Nat) :
    List ReadOnlySymbol →
      LocalReplayState (cachedInputMachine machine).State H w → Prop
  | [], _ => False
  | [unread], state =>
      readOnlySymbol input state.inputHead.val = unread
  | unread :: nextUnread :: rest, state =>
      readOnlySymbol input state.inputHead.val = unread ∧
        match finiteLocalCachedStep machine H w base unread state with
        | .inside next =>
            FiniteCachedVisitSymbolsAgree machine input H w base
              (nextUnread :: rest) next
        | .halted _ =>
            FiniteCachedVisitSymbolsAgree machine input H w base
              (nextUnread :: rest) state
        | .workHeadExit => False
        | .inputHorizonExceeded => False

/-- One-step unfolding equation for symbol agreement on a non-final step. -/
theorem finiteCachedVisitSymbolsAgree_cons_cons
    (machine : DeterministicMachine) (input : List Bool)
    (H w base : Nat) (unread nextUnread : ReadOnlySymbol)
    (rest : List ReadOnlySymbol)
    (state : LocalReplayState (cachedInputMachine machine).State H w) :
    FiniteCachedVisitSymbolsAgree machine input H w base
        (unread :: nextUnread :: rest) state ↔
      readOnlySymbol input state.inputHead.val = unread ∧
        match finiteLocalCachedStep machine H w base unread state with
        | .inside next => FiniteCachedVisitSymbolsAgree machine input H w base
            (nextUnread :: rest) next
        | .halted _ => FiniteCachedVisitSymbolsAgree machine input H w base
            (nextUnread :: rest) state
        | .workHeadExit => False
        | .inputHorizonExceeded => False := by
  rfl

/-- Exact materialized semantics of the finite runner.

If every supplied unread symbol agrees with the external input and the finite
runner completes, then its retained endpoint materializes to the ordinary
cached-machine run.  Simultaneously, every pre-transition global work head is
proved to lie in the slab.  The last successor head is deliberately absent
from the membership conclusion and may have left the slab.
-/
theorem finiteCachedVisitReplay_completed_sound
    (machine : DeterministicMachine) (input : List Bool)
    {H w base : Nat} (hbound : base + w ≤ H + 1)
    (unreads : List ReadOnlySymbol)
    (state : LocalReplayState (cachedInputMachine machine).State H w)
    (final : FiniteLocalFinalState
      (cachedInputMachine machine).State H w)
    (hagree : FiniteCachedVisitSymbolsAgree
      machine input H w base unreads state)
    (hreplay : finiteCachedVisitReplay machine H w base hbound
        unreads state = .completed final) :
    materializeFiniteLocalFinalState base final =
        runFrom (cachedInputMachine machine) input
          (materializeLocalReplayState base state) unreads.length ∧
      ∀ time : Fin unreads.length,
        WorkCellInSlab base w
          (runFrom (cachedInputMachine machine) input
            (materializeLocalReplayState base state) time.val).workHead := by
  induction unreads generalizing state final with
  | nil => simp [FiniteCachedVisitSymbolsAgree] at hagree
  | cons unread unreads ih =>
      cases unreads with
      | nil =>
          simp only [FiniteCachedVisitSymbolsAgree] at hagree
          simp only [finiteCachedVisitReplay] at hreplay
          cases hstep : finiteLocalCachedFinalStep machine H w base unread state with
          | stepped _ =>
              rw [hstep] at hreplay
              cases hreplay
              constructor
              · simpa only [List.length_cons, List.length_nil,
                    Nat.zero_add, runFrom_succ, runFrom_zero] using
                  finiteLocalCachedFinalStep_stepped_materialize
                    machine unread state _ input hagree hstep
              · intro time
                have hzero : time.val = 0 := by
                  have htime := time.isLt
                  simp only [List.length_cons, List.length_nil,
                    Nat.zero_add] at htime
                  omega
                simpa [hzero] using
                  materializeLocalReplayState_workHead_in_slab state
          | halted outcome =>
              rw [hstep] at hreplay
              cases hreplay
              have hhalt :=
                (finiteLocalCachedFinalStep_eq_halted_iff
                  machine unread state outcome).mp hstep
              have hhaltMaterialized :
                  (cachedInputMachine machine).halt
                      (materializeLocalReplayState base state).state =
                    some outcome := by
                simpa [materializeLocalReplayState] using hhalt
              constructor
              · rw [materialize_finalStateOfReplayState]
                simpa only [List.length_cons, List.length_nil,
                    Nat.zero_add, runFrom_succ, runFrom_zero] using
                  (step_of_halted (cachedInputMachine machine) input
                    (materializeLocalReplayState base state) outcome
                    hhaltMaterialized).symm
              · intro time
                have hzero : time.val = 0 := by
                  have htime := time.isLt
                  simp only [List.length_cons, List.length_nil,
                    Nat.zero_add] at htime
                  omega
                simpa [hzero] using
                  materializeLocalReplayState_workHead_in_slab state
          | inputHorizonExceeded => simp [hstep] at hreplay
          | workHorizonExceeded => simp [hstep] at hreplay
      | cons nextUnread rest =>
          simp only [FiniteCachedVisitSymbolsAgree] at hagree
          rcases hagree with ⟨hread, htailAgree⟩
          simp only [finiteCachedVisitReplay] at hreplay
          cases hstep : finiteLocalCachedStep machine H w base unread state with
          | inside next =>
              rw [hstep] at htailAgree hreplay
              have hmaterialize := finiteLocalCachedStep_inside_materialize
                machine unread state next input hread hstep
              have htail := ih next final htailAgree hreplay
              constructor
              · rw [List.length_cons, runFrom_succ, ← hmaterialize]
                exact htail.1
              · intro time
                refine Fin.cases ?_ (fun remaining => ?_) time
                · simpa using
                    materializeLocalReplayState_workHead_in_slab state
                · simpa only [Fin.succ, Nat.succ_eq_add_one,
                    runFrom_succ, ← hmaterialize] using htail.2 remaining
          | halted outcome =>
              rw [hstep] at htailAgree hreplay
              have hhalt :=
                (finiteLocalCachedStep_eq_halted_iff
                  machine unread state outcome).mp hstep
              have hhaltMaterialized :
                  (cachedInputMachine machine).halt
                      (materializeLocalReplayState base state).state =
                    some outcome := by
                simpa [materializeLocalReplayState] using hhalt
              have hstutter := step_of_halted
                (cachedInputMachine machine) input
                (materializeLocalReplayState base state) outcome
                hhaltMaterialized
              have htail := ih state final htailAgree hreplay
              constructor
              · rw [List.length_cons, runFrom_succ, hstutter]
                exact htail.1
              · intro time
                refine Fin.cases ?_ (fun remaining => ?_) time
                · simpa using
                    materializeLocalReplayState_workHead_in_slab state
                · simpa only [Fin.succ, Nat.succ_eq_add_one,
                    runFrom_succ, hstutter] using htail.2 remaining
          | workHeadExit => simp [hstep] at htailAgree
          | inputHorizonExceeded => simp [hstep] at htailAgree

/-- Completeness of the finite runner under the exact semantic bounds it
needs.  All pre-transition work heads must lie in the slab, while only the
final successor work head must fit the absolute horizon.  Monotonicity of the
one-way input head makes a final input-head bound sufficient for every local
step.

The witness symbol list is the chronological list of symbols actually seen
by the cached run.  The theorem returns a finite endpoint, exact executable
completion, exact materialized equality, and the symbol-agreement certificate
used by the soundness theorem.
-/
theorem finiteCachedVisitReplay_complete_of_semantic_bounds
    (machine : DeterministicMachine) (input : List Bool)
    {H w base : Nat} (hbound : base + w ≤ H + 1)
    (state : LocalReplayState (cachedInputMachine machine).State H w)
    (steps : Nat) (hsteps : 0 < steps)
    (hinside : ∀ time, time < steps →
      WorkCellInSlab base w
        (runFrom (cachedInputMachine machine) input
          (materializeLocalReplayState base state) time).workHead)
    (hfinalInput :
      (runFrom (cachedInputMachine machine) input
        (materializeLocalReplayState base state) steps).inputHead < H + 1)
    (hfinalWork :
      (runFrom (cachedInputMachine machine) input
        (materializeLocalReplayState base state) steps).workHead < H + 1) :
    ∃ final : FiniteLocalFinalState
        (cachedInputMachine machine).State H w,
      finiteCachedVisitReplay machine H w base hbound
          (cachedRunUnreadSymbols machine input
            (materializeLocalReplayState base state) steps) state =
        .completed final ∧
      materializeFiniteLocalFinalState base final =
        runFrom (cachedInputMachine machine) input
          (materializeLocalReplayState base state) steps ∧
      FiniteCachedVisitSymbolsAgree machine input H w base
        (cachedRunUnreadSymbols machine input
          (materializeLocalReplayState base state) steps) state := by
  induction steps generalizing state with
  | zero => omega
  | succ steps ih =>
      cases steps with
      | zero =>
          let unread := readOnlySymbol input state.inputHead.val
          cases hhalt : (cachedInputMachine machine).halt state.control with
          | some outcome =>
              let final := finiteLocalFinalStateOfReplayState
                base hbound state
              have hlocal : finiteLocalCachedFinalStep machine H w base
                  unread state = .halted outcome :=
                (finiteLocalCachedFinalStep_eq_halted_iff
                  machine unread state outcome).2 hhalt
              have hhaltMaterialized :
                  (cachedInputMachine machine).halt
                      (materializeLocalReplayState base state).state =
                    some outcome := by
                simpa [materializeLocalReplayState] using hhalt
              refine ⟨final, ?_, ?_, ?_⟩
              · simp [cachedRunUnreadSymbols, finiteCachedVisitReplay,
                  materializeLocalReplayState, hlocal, unread, final]
              · rw [materialize_finalStateOfReplayState]
                simpa only [runFrom_succ, runFrom_zero] using
                  (step_of_halted (cachedInputMachine machine) input
                    (materializeLocalReplayState base state) outcome
                    hhaltMaterialized).symm
              · simp [cachedRunUnreadSymbols,
                  FiniteCachedVisitSymbolsAgree,
                  materializeLocalReplayState]
          | none =>
              let unread := readOnlySymbol input state.inputHead.val
              let instruction := cachedInputTransition machine state.control
                unread (state.workSlab state.relativeWorkHead)
              have hglobal := step_cached_materialized_eq_applyInstruction
                machine input (base := base) state hhalt
              have hinput :
                  moveInputHead state.inputHead.val instruction.inputMove <
                    H + 1 := by
                have hfinalInput' := hfinalInput
                simp only [runFrom_succ, runFrom_zero] at hfinalInput'
                rw [hglobal] at hfinalInput'
                simpa [applyInstruction, materializeLocalReplayState,
                  instruction, unread] using hfinalInput'
              have hwork :
                  moveWorkHead (base + state.relativeWorkHead.val)
                      instruction.workMove < H + 1 := by
                have hfinalWork' := hfinalWork
                simp only [runFrom_succ, runFrom_zero] at hfinalWork'
                rw [hglobal] at hfinalWork'
                simpa [applyInstruction, materializeLocalReplayState,
                  instruction, unread] using hfinalWork'
              let final : FiniteLocalFinalState
                  (cachedInputMachine machine).State H w :=
                { control := instruction.nextState
                  inputHead := ⟨moveInputHead state.inputHead.val
                    instruction.inputMove, hinput⟩
                  workHead := ⟨moveWorkHead
                    (base + state.relativeWorkHead.val)
                    instruction.workMove, hwork⟩
                  workSlab := writeWorkSlab state.workSlab
                    state.relativeWorkHead instruction.write }
              have hlocal : finiteLocalCachedFinalStep machine H w base
                  unread state = .stepped final := by
                unfold finiteLocalCachedFinalStep
                rw [hhalt]
                dsimp only
                rw [dif_pos hinput, dif_pos hwork]
              refine ⟨final, ?_, ?_, ?_⟩
              · simp [cachedRunUnreadSymbols, finiteCachedVisitReplay,
                  materializeLocalReplayState, hlocal, unread]
              · simpa only [runFrom_succ, runFrom_zero] using
                  finiteLocalCachedFinalStep_stepped_materialize
                    machine unread state final input rfl hlocal
              · simp [cachedRunUnreadSymbols,
                  FiniteCachedVisitSymbolsAgree,
                  materializeLocalReplayState]
      | succ remaining =>
          let unread := readOnlySymbol input state.inputHead.val
          cases hhalt : (cachedInputMachine machine).halt state.control with
          | some outcome =>
              have hlocal : finiteLocalCachedStep machine H w base unread
                  state = .halted outcome :=
                (finiteLocalCachedStep_eq_halted_iff
                  machine unread state outcome).2 hhalt
              have hhaltMaterialized :
                  (cachedInputMachine machine).halt
                      (materializeLocalReplayState base state).state =
                    some outcome := by
                simpa [materializeLocalReplayState] using hhalt
              have hstutter := step_of_halted
                (cachedInputMachine machine) input
                (materializeLocalReplayState base state) outcome
                hhaltMaterialized
              have hinsideTail : ∀ time, time < remaining + 1 →
                  WorkCellInSlab base w
                    (runFrom (cachedInputMachine machine) input
                      (materializeLocalReplayState base state) time).workHead := by
                intro time htime
                exact hinside time (by omega)
              have hfinalInputTail :
                  (runFrom (cachedInputMachine machine) input
                    (materializeLocalReplayState base state)
                    (remaining + 1)).inputHead < H + 1 := by
                simpa only [runFrom_succ, hstutter] using hfinalInput
              have hfinalWorkTail :
                  (runFrom (cachedInputMachine machine) input
                    (materializeLocalReplayState base state)
                    (remaining + 1)).workHead < H + 1 := by
                simpa only [runFrom_succ, hstutter] using hfinalWork
              obtain ⟨final, htailReplay, htailMaterialize, htailAgree⟩ :=
                ih state (by omega) hinsideTail hfinalInputTail hfinalWorkTail
              refine ⟨final, ?_, ?_, ?_⟩
              · rw [cachedRunUnreadSymbols, hstutter]
                rw [cachedRunUnreadSymbols, hstutter]
                simp only [materializeLocalReplayState]
                rw [finiteCachedVisitReplay_cons_cons, hlocal]
                simpa only [cachedRunUnreadSymbols, hstutter] using htailReplay
              · calc
                  materializeFiniteLocalFinalState base final =
                      runFrom (cachedInputMachine machine) input
                        (materializeLocalReplayState base state)
                        (remaining + 1) := htailMaterialize
                  _ = runFrom (cachedInputMachine machine) input
                        (materializeLocalReplayState base state)
                        (remaining + 1 + 1) := by
                      rw [runFrom_eq_self_of_halted
                        (cachedInputMachine machine) input
                        (materializeLocalReplayState base state) outcome
                        hhaltMaterialized,
                        runFrom_eq_self_of_halted
                          (cachedInputMachine machine) input
                          (materializeLocalReplayState base state) outcome
                          hhaltMaterialized]
              · rw [cachedRunUnreadSymbols, hstutter]
                rw [cachedRunUnreadSymbols, hstutter]
                simp only [materializeLocalReplayState]
                rw [finiteCachedVisitSymbolsAgree_cons_cons, hlocal]
                constructor
                · rfl
                · simpa only [cachedRunUnreadSymbols, hstutter] using
                    htailAgree
          | none =>
              let instruction := cachedInputTransition machine state.control
                unread (state.workSlab state.relativeWorkHead)
              have hglobal := step_cached_materialized_eq_applyInstruction
                machine input (base := base) state hhalt
              have hnextInputBound :
                  (step (cachedInputMachine machine) input
                    (materializeLocalReplayState base state)).inputHead <
                      H + 1 := by
                have hmono := inputHead_le_runFrom
                  (cachedInputMachine machine) input
                  (step (cachedInputMachine machine) input
                    (materializeLocalReplayState base state))
                  (remaining + 1)
                exact lt_of_le_of_lt hmono (by
                  simpa only [runFrom_succ] using hfinalInput)
              have hnextInside : WorkCellInSlab base w
                  (step (cachedInputMachine machine) input
                    (materializeLocalReplayState base state)).workHead := by
                have hone := hinside 1 (by omega)
                simpa only [runFrom_succ, runFrom_zero] using hone
              have hinput :
                  moveInputHead state.inputHead.val instruction.inputMove <
                    H + 1 := by
                have hnextInputBound' := hnextInputBound
                rw [hglobal] at hnextInputBound'
                simpa [applyInstruction, materializeLocalReplayState,
                  instruction, unread] using hnextInputBound'
              have hwork : WorkCellInSlab base w
                  (moveWorkHead (base + state.relativeWorkHead.val)
                    instruction.workMove) := by
                have hnextInside' := hnextInside
                rw [hglobal] at hnextInside'
                simpa [applyInstruction, materializeLocalReplayState,
                  instruction, unread] using hnextInside'
              let next : LocalReplayState
                  (cachedInputMachine machine).State H w :=
                { control := instruction.nextState
                  inputHead := ⟨moveInputHead state.inputHead.val
                    instruction.inputMove, hinput⟩
                  relativeWorkHead := workCellIndex hwork
                  workSlab := writeWorkSlab state.workSlab
                    state.relativeWorkHead instruction.write }
              have hlocal : finiteLocalCachedStep machine H w base unread
                  state = .inside next := by
                unfold finiteLocalCachedStep
                rw [hhalt]
                dsimp only
                rw [dif_pos hinput, dif_pos hwork]
              have hmaterialize : materializeLocalReplayState base next =
                  step (cachedInputMachine machine) input
                    (materializeLocalReplayState base state) :=
                finiteLocalCachedStep_inside_materialize
                  machine unread state next input rfl hlocal
              have hinsideTail : ∀ time, time < remaining + 1 →
                  WorkCellInSlab base w
                    (runFrom (cachedInputMachine machine) input
                      (materializeLocalReplayState base next) time).workHead := by
                intro time htime
                have h := hinside (time + 1) (by omega)
                simpa only [runFrom_succ, hmaterialize] using h
              have hfinalInputTail :
                  (runFrom (cachedInputMachine machine) input
                    (materializeLocalReplayState base next)
                    (remaining + 1)).inputHead < H + 1 := by
                simpa only [runFrom_succ, hmaterialize] using hfinalInput
              have hfinalWorkTail :
                  (runFrom (cachedInputMachine machine) input
                    (materializeLocalReplayState base next)
                    (remaining + 1)).workHead < H + 1 := by
                simpa only [runFrom_succ, hmaterialize] using hfinalWork
              obtain ⟨final, htailReplay, htailMaterialize, htailAgree⟩ :=
                ih next (by omega) hinsideTail hfinalInputTail hfinalWorkTail
              refine ⟨final, ?_, ?_, ?_⟩
              · rw [cachedRunUnreadSymbols, ← hmaterialize]
                rw [cachedRunUnreadSymbols]
                simp only [materializeLocalReplayState]
                rw [finiteCachedVisitReplay_cons_cons, hlocal]
                simpa only [cachedRunUnreadSymbols] using htailReplay
              · calc
                  materializeFiniteLocalFinalState base final =
                      runFrom (cachedInputMachine machine) input
                        (materializeLocalReplayState base next)
                        (remaining + 1) := htailMaterialize
                  _ = runFrom (cachedInputMachine machine) input
                        (materializeLocalReplayState base state)
                        (remaining + 1 + 1) := by
                      symm
                      rw [runFrom_succ, ← hmaterialize]
              · rw [cachedRunUnreadSymbols, ← hmaterialize]
                rw [cachedRunUnreadSymbols]
                simp only [materializeLocalReplayState]
                rw [finiteCachedVisitSymbolsAgree_cons_cons, hlocal]
                constructor
                · rfl
                · simpa only [cachedRunUnreadSymbols] using htailAgree

/-- The advertised block slab lies wholly in the ambient work horizon. -/
theorem advertisedBlockLower_add_width_le_horizon
    {T b : Nat} (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1)) :
    advertisedBlockLower offsets block +
        advertisedBlockWidth offsets block ≤ T + 1 := by
  rw [advertisedBlockLower_add_width_eq_upperExclusive]
  exact advertisedBlockUpperExclusive_le_total_add_one offsets block

/-- Convert an advertised entry and carried slab to the finite cached replay
carrier.  The only proof argument is the necessary fact that the advertised
entry head is in this block's slab. -/
def finiteCachedStateOfVisitEntry
    (machine : DeterministicMachine) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (hentry : WorkCellInSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      visit.entry.workHead.val) :
    LocalReplayState (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block) where
  control := visit.entry.state
  inputHead := visit.entry.inputHead
  relativeWorkHead := workCellIndex hentry
  workSlab := carried

/-- Materializing the finite advertised entry recovers exactly the old
fixed-alpha entry configuration. -/
theorem materialize_finiteCachedStateOfVisitEntry
    (machine : DeterministicMachine) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (hentry : WorkCellInSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      visit.entry.workHead.val) :
    materializeLocalReplayState
        (advertisedBlockLower alpha.offsets block)
        (finiteCachedStateOfVisitEntry machine alpha block visit carried
          hentry) =
      fixedAlphaBlockVisitEntryConfiguration alpha block visit carried := by
  unfold materializeLocalReplayState finiteCachedStateOfVisitEntry
    fixedAlphaBlockVisitEntryConfiguration
    configurationOfFixedAlphaEndpoint
  congr 1
  simpa [workSlabCell] using workSlabCell_workCellIndex hentry

/-- Restricting a materialized finite endpoint recovers its stored slab. -/
@[simp]
theorem restrictWorkSlab_materializeFiniteLocalFinalState
    {State : Type} {H w base : Nat}
    (state : FiniteLocalFinalState State H w) :
    restrictWorkSlab base w
        (materializeFiniteLocalFinalState base state).workTape =
      state.workSlab := by
  change restrictWorkSlab base w
      (workTapeOfWorkSlab base state.workSlab) = state.workSlab
  exact restrictWorkSlab_workTapeOfWorkSlab base state.workSlab

/-- Fixed-alpha wrapper: replay one advertised cached-machine visit from a
finite carried slab and a chronologically supplied finite symbol list. -/
def finiteCachedFixedAlphaBlockVisitReplay
    (machine : DeterministicMachine) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (hentry : WorkCellInSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      visit.entry.workHead.val)
    (unreads : List ReadOnlySymbol) :
    FiniteCachedVisitReplayResult (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block) :=
  finiteCachedVisitReplay machine T
    (advertisedBlockWidth alpha.offsets block)
    (advertisedBlockLower alpha.offsets block)
    (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
    unreads
    (finiteCachedStateOfVisitEntry machine alpha block visit carried hentry)

/-- Sound bridge from a completed finite cached replay to the old semantic
one-visit validity predicate.

The hypotheses mention only the explicit finite symbol list, the finite
runner result, and equality with the advertised finite endpoint.  The
conclusion recovers both `FixedAlphaBlockVisitValid` and the old carried
output slab.  Thus no full work tape is needed by the executable replay; a
full configuration appears only in this correctness theorem.
-/
theorem finiteCachedFixedAlphaBlockVisitReplay_completed_sound
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (hentry : WorkCellInSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      visit.entry.workHead.val)
    (unreads : List ReadOnlySymbol)
    (final : FiniteLocalFinalState (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block))
    (hlength : unreads.length = visit.steps)
    (hagree : FiniteCachedVisitSymbolsAgree machine input T
      (advertisedBlockWidth alpha.offsets block)
      (advertisedBlockLower alpha.offsets block) unreads
      (finiteCachedStateOfVisitEntry machine alpha block visit carried
        hentry))
    (hreplay : finiteCachedFixedAlphaBlockVisitReplay machine alpha block
      visit carried hentry unreads = .completed final)
    (hendpoint : visit.exit.state = final.control ∧
      visit.exit.inputHead = final.inputHead ∧
      visit.exit.workHead = final.workHead) :
    FixedAlphaBlockVisitValid (cachedInputMachine machine) input alpha block
        visit carried ∧
      final.workSlab = fixedAlphaBlockVisitOutputSlab
        (cachedInputMachine machine) input alpha block visit carried := by
  let base := advertisedBlockLower alpha.offsets block
  let width := advertisedBlockWidth alpha.offsets block
  let initial := finiteCachedStateOfVisitEntry
    machine alpha block visit carried hentry
  have hsound := finiteCachedVisitReplay_completed_sound
    machine input
    (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
    unreads initial final hagree (by
      simpa [finiteCachedFixedAlphaBlockVisitReplay, initial, base, width]
        using hreplay)
  have hinitial : materializeLocalReplayState base initial =
      fixedAlphaBlockVisitEntryConfiguration alpha block visit carried := by
    simpa [base, initial] using
      materialize_finiteCachedStateOfVisitEntry
        machine alpha block visit carried hentry
  have hrun : materializeFiniteLocalFinalState base final =
      fixedAlphaBlockVisitRun (cachedInputMachine machine) input alpha block
        visit carried := by
    calc
      materializeFiniteLocalFinalState base final =
          runFrom (cachedInputMachine machine) input
            (materializeLocalReplayState base initial) unreads.length :=
        hsound.1
      _ = runFrom (cachedInputMachine machine) input
          (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
          visit.steps := by rw [hinitial, hlength]
      _ = fixedAlphaBlockVisitRun (cachedInputMachine machine) input alpha
          block visit carried := rfl
  constructor
  · constructor
    · intro time
      let lifted : Fin unreads.length := ⟨time.val, by
        rw [hlength]
        exact time.isLt⟩
      have hinside := hsound.2 lifted
      simpa [base, width, hinitial, hlength, lifted] using hinside
    · rw [← hrun]
      rcases hendpoint with ⟨hstate, hinput, hwork⟩
      exact ⟨hstate, congrArg Fin.val hinput, congrArg Fin.val hwork⟩
  · calc
      final.workSlab = restrictWorkSlab base width
          (materializeFiniteLocalFinalState base final).workTape := by simp
      _ = restrictWorkSlab base width
          (fixedAlphaBlockVisitRun (cachedInputMachine machine) input alpha
            block visit carried).workTape := by rw [hrun]
      _ = fixedAlphaBlockVisitOutputSlab
          (cachedInputMachine machine) input alpha block visit carried := rfl

/-- Finite certificate for one cached fixed-alpha visit.  The unread list is
the chronological list of symbols of the old semantic run, but the replay
itself receives that list explicitly and carries only finite local state. -/
def FiniteCachedFixedAlphaVisitCertificate
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block)) : Prop :=
  ∃ hentry : WorkCellInSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      visit.entry.workHead.val,
    ∃ final : FiniteLocalFinalState (cachedInputMachine machine).State T
        (advertisedBlockWidth alpha.offsets block),
      finiteCachedFixedAlphaBlockVisitReplay machine alpha block visit
          carried hentry
          (cachedRunUnreadSymbols machine input
            (fixedAlphaBlockVisitEntryConfiguration
              alpha block visit carried) visit.steps) =
        .completed final ∧
      FiniteCachedVisitSymbolsAgree machine input T
          (advertisedBlockWidth alpha.offsets block)
          (advertisedBlockLower alpha.offsets block)
          (cachedRunUnreadSymbols machine input
            (fixedAlphaBlockVisitEntryConfiguration
              alpha block visit carried) visit.steps)
          (finiteCachedStateOfVisitEntry machine alpha block visit carried
            hentry) ∧
      visit.exit.state = final.control ∧
        visit.exit.inputHead = final.inputHead ∧
        visit.exit.workHead = final.workHead

/-- Exact correspondence with the old one-visit semantics.

This closes both directions, including early halted stuttering and a final
step that exits the slab.  The only full configurations in the proof are the
old semantic reference run and materializations used to state correctness;
the executable certificate state and transition are finite.
-/
theorem finiteCachedFixedAlphaVisitCertificate_iff
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block)) :
    FiniteCachedFixedAlphaVisitCertificate machine input alpha block visit
        carried ↔
      FixedAlphaBlockVisitValid (cachedInputMachine machine) input alpha block
        visit carried := by
  constructor
  · rintro ⟨hentry, final, hreplay, hagree, hstate, hinput, hwork⟩
    exact (finiteCachedFixedAlphaBlockVisitReplay_completed_sound
      machine input alpha block visit carried hentry
      (cachedRunUnreadSymbols machine input
        (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
        visit.steps)
      final (by simp) hagree hreplay ⟨hstate, hinput, hwork⟩).1
  · intro hvalid
    have hentry : WorkCellInSlab
        (advertisedBlockLower alpha.offsets block)
        (advertisedBlockWidth alpha.offsets block)
        visit.entry.workHead.val := by
      have hzero := hvalid.1 ⟨0, visit.steps_pos⟩
      simpa [fixedAlphaBlockVisitEntryConfiguration] using hzero
    let base := advertisedBlockLower alpha.offsets block
    let width := advertisedBlockWidth alpha.offsets block
    let initial := finiteCachedStateOfVisitEntry
      machine alpha block visit carried hentry
    have hinitial : materializeLocalReplayState base initial =
        fixedAlphaBlockVisitEntryConfiguration alpha block visit carried := by
      simpa [base, initial] using
        materialize_finiteCachedStateOfVisitEntry
          machine alpha block visit carried hentry
    have hinside : ∀ time, time < visit.steps →
        WorkCellInSlab base width
          (runFrom (cachedInputMachine machine) input
            (materializeLocalReplayState base initial) time).workHead := by
      intro time htime
      have h := hvalid.1 ⟨time, htime⟩
      simpa [base, width, hinitial] using h
    have hrun : runFrom (cachedInputMachine machine) input
          (materializeLocalReplayState base initial) visit.steps =
        fixedAlphaBlockVisitRun (cachedInputMachine machine) input alpha block
          visit carried := by
      rw [hinitial]
      rfl
    have hfinalInput :
        (runFrom (cachedInputMachine machine) input
          (materializeLocalReplayState base initial) visit.steps).inputHead <
            T + 1 := by
      rw [hrun, ← hvalid.2.2.1]
      exact visit.exit.inputHead.isLt
    have hfinalWork :
        (runFrom (cachedInputMachine machine) input
          (materializeLocalReplayState base initial) visit.steps).workHead <
            T + 1 := by
      rw [hrun, ← hvalid.2.2.2]
      exact visit.exit.workHead.isLt
    obtain ⟨final, hreplay, hmaterialize, hagree⟩ :=
      finiteCachedVisitReplay_complete_of_semantic_bounds
        machine input
        (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
        initial visit.steps visit.steps_pos hinside hfinalInput hfinalWork
    have hmaterializeRun : materializeFiniteLocalFinalState base final =
        fixedAlphaBlockVisitRun (cachedInputMachine machine) input alpha block
          visit carried := hmaterialize.trans hrun
    refine ⟨hentry, final, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [finiteCachedFixedAlphaBlockVisitReplay, initial, base, width,
        hinitial] using hreplay
    · simpa [initial, base, width, hinitial] using hagree
    · calc
        visit.exit.state =
            (fixedAlphaBlockVisitRun (cachedInputMachine machine) input alpha
              block visit carried).state := hvalid.2.1
        _ = (materializeFiniteLocalFinalState base final).state :=
          congrArg Configuration.state hmaterializeRun.symm
        _ = final.control := rfl
    · apply Fin.ext
      calc
        visit.exit.inputHead.val =
            (fixedAlphaBlockVisitRun (cachedInputMachine machine) input alpha
              block visit carried).inputHead := hvalid.2.2.1
        _ = (materializeFiniteLocalFinalState base final).inputHead :=
          congrArg Configuration.inputHead hmaterializeRun.symm
        _ = final.inputHead.val := rfl
    · apply Fin.ext
      calc
        visit.exit.workHead.val =
            (fixedAlphaBlockVisitRun (cachedInputMachine machine) input alpha
              block visit carried).workHead := hvalid.2.2.2
        _ = (materializeFiniteLocalFinalState base final).workHead :=
          congrArg Configuration.workHead hmaterializeRun.symm
        _ = final.workHead.val := rfl

/-- A completed finite replay matches the advertised visit endpoint exactly
when its retained control and two bounded absolute heads do. -/
def FiniteCachedVisitResultMatchesEndpoint
    {State : Type} {T w : Nat}
    (endpoint : FixedAlphaVisitEndpoint State T)
    (result : FiniteCachedVisitReplayResult State T w) : Prop :=
  match result with
  | .completed state =>
      endpoint.state = state.control ∧
        endpoint.inputHead = state.inputHead ∧
        endpoint.workHead = state.workHead
  | _ => False

/-- A successful fixed-alpha finite replay exposes the exact next carried
slab without materializing a full work tape. -/
def finiteCachedVisitOutputSlab?
    {State : Type} {H w : Nat}
    (result : FiniteCachedVisitReplayResult State H w) :
    Option (WorkSlab w) :=
  match result with
  | .completed state => some state.workSlab
  | _ => none

end OneTapeMagnification
end Frontier
end Pnp4
