import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.GuardedCanonicalAggregateEndpoint

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Exact rejecting master guards for canonical components

The existing `LayeredQueryProgram.guardByMasterOrder` is a read-once guard,
but it is deliberately permissive on a master-order mismatch: it supplies
`none` to the base transition.  For an arbitrary base program that can create
a false positive.  This file first records a finite counterexample, then adds
a rejecting variant whose mismatch state is an absorbing false-output sink.

The intended application is the total fused canonical component compiler.
The rejecting guard keeps the same accepted canonical execution, while its
generic soundness direction needs no replay or follows-master premise.
-/

namespace LayeredQueryProgram

/-! ## The permissive guard has no generic soundness theorem -/

/-- A one-layer program that rejects when it receives the answer to its real
query, but accepts if that query is silently suppressed. -/
def permissiveGuardFalsePositiveProgram : LayeredQueryProgram 2 1 where
  State := Bool
  stateFintype := inferInstance
  start := false
  query? := fun _ _ => some (1 : Fin 2)
  next := fun _ _ answer =>
    match answer with
    | none => true
    | some _ => false
  output := id

/-- On the all-false input the base program rejects, while guarding it by the
incompatible singleton master `[0]` accepts.  Thus
`guardByMasterOrder_eval = true -> base.eval = true` is false in general. -/
theorem guardByMasterOrder_can_create_false_positive :
    (guardByMasterOrder permissiveGuardFalsePositiveProgram
        [(0 : Fin 2)]).eval (fun _ => false) = true /\
      permissiveGuardFalsePositiveProgram.eval (fun _ => false) = false := by
  constructor <;> rfl

/-! ## A rejecting guard -/

/-- Live guarded state, or one absorbing rejection sink. -/
abbrev RejectingMasterGuardState {n L : Nat}
    (program : LayeredQueryProgram n L) (master : List (Fin n)) :=
  Option (Prod program.State (MasterCursor master))

/-- A live state exposes exactly the query exposed by the old master guard;
the rejection sink exposes no query. -/
def rejectingMasterGuardQuery? {n L : Nat}
    (program : LayeredQueryProgram n L) (master : List (Fin n))
    (layer : Fin L) :
    RejectingMasterGuardState program master -> Option (Fin n)
  | none => none
  | some state => masterGuardedQuery? program master layer state

/-- Delegate a silent base layer.  Delegate a real query only when it matches
the current master position and carries a real answer.  Every mismatch enters
the absorbing rejection sink instead of supplying `none` to the base program. -/
def rejectingMasterGuardNext {n L : Nat}
    (program : LayeredQueryProgram n L) (master : List (Fin n))
    (layer : Fin L) :
    RejectingMasterGuardState program master -> Option Bool ->
      RejectingMasterGuardState program master
  | none, _ => none
  | some state, answer =>
      match program.query? layer state.1,
          masterGuardedQuery? program master layer state, answer with
      | none, _, _ => some (program.next layer state.1 none, state.2)
      | some _, some _, some bit =>
          some (program.next layer state.1 (some bit),
            advanceMasterCursor master state.2)
      | some _, _, _ => none

/-- Add an absorbing false-output sink to master-order guarding. -/
def rejectingGuardByMasterOrder {n L : Nat}
    (program : LayeredQueryProgram n L) (master : List (Fin n)) :
    LayeredQueryProgram n L where
  State := RejectingMasterGuardState program master
  stateFintype := by
    letI := program.stateFintype
    infer_instance
  start := some (program.start, Fin.mk 0 (Nat.zero_lt_succ _))
  query? := rejectingMasterGuardQuery? program master
  next := rejectingMasterGuardNext program master
  output := fun state =>
    match state with
    | none => false
    | some state => program.output state.1

/-- The rejecting guard has exactly one more state than the old product
guard: the single absorbing rejection sink. -/
@[simp] theorem rejectingGuardByMasterOrder_width
    {n L : Nat} (program : LayeredQueryProgram n L)
    (master : List (Fin n)) :
    (rejectingGuardByMasterOrder program master).width =
      program.width * (master.length + 1) + 1 := by
  simp [rejectingGuardByMasterOrder, RejectingMasterGuardState,
    LayeredQueryProgram.width]

/-- If one rejecting-guard step remains live, its base-state projection is
exactly the ordinary base transition on the same input. -/
theorem rejectingMasterGuardNext_live_state_eq_baseNext
    {n L : Nat} (program : LayeredQueryProgram n L)
    (master : List (Fin n)) (layer : Fin L)
    (state : Prod program.State (MasterCursor master))
    (input : Fin n -> Bool)
    (nextState : Prod program.State (MasterCursor master))
    (hnext : rejectingMasterGuardNext program master layer (some state)
        ((rejectingMasterGuardQuery? program master layer (some state)).map
          input) = some nextState) :
    nextState.1 = program.next layer state.1
      ((program.query? layer state.1).map input) := by
  cases hbase : program.query? layer state.1 with
  | none =>
      simp [rejectingMasterGuardQuery?, rejectingMasterGuardNext,
        masterGuardedQuery?, hbase] at hnext
      exact congrArg Prod.fst hnext.symm
  | some actual =>
      cases hmaster : masterCursorQuery? master state.2 with
      | none =>
          simp [rejectingMasterGuardQuery?, rejectingMasterGuardNext,
            masterGuardedQuery?, hbase, hmaster] at hnext
      | some expected =>
          by_cases heq : actual = expected
          . simp [rejectingMasterGuardQuery?, rejectingMasterGuardNext,
              masterGuardedQuery?, hbase, hmaster, heq] at hnext
            simpa [heq] using congrArg Prod.fst hnext.symm
          . simp [rejectingMasterGuardQuery?, rejectingMasterGuardNext,
              masterGuardedQuery?, hbase, hmaster, heq] at hnext

/-- At every prefix, survival outside the rejection sink implies exact
agreement of the projected live state with the unguarded base execution. -/
theorem rejectingGuardByMasterOrder_executePrefix_live_state_eq_base
    {n L : Nat} (program : LayeredQueryProgram n L)
    (master : List (Fin n)) (input : Fin n -> Bool)
    (k : Nat) (hk : k <= L)
    (live : Prod program.State (MasterCursor master))
    (hlive : ((rejectingGuardByMasterOrder program master).executePrefix
        input k hk).1 = some live) :
    live.1 = (program.executePrefix input k hk).1 := by
  induction k generalizing live with
  | zero =>
      simp [executePrefix, rejectingGuardByMasterOrder] at hlive
      exact congrArg Prod.fst hlive.symm
  | succ k ih =>
      let guarded := rejectingGuardByMasterOrder program master
      let previous := guarded.executePrefix input k (by omega)
      let layer : Fin L := Fin.mk k (by omega)
      have hstep :
          guarded.next layer previous.1
              ((guarded.query? layer previous.1).map input) = some live := by
        simpa [guarded, previous, layer, executePrefix] using hlive
      cases hprevious : previous.1 with
      | none =>
          rw [hprevious] at hstep
          change rejectingMasterGuardNext program master layer none
              ((rejectingMasterGuardQuery? program master layer none).map
                input) = some live at hstep
          simp [rejectingMasterGuardNext] at hstep
      | some previousLive =>
          rw [hprevious] at hstep
          have hpreviousLive :
              (guarded.executePrefix input k (by omega)).1 =
                some previousLive := by
            simpa [previous] using hprevious
          have hprojection : previousLive.1 =
              (program.executePrefix input k (by omega)).1 :=
            ih (by omega) previousLive hpreviousLive
          have hnextProjection :=
            rejectingMasterGuardNext_live_state_eq_baseNext
              program master layer previousLive input live (by
                simpa [guarded, rejectingGuardByMasterOrder] using hstep)
          simp only [executePrefix]
          rw [hprojection] at hnextProjection
          simpa [layer] using hnextProjection

/-- The rejecting guard can never create a false positive, for any base
program, master list, or input. -/
theorem rejectingGuardByMasterOrder_eval_true_implies_base
    {n L : Nat} (program : LayeredQueryProgram n L)
    (master : List (Fin n)) (input : Fin n -> Bool)
    (haccept : (rejectingGuardByMasterOrder program master).eval input =
      true) :
    program.eval input = true := by
  unfold eval finalState at haccept
  unfold eval finalState
  generalize hfinal :
      ((rejectingGuardByMasterOrder program master).executePrefix
        input L le_rfl).1 = final at haccept
  cases final with
  | none =>
      simp [rejectingGuardByMasterOrder] at haccept
  | some live =>
      have hstate :=
        rejectingGuardByMasterOrder_executePrefix_live_state_eq_base
          program master input L le_rfl live hfinal
      change program.output live.1 = true at haccept
      simpa [hstate] using haccept

/-- If the base execution follows the master, the rejecting guard never
enters its sink and simulates the base state and trace exactly. -/
theorem rejectingGuardByMasterOrder_executePrefix_simulates_of_follows
    {n L : Nat} (program : LayeredQueryProgram n L)
    (master : List (Fin n)) (input : Fin n -> Bool)
    (hfollows : ExecutionQueriesFollowMaster program master input)
    (k : Nat) (hk : k <= L) :
    let base := program.executePrefix input k hk
    let guarded := (rejectingGuardByMasterOrder program master).executePrefix
      input k hk
    Exists fun cursor : MasterCursor master =>
      guarded.1 = some (base.1, cursor) /\
        cursor.val = base.2.length /\ guarded.2 = base.2 := by
  induction k with
  | zero =>
      refine Exists.intro (Fin.mk 0 (Nat.zero_lt_succ _)) ?_
      simp [executePrefix, rejectingGuardByMasterOrder]
  | succ k ih =>
      let guardedProgram := rejectingGuardByMasterOrder program master
      let basePrevious := program.executePrefix input k (by omega)
      let guardedPrevious := guardedProgram.executePrefix input k (by omega)
      let layer : Fin L := Fin.mk k (by omega)
      have hprevious := ih (by omega)
      dsimp only at hprevious
      choose cursor hstate hcursor htrace using hprevious
      have hfollow := hfollows k (by omega)
      dsimp only at hfollow
      let baseQuery := program.query? layer basePrevious.1
      change (match baseQuery with
        | none => True
        | some query =>
            Exists fun hlength : basePrevious.2.length < master.length =>
              master.get (Fin.mk basePrevious.2.length hlength) = query)
        at hfollow
      cases hbaseQuery : baseQuery with
      | none =>
          have hbaseQueryStep : program.query? (Fin.mk k (by omega))
              (program.executePrefix input k (by omega)).1 = none := by
            simpa [baseQuery, basePrevious, layer] using hbaseQuery
          have hguardedQueryStep :
              guardedProgram.query? (Fin.mk k (by omega))
                (guardedProgram.executePrefix input k (by omega)).1 = none := by
            rw [hstate]
            simp [guardedProgram, rejectingGuardByMasterOrder,
              rejectingMasterGuardQuery?, masterGuardedQuery?,
              hbaseQueryStep]
          have hguardedNextStep :
              guardedProgram.next (Fin.mk k (by omega))
                  (guardedProgram.executePrefix input k (by omega)).1 none =
                some (program.next (Fin.mk k (by omega))
                  (program.executePrefix input k (by omega)).1 none, cursor) := by
            rw [hstate]
            simp [guardedProgram, rejectingGuardByMasterOrder,
              rejectingMasterGuardNext, hbaseQueryStep]
          refine Exists.intro cursor ?_
          simp only [executePrefix]
          rw [hguardedQueryStep, hbaseQueryStep]
          simp only [Option.map_none, Option.toList_none, List.append_nil]
          rw [hguardedNextStep]
          exact And.intro rfl (And.intro hcursor htrace)
      | some query =>
          simp [hbaseQuery] at hfollow
          choose hlength hget using hfollow
          have hcursorLength : cursor.val < master.length := by
            simpa [hcursor] using hlength
          have hmasterQuery : masterCursorQuery? master cursor =
              some query := by
            rw [masterCursorQuery?, dif_pos hcursorLength]
            apply congrArg some
            simpa [hcursor] using hget
          have hbaseQueryStep : program.query? (Fin.mk k (by omega))
              (program.executePrefix input k (by omega)).1 = some query := by
            simpa [baseQuery, basePrevious, layer] using hbaseQuery
          have hguardedQueryStep :
              guardedProgram.query? (Fin.mk k (by omega))
                (guardedProgram.executePrefix input k (by omega)).1 =
                  some query := by
            rw [hstate]
            simp [guardedProgram, rejectingGuardByMasterOrder,
              rejectingMasterGuardQuery?, masterGuardedQuery?,
              hbaseQueryStep, hmasterQuery]
          have hguardedNextStep :
              guardedProgram.next (Fin.mk k (by omega))
                  (guardedProgram.executePrefix input k (by omega)).1
                  (some (input query)) =
                some (program.next (Fin.mk k (by omega))
                    (program.executePrefix input k (by omega)).1
                    (some (input query)),
                  advanceMasterCursor master cursor) := by
            rw [hstate]
            simp [guardedProgram, rejectingGuardByMasterOrder,
              rejectingMasterGuardNext, masterGuardedQuery?,
              hbaseQueryStep, hmasterQuery]
          refine Exists.intro (advanceMasterCursor master cursor) ?_
          simp only [executePrefix]
          rw [hguardedQueryStep, hbaseQueryStep]
          simp only [Option.map_some, Option.toList_some]
          rw [hguardedNextStep]
          refine And.intro rfl (And.intro ?_ ?_)
          . rw [advanceMasterCursor_val_of_lt master cursor hcursorLength,
              hcursor]
            simp
          . rw [htrace]

/-- Exact semantic preservation whenever the base query sequence follows the
master. -/
theorem rejectingGuardByMasterOrder_eval_eq_of_follows
    {n L : Nat} (program : LayeredQueryProgram n L)
    (master : List (Fin n)) (input : Fin n -> Bool)
    (hfollows : ExecutionQueriesFollowMaster program master input) :
    (rejectingGuardByMasterOrder program master).eval input =
      program.eval input := by
  have hfinal :=
    rejectingGuardByMasterOrder_executePrefix_simulates_of_follows
      program master input hfollows L le_rfl
  dsimp only at hfinal
  choose cursor hstate hcursor htrace using hfinal
  unfold eval finalState
  rw [hstate]
  rfl

/-- Trace invariant used to prove read-once behavior.  A live trace is the
master prefix at its cursor.  Once rejected, the frozen trace remains some
master prefix even though the cursor is no longer stored. -/
def RejectingGuardTraceMatchesState {n L : Nat}
    (program : LayeredQueryProgram n L) (master : List (Fin n))
    (state : RejectingMasterGuardState program master)
    (trace : List (Fin n)) : Prop :=
  match state with
  | none => Exists fun k => k <= master.length /\ trace = master.take k
  | some live => trace = master.take live.2.val

private theorem rejectingGuard_take_succ_eq_take_append_get
    {alpha : Type} (items : List alpha) (index : Nat)
    (hindex : index < items.length) :
    items.take (index + 1) =
      items.take index ++ [items.get (Fin.mk index hindex)] := by
  induction items generalizing index with
  | nil => simp at hindex
  | cons item rest ih =>
      cases index with
      | zero => simp
      | succ index =>
          simp only [List.take_succ_cons, List.get_cons_succ,
            List.cons_append, List.cons.injEq, true_and]
          exact ih index (by simpa using hindex)

/-- Every prefix of the rejecting execution satisfies the master-prefix
trace invariant. -/
theorem rejectingGuardByMasterOrder_executePrefix_trace_matches
    {n L : Nat} (program : LayeredQueryProgram n L)
    (master : List (Fin n)) (input : Fin n -> Bool)
    (k : Nat) (hk : k <= L) :
    let executed := (rejectingGuardByMasterOrder program master).executePrefix
      input k hk
    RejectingGuardTraceMatchesState program master executed.1 executed.2 := by
  induction k with
  | zero =>
      simp [executePrefix, rejectingGuardByMasterOrder,
        RejectingGuardTraceMatchesState]
  | succ k ih =>
      let guarded := rejectingGuardByMasterOrder program master
      let previous := guarded.executePrefix input k (by omega)
      let layer : Fin L := Fin.mk k (by omega)
      have hprevious : RejectingGuardTraceMatchesState program master
          previous.1 previous.2 := by
        simpa [guarded, previous] using ih (by omega)
      simp only [executePrefix]
      cases hstate : previous.1 with
      | none =>
          change RejectingGuardTraceMatchesState program master
            (rejectingMasterGuardNext program master layer none
              ((rejectingMasterGuardQuery? program master layer none).map
                input))
            (previous.2 ++
              (rejectingMasterGuardQuery? program master layer none).toList)
          simpa [rejectingMasterGuardQuery?, rejectingMasterGuardNext,
            hstate] using hprevious
      | some live =>
          have htrace : previous.2 = master.take live.2.val := by
            simpa [RejectingGuardTraceMatchesState, hstate] using hprevious
          cases hbase : program.query? layer live.1 with
          | none =>
              change RejectingGuardTraceMatchesState program master
                (rejectingMasterGuardNext program master layer (some live)
                  ((rejectingMasterGuardQuery? program master layer
                    (some live)).map input))
                (previous.2 ++
                  (rejectingMasterGuardQuery? program master layer
                    (some live)).toList)
              simp [RejectingGuardTraceMatchesState,
                rejectingMasterGuardQuery?, rejectingMasterGuardNext,
                masterGuardedQuery?, hbase, htrace]
          | some actual =>
              cases hmaster : masterCursorQuery? master live.2 with
              | none =>
                  change RejectingGuardTraceMatchesState program master
                    (rejectingMasterGuardNext program master layer (some live)
                      ((rejectingMasterGuardQuery? program master layer
                        (some live)).map input))
                    (previous.2 ++
                      (rejectingMasterGuardQuery? program master layer
                        (some live)).toList)
                  simp only [rejectingMasterGuardQuery?,
                    rejectingMasterGuardNext, masterGuardedQuery?, hbase,
                    hmaster, RejectingGuardTraceMatchesState,
                    Option.toList_none, List.append_nil]
                  refine Exists.intro live.2.val ?_
                  constructor
                  . omega
                  . exact htrace
              | some expected =>
                  by_cases heq : actual = expected
                  . have hcursor : live.2.val < master.length := by
                      by_contra hnot
                      simp [masterCursorQuery?, hnot] at hmaster
                    have hget : master.get (Fin.mk live.2.val hcursor) =
                        expected := by
                      simpa [masterCursorQuery?, hcursor] using hmaster
                    change RejectingGuardTraceMatchesState program master
                      (rejectingMasterGuardNext program master layer
                        (some live)
                        ((rejectingMasterGuardQuery? program master layer
                          (some live)).map input))
                      (previous.2 ++
                        (rejectingMasterGuardQuery? program master layer
                          (some live)).toList)
                    simp only [rejectingMasterGuardQuery?,
                      rejectingMasterGuardNext, masterGuardedQuery?, hbase,
                      hmaster, heq, if_pos, Option.map_some,
                      Option.toList_some, RejectingGuardTraceMatchesState]
                    rw [advanceMasterCursor_val_of_lt master live.2 hcursor,
                      htrace]
                    symm
                    rw [rejectingGuard_take_succ_eq_take_append_get
                      master live.2.val hcursor, hget]
                  . change RejectingGuardTraceMatchesState program master
                      (rejectingMasterGuardNext program master layer
                        (some live)
                        ((rejectingMasterGuardQuery? program master layer
                          (some live)).map input))
                      (previous.2 ++
                        (rejectingMasterGuardQuery? program master layer
                          (some live)).toList)
                    simp only [rejectingMasterGuardQuery?,
                      rejectingMasterGuardNext, masterGuardedQuery?, hbase,
                      hmaster, heq, RejectingGuardTraceMatchesState]
                    refine Exists.intro live.2.val ?_
                    constructor
                    . omega
                    . simpa using htrace

/-- Every rejecting-guard trace is a prefix, hence a sublist, of the master. -/
theorem rejectingGuardByMasterOrder_queryTrace_sublist
    {n L : Nat} (program : LayeredQueryProgram n L)
    (master : List (Fin n)) (input : Fin n -> Bool) :
    List.Sublist
      ((rejectingGuardByMasterOrder program master).queryTrace input)
      master := by
  have hinvariant :=
    rejectingGuardByMasterOrder_executePrefix_trace_matches
      program master input L le_rfl
  dsimp only at hinvariant
  rw [queryTrace]
  generalize hstate :
      ((rejectingGuardByMasterOrder program master).executePrefix
        input L le_rfl).1 = state at hinvariant
  cases state with
  | none =>
      simp only [RejectingGuardTraceMatchesState] at hinvariant
      choose k hk htrace using hinvariant
      rw [htrace]
      exact List.take_sublist _ _
  | some live =>
      simp only [RejectingGuardTraceMatchesState] at hinvariant
      rw [hinvariant]
      exact List.take_sublist _ _

/-- A duplicate-free master makes the rejecting guard read-once on every
input, including every rejected mismatch path. -/
theorem rejectingGuardByMasterOrder_isReadOnce
    {n L : Nat} (program : LayeredQueryProgram n L)
    (master : List (Fin n)) (hmaster : master.Nodup) :
    (rejectingGuardByMasterOrder program master).IsReadOnce := by
  intro input
  exact hmaster.sublist
    (rejectingGuardByMasterOrder_queryTrace_sublist program master input)

end LayeredQueryProgram

local instance cachedInputMachineStateDecidableEqForExactMasterGuard
    (machine : DeterministicMachine) [DecidableEq machine.State] :
    DecidableEq (cachedInputMachine machine).State :=
  cachedInputStateDecidableEq machine

/-! ## Soundness of the unguarded fused program -/

/-- Acceptance of the fused total compiler already forces every advertised
blank-slab replay to be valid.  This is the missing converse to the existing
`...eval_eq_inPlace_of_acceptedFromBlank` theorem: it follows by erasing the
actual fused execution to the exact outer verifier, not from a replay premise. -/
theorem compileAdaptiveFiniteCachedTimedAlphaAllBlocksInPlaceRollingTotal_eval_true_implies_replayAccepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (heval :
      (compileAdaptiveFiniteCachedTimedAlphaAllBlocksInPlaceRollingTotal
        (n := input.length) machine alpha blockVisits).eval
          (fun index => input.get index) = true) :
    forall block : Fin (T / b + 1),
      FixedAlphaBlockVisitReplayAccepted
        (cachedInputMachine machine) input alpha block
        (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
        (blockVisits block) := by
  let fused :=
    finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier
      machine input.length alpha blockVisits
  let outer := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
    machine input.length alpha blockVisits
  let fusedSelector : fused.State -> Option (Fin input.length) :=
    finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex?
      machine input.length
  let outerSelector : outer.State -> Option (Fin input.length) :=
    finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length
  let inputBits : Fin input.length -> Bool := fun index => input.get index
  let fuel := finiteCachedAllBlocksFuel blockVisits
  have htotal : forall state, fused.requestsInput state = true ->
      exists index, fusedSelector state = some index := by
    intro state hrequest
    exact finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex?_total
      machine input.length state hrequest
  have hrunPhase :
      (fused.runAdaptive fuel (fun bit => .bit bit)
        fusedSelector inputBits).1 =
      fused.inputDrivenCore (fun bit => .bit bit) fusedSelector inputBits
        fuel fused.start := by
    simpa [FiniteStreamingVerifier.runAdaptive,
      FiniteStreamingVerifier.initialFueledState] using
        fused.runAdaptiveFrom_state_eq_inputDrivenCore_of_fuel_le_layers
          (fun bit => .bit bit) fusedSelector inputBits htotal
          (fused.initialFueledState fuel) fuel le_rfl
  have herase :
      eraseFiniteCachedAllBlocksInPlaceRolling machine
          (fused.inputDrivenCore (fun bit => .bit bit) fusedSelector inputBits
            fuel fused.start) =
        outer.inputDrivenCore (fun bit => .bit bit) outerSelector inputBits
          fuel outer.start := by
    have hcore := eraseFiniteCachedAllBlocksInPlaceRolling_inputDrivenCore
      machine alpha blockVisits inputBits fuel fused.start
    have hstart := eraseFiniteCachedAllBlocksInPlaceRolling_totalStart
      machine alpha blockVisits
    have hstart' : eraseFiniteCachedAllBlocksInPlaceRolling machine
        fused.start = outer.start := by
      change eraseFiniteCachedAllBlocksInPlaceRolling machine
          (finiteCachedAllBlocksInPlaceRollingTotalStart machine alpha
            blockVisits) =
        finiteCachedAllBlocksTotalStart machine alpha blockVisits
      exact hstart
    change eraseFiniteCachedAllBlocksInPlaceRolling machine
        (fused.inputDrivenCore (fun bit => .bit bit) fusedSelector inputBits
          fuel fused.start) =
      outer.inputDrivenCore (fun bit => .bit bit) outerSelector inputBits
        fuel (eraseFiniteCachedAllBlocksInPlaceRolling machine fused.start)
      at hcore
    rw [hstart'] at hcore
    exact hcore
  have houterHalted : outer.halted
      (outer.inputDrivenCore (fun bit => .bit bit) outerSelector inputBits
        fuel outer.start) = true := by
    simpa [outer, outerSelector, inputBits, fuel] using
      finiteCachedAllBlocks_inputDrivenCore_halted
        machine input alpha blockVisits
  have hfusedCoreHalted : fused.halted
      (fused.inputDrivenCore (fun bit => .bit bit) fusedSelector inputBits
        fuel fused.start) = true := by
    change finiteCachedAllBlocksInPlaceRollingHalted machine _ = true
    rw [finiteCachedAllBlocksInPlaceRollingHalted_erase, herase]
    exact houterHalted
  have hrunHalted : fused.halted
      (fused.runAdaptive fuel (fun bit => .bit bit)
        fusedSelector inputBits).1 = true := by
    rw [hrunPhase]
    exact hfusedCoreHalted
  have hfinish : fused.finishWithEndSymbol .rightEnd
      (fused.runAdaptive fuel (fun bit => .bit bit)
        fusedSelector inputBits) =
      (fused.runAdaptive fuel (fun bit => .bit bit)
        fusedSelector inputBits).1 :=
    fused.finishWithEndSymbol_eq_of_halted .rightEnd _ hrunHalted
  have hevalCore : fused.accept
      (fused.inputDrivenCore (fun bit => .bit bit) fusedSelector inputBits
        fuel fused.start) = true := by
    have heval' := heval
    rw [compileAdaptiveFiniteCachedTimedAlphaAllBlocksInPlaceRollingTotal_eval]
      at heval'
    change fused.accept
      (fused.finishWithEndSymbol .rightEnd
        (fused.runAdaptive fuel (fun bit => .bit bit)
          fusedSelector inputBits)) = true at heval'
    rw [hfinish, hrunPhase] at heval'
    exact heval'
  have hfusedCompleted : exists fold : InPlaceTwoWindowFoldState T b,
      fused.inputDrivenCore (fun bit => .bit bit) fusedSelector inputBits
        fuel fused.start = .completed fold := by
    generalize hstate : fused.inputDrivenCore (fun bit => .bit bit)
        fusedSelector inputBits fuel fused.start = state at hevalCore
    cases state with
    | active block state allVisits allCuts =>
        simp [fused, finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier,
          finiteCachedAllBlocksInPlaceRollingAccept] at hevalCore
    | completed fold => exact Exists.intro fold rfl
    | rejected =>
        simp [fused, finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier,
          finiteCachedAllBlocksInPlaceRollingAccept] at hevalCore
  choose fold hfusedCompleted using hfusedCompleted
  have houterCompleted :
      outer.inputDrivenCore (fun bit => .bit bit) outerSelector inputBits
        fuel outer.start = .completed := by
    rw [hfusedCompleted] at herase
    simpa [eraseFiniteCachedAllBlocksInPlaceRolling] using herase.symm
  apply (finiteCachedAllBlocks_inputDrivenCore_completed_iff_replayAccepted
    machine input alpha blockVisits).1
  simpa [outer, outerSelector, inputBits, fuel] using houterCompleted

/-! ## Rejecting master guard specialized to the canonical fused component -/

/-- The fused timed-alpha schedule compiler with the rejecting master cursor.
Unlike the earlier permissive guard, every off-master real query enters a
permanent rejecting sink. -/
def compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled) :
    LayeredQueryProgram n
      (finiteCachedAllBlocksFuel
        (fun block => timedAlphaBlockVisits block scheduled)) :=
  LayeredQueryProgram.rejectingGuardByMasterOrder
    (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
      machine alpha scheduled)
    (finiteCachedTimedAlphaScheduleMasterQueryOrder scheduled hmonotone)

/-- A chained monotone schedule supplies a duplicate-free master, so the
rejecting guarded fused component is genuinely read-once on every input,
including mismatch paths that enter the rejecting sink. -/
theorem compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling_isReadOnce
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hchained : TimedAlphaScheduledVisitsChained scheduled)
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled) :
    (compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling
      (n := n) machine alpha scheduled hmonotone).IsReadOnce := by
  apply LayeredQueryProgram.rejectingGuardByMasterOrder_isReadOnce
  exact finiteCachedTimedAlphaScheduleMasterQueryOrder_nodup
    (n := n) scheduled hchained hmonotone

/-- The rejecting sink costs one state beyond the product of the base state
and finite master cursor. -/
@[simp]
theorem compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling_width
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled) :
    (compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling
      (n := n) machine alpha scheduled hmonotone).width =
      (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
        (n := n) machine alpha scheduled).width *
          ((finiteCachedTimedAlphaScheduleMasterQueryOrder
            (n := n) scheduled hmonotone).length + 1) + 1 := by
  exact LayeredQueryProgram.rejectingGuardByMasterOrder_width _ _

/-- On an input whose base execution follows the advertised master order,
the rejecting cursor is observationally invisible. -/
theorem compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling_eval_eq_base_of_follows
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled)
    (input : Fin n -> Bool)
    (hfollows : LayeredQueryProgram.ExecutionQueriesFollowMaster
      (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
        machine alpha scheduled)
      (finiteCachedTimedAlphaScheduleMasterQueryOrder scheduled hmonotone)
      input) :
    (compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling
      machine alpha scheduled hmonotone).eval input =
      (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
        machine alpha scheduled).eval input := by
  exact LayeredQueryProgram.rejectingGuardByMasterOrder_eval_eq_of_follows
    (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
      machine alpha scheduled)
    (finiteCachedTimedAlphaScheduleMasterQueryOrder scheduled hmonotone)
    input hfollows

/-- The canonical accepted-input path is preserved exactly: its real query
trace follows the canonical master, and the compiled Boolean is precisely the
semantic in-place two-window fold Boolean. -/
theorem compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling_eval_eq_timedAlphaFold_of_acceptedFromBlank_canonical
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      (cachedInputMachine machine) input alpha scheduled) :
    let hmonotone :=
      allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
        (cachedInputMachine machine) input alpha scheduled haccepted
    (compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling
      (n := input.length) machine alpha scheduled hmonotone).eval
        (fun index => input.get index) =
      timedAlphaInPlaceTwoWindowFoldCheck
        (cachedInputMachine machine) input alpha scheduled := by
  dsimp only
  let hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled :=
    allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
      (cachedInputMachine machine) input alpha scheduled haccepted
  have hfollows : LayeredQueryProgram.ExecutionQueriesFollowMaster
      (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
        (n := input.length) machine alpha scheduled)
      (finiteCachedTimedAlphaScheduleMasterQueryOrder scheduled hmonotone)
      (fun index => input.get index) := by
    simpa [hmonotone] using
      finiteCachedTimedAlphaScheduleInPlaceRollingExecutionQueriesFollowMaster_of_acceptedFromBlank
        machine input alpha scheduled haccepted
  rw [compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling_eval_eq_base_of_follows
    machine alpha scheduled hmonotone (fun index => input.get index) hfollows]
  let blockVisits := fun block => timedAlphaBlockVisits block scheduled
  have hoperational :=
    compileAdaptiveFiniteCachedTimedAlphaAllBlocksInPlaceRollingTotal_eval_eq_inPlace_of_acceptedFromBlank
      machine input alpha blockVisits (by
        simpa [blockVisits] using haccepted)
  simpa [compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal,
    blockVisits, timedAlphaInPlaceTwoWindowFoldCheck,
    timedScheduleBlankBlockSlabs, timedScheduleBlockVisitFamily] using
      hoperational

/-- Acceptance of the rejecting guarded component is sound even without a
follows-master premise: it can only arise from a live base execution, and the
base fused compiler then forces all advertised blank-slab replays. -/
theorem compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling_eval_true_implies_replayAccepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled)
    (heval :
      (compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling
        (n := input.length) machine alpha scheduled hmonotone).eval
          (fun index => input.get index) = true) :
    forall block : Fin (T / b + 1),
      FixedAlphaBlockVisitReplayAccepted
        (cachedInputMachine machine) input alpha block
        (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
        (timedAlphaBlockVisits block scheduled) := by
  apply
    compileAdaptiveFiniteCachedTimedAlphaAllBlocksInPlaceRollingTotal_eval_true_implies_replayAccepted
      machine input alpha (fun block => timedAlphaBlockVisits block scheduled)
  apply LayeredQueryProgram.rejectingGuardByMasterOrder_eval_true_implies_base
    (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
      (n := input.length) machine alpha scheduled)
    (finiteCachedTimedAlphaScheduleMasterQueryOrder scheduled hmonotone)
    (fun index => input.get index)
  exact heval

/-! ## Total exact read-once component -/

/-- Total checked rejecting compiler.  Invalid schedules and schedules whose
advertised input endpoints are not monotone select a query-free rejection
program; the good branch uses the rejecting master cursor above. -/
def compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b)) :
    LayeredQueryProgram n
      (finiteCachedAllBlocksFuel
        (fun block => timedAlphaBlockVisits block scheduled)) :=
  if _hschedule : timedAlphaVisitScheduleCheck
      (cachedInputMachine machine) alpha scheduled = true then
    if hmonotone : timedAlphaScheduledVisitsInputMonotoneCheck
        scheduled = true then
      compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling
        machine alpha scheduled
        ((timedAlphaScheduledVisitsInputMonotoneCheck_eq_true_iff
          scheduled).1 hmonotone)
    else
      LayeredQueryProgram.constantReject n
        (finiteCachedAllBlocksFuel
          (fun block => timedAlphaBlockVisits block scheduled))
  else
    LayeredQueryProgram.constantReject n
      (finiteCachedAllBlocksFuel
        (fun block => timedAlphaBlockVisits block scheduled))

/-- The checked rejecting compiler is globally read-once for every schedule
and every Boolean input; no semantic acceptance premise is needed. -/
theorem compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_isReadOnce
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b)) :
    (compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
      (n := n) machine alpha scheduled).IsReadOnce := by
  unfold
    compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
  split
  · rename_i hscheduleCheck
    split
    · rename_i hmonotoneCheck
      have hschedule :=
        (timedAlphaVisitScheduleCheck_eq_true_iff
          (cachedInputMachine machine) alpha scheduled).1 hscheduleCheck
      have hmonotone :=
        (timedAlphaScheduledVisitsInputMonotoneCheck_eq_true_iff
          scheduled).1 hmonotoneCheck
      obtain ⟨_syntactic, _finalCursor, _visitsSoFar, _hfold, _hfinish,
        hchained⟩ := hschedule
      exact
        compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling_isReadOnce
          machine alpha scheduled hchained hmonotone
    · exact LayeredQueryProgram.constantReject_isReadOnce _ _
  · exact LayeredQueryProgram.constantReject_isReadOnce _ _

/-- The total rejecting read-once program is extensionally exact for one
fixed alpha and advertised schedule.  The forward direction uses rejecting
guard soundness to recover every replay; the reverse direction uses canonical
accepted-trace preservation.  Thus neither direction retains a
follows-master or replay premise. -/
theorem compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_eval_eq_inPlaceCanonicalCutCheck
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b)) :
    (compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
      (n := input.length) machine alpha scheduled).eval
        (fun index => input.get index) =
      timedAlphaVisitScheduleInPlaceCanonicalCutCheck
        (cachedInputMachine machine) input alpha scheduled := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro heval
    unfold
      compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
      at heval
    split at heval
    · rename_i hscheduleCheck
      split at heval
      · rename_i hmonotoneCheck
        have hvalid : TimedAlphaVisitScheduleValid
            (cachedInputMachine machine) alpha scheduled :=
          (timedAlphaVisitScheduleCheck_eq_true_iff
            (cachedInputMachine machine) alpha scheduled).1 hscheduleCheck
        let hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled :=
          (timedAlphaScheduledVisitsInputMonotoneCheck_eq_true_iff
            scheduled).1 hmonotoneCheck
        have hreplay : forall block : Fin (T / b + 1),
            FixedAlphaBlockVisitReplayAccepted
              (cachedInputMachine machine) input alpha block
              (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
              (timedAlphaBlockVisits block scheduled) := by
          apply
            compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling_eval_true_implies_replayAccepted
              machine input alpha scheduled hmonotone
          simpa [hmonotone] using heval
        have haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
            (cachedInputMachine machine) input alpha scheduled := by
          intro block
          exact ⟨hvalid.blockVisitsChronological
            (cachedInputMachine machine) block, hreplay block⟩
        have hbase : timedAlphaVisitScheduleAllBlockVisitsCheck
            (cachedInputMachine machine) input alpha scheduled = true :=
          (timedAlphaVisitScheduleAllBlockVisitsCheck_eq_true_iff
            (cachedInputMachine machine) input alpha scheduled).2
              ⟨hvalid, haccepted⟩
        have hpreserve :=
          compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling_eval_eq_timedAlphaFold_of_acceptedFromBlank_canonical
            machine input alpha scheduled haccepted
        dsimp only at hpreserve
        have hfold : timedAlphaInPlaceTwoWindowFoldCheck
            (cachedInputMachine machine) input alpha scheduled = true := by
          rw [← hpreserve]
          simpa only using heval
        rw [timedAlphaVisitScheduleInPlaceCanonicalCutCheck,
          Bool.and_eq_true]
        exact ⟨hbase, hfold⟩
      · simp only [LayeredQueryProgram.constantReject_eval,
          Bool.false_eq_true] at heval
    · simp only [LayeredQueryProgram.constantReject_eval,
        Bool.false_eq_true] at heval
  · intro hcheck
    rw [timedAlphaVisitScheduleInPlaceCanonicalCutCheck,
      Bool.and_eq_true] at hcheck
    have hreflect :=
      (timedAlphaVisitScheduleAllBlockVisitsCheck_eq_true_iff
        (cachedInputMachine machine) input alpha scheduled).1 hcheck.1
    have hvalid : TimedAlphaVisitScheduleValid
        (cachedInputMachine machine) alpha scheduled := hreflect.1
    have haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
        (cachedInputMachine machine) input alpha scheduled := hreflect.2
    let hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled :=
      allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
        (cachedInputMachine machine) input alpha scheduled haccepted
    have hscheduleCheck : timedAlphaVisitScheduleCheck
        (cachedInputMachine machine) alpha scheduled = true :=
      (timedAlphaVisitScheduleCheck_eq_true_iff
        (cachedInputMachine machine) alpha scheduled).2 hvalid
    have hmonotoneCheck : timedAlphaScheduledVisitsInputMonotoneCheck
        scheduled = true :=
      (timedAlphaScheduledVisitsInputMonotoneCheck_eq_true_iff scheduled).2
        hmonotone
    unfold
      compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
    rw [dif_pos hscheduleCheck, dif_pos hmonotoneCheck]
    have hpreserve :=
      compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRolling_eval_eq_timedAlphaFold_of_acceptedFromBlank_canonical
        machine input alpha scheduled haccepted
    dsimp only at hpreserve
    rw [hpreserve]
    exact hcheck.2

end OneTapeMagnification
end Frontier
end Pnp4
