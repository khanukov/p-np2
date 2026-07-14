import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedAllBlocksReadOnce
import Pnp4.Frontier.OneTapeMagnification.ExecutableTimedAlphaQueryOrder

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Guarding an adaptive program by a duplicate-free master order

An interval-only guard prevents a local replay from querying beyond its
advertised exit, but proving cross-block read-once still requires tracking
where the execution sits in the stably grouped master order.  This file makes
that cursor explicit.  It costs only a factor `master.length + 1` in width.

The wrapper exposes a base-program query only when it is exactly the next
coordinate of `master`.  A mismatch receives `none` and cannot create a real
query.  Consequently every wrapped trace is a prefix of `master`, on every
Boolean input and independently of base-program correctness.

For the finite cached all-block compiler, schedule geometry proves that the
master is duplicate-free.  Completeness is preserved whenever the unguarded
accepted execution follows that master order; the final transfer theorem
states this exact remaining operational premise.
-/

namespace LayeredQueryProgram

/-- Cursor into a finite master query order, including the exhausted
position at `master.length`. -/
abbrev MasterCursor {n : Nat} (master : List (Fin n)) :=
  Fin (master.length + 1)

/-- Query named by the current master cursor, if it is not exhausted. -/
def masterCursorQuery? {n : Nat} (master : List (Fin n))
    (cursor : MasterCursor master) : Option (Fin n) :=
  if hcursor : cursor.val < master.length then
    some (master.get ⟨cursor.val, hcursor⟩)
  else
    none

/-- Advance a nonexhausted master cursor by one; leave an exhausted cursor
unchanged. -/
def advanceMasterCursor {n : Nat} (master : List (Fin n))
    (cursor : MasterCursor master) : MasterCursor master :=
  if hcursor : cursor.val < master.length then
    ⟨cursor.val + 1, by omega⟩
  else
    cursor

/-- Keep a base query only when it is exactly the current master query. -/
def masterGuardedQuery? {n L : Nat}
    (program : LayeredQueryProgram n L) (master : List (Fin n))
    (layer : Fin L) (state : program.State × MasterCursor master) :
    Option (Fin n) :=
  match program.query? layer state.1, masterCursorQuery? master state.2 with
  | some actual, some expected =>
      if actual = expected then some actual else none
  | _, _ => none

/-- A guarded transition delegates an allowed answer to the base program and
advances the master cursor.  A blocked query supplies `none` and retains the
cursor. -/
def masterGuardedNext {n L : Nat}
    (program : LayeredQueryProgram n L) (master : List (Fin n))
    (layer : Fin L) (state : program.State × MasterCursor master)
    (answer : Option Bool) : program.State × MasterCursor master :=
  match masterGuardedQuery? program master layer state with
  | some _ =>
      (program.next layer state.1 answer,
        advanceMasterCursor master state.2)
  | none =>
      (program.next layer state.1 none, state.2)

/-- Add a finite master-order cursor to an arbitrary adaptive layered
program. -/
def guardByMasterOrder {n L : Nat}
    (program : LayeredQueryProgram n L) (master : List (Fin n)) :
    LayeredQueryProgram n L where
  State := program.State × MasterCursor master
  stateFintype := by
    letI := program.stateFintype
    infer_instance
  start := (program.start, ⟨0, Nat.zero_lt_succ _⟩)
  query? := masterGuardedQuery? program master
  next := masterGuardedNext program master
  output := fun state => program.output state.1

theorem masterGuardedQuery?_eq_some_iff
    {n L : Nat} (program : LayeredQueryProgram n L)
    (master : List (Fin n)) (layer : Fin L)
    (state : program.State) (cursor : MasterCursor master)
    (query : Fin n) :
    masterGuardedQuery? program master layer (state, cursor) = some query ↔
      ∃ hcursor : cursor.val < master.length,
        program.query? layer state = some query ∧
          master.get ⟨cursor.val, hcursor⟩ = query := by
  by_cases hcursor : cursor.val < master.length
  · cases hbase : program.query? layer state with
    | none =>
        simp [masterGuardedQuery?, masterCursorQuery?, hcursor, hbase]
    | some actual =>
        simp only [masterGuardedQuery?,
          masterCursorQuery?, dif_pos hcursor, hbase]
        by_cases heq : actual = master.get ⟨cursor.val, hcursor⟩
        · rw [if_pos heq]
          constructor
          · intro houtput
            have hactual : actual = query := Option.some.inj houtput
            refine ⟨hcursor, ?_, ?_⟩
            · exact congrArg some hactual
            · exact heq.symm.trans hactual
          · rintro ⟨otherCursor, hprogram, hget⟩
            have hget' : master.get ⟨cursor.val, hcursor⟩ = query := by
              simpa using hget
            exact congrArg some (heq.trans hget')
        · rw [if_neg heq]
          constructor
          · intro himpossible
            contradiction
          · rintro ⟨otherCursor, hprogram, hget⟩
            have hactual : actual = query := by
              exact Option.some.inj hprogram
            have hget' : master.get ⟨cursor.val, hcursor⟩ = query := by
              simpa using hget
            exact (heq (hactual.trans hget'.symm)).elim
  · simp only [masterGuardedQuery?,
      masterCursorQuery?, dif_neg hcursor]
    constructor
    · intro himpossible
      cases hbase : program.query? layer state <;>
        simp [hbase] at himpossible
    · rintro ⟨otherCursor, _, _⟩
      exact (hcursor otherCursor).elim

@[simp]
theorem advanceMasterCursor_val_of_lt
    {n : Nat} (master : List (Fin n)) (cursor : MasterCursor master)
    (hcursor : cursor.val < master.length) :
    (advanceMasterCursor master cursor).val = cursor.val + 1 := by
  simp [advanceMasterCursor, hcursor]

private theorem take_succ_eq_take_append_get
    {α : Type} (items : List α) (index : Nat)
    (hindex : index < items.length) :
    items.take (index + 1) =
      items.take index ++ [items.get ⟨index, hindex⟩] := by
  induction items generalizing index with
  | nil => simp at hindex
  | cons item rest ih =>
      cases index with
      | zero => simp
      | succ index =>
          simp only [List.take_succ_cons, List.get_cons_succ,
            List.cons_append, List.cons.injEq, true_and]
          exact ih index (by simpa using hindex)

/-- At every prefix, the guarded trace is exactly the master prefix ending at
the live master cursor. -/
theorem guardByMasterOrder_executePrefix_trace_eq_take_cursor
    {n L : Nat} (program : LayeredQueryProgram n L)
    (master : List (Fin n)) (input : Fin n → Bool)
    (k : Nat) (hk : k ≤ L) :
    let executed := (guardByMasterOrder program master).executePrefix
      input k hk
    executed.2 = master.take executed.1.2.val := by
  induction k with
  | zero =>
      simp [LayeredQueryProgram.executePrefix, guardByMasterOrder]
  | succ k ih =>
      let guarded := guardByMasterOrder program master
      let previous := guarded.executePrefix input k (by omega)
      let layer : Fin L := ⟨k, by omega⟩
      let query := guarded.query? layer previous.1
      have hprevious : previous.2 = master.take previous.1.2.val := by
        simpa [guarded, previous] using ih (by omega)
      simp only [LayeredQueryProgram.executePrefix]
      change previous.2 ++ query.toList =
        master.take
          (guarded.next layer previous.1 (query.map input)).2.val
      cases hquery : query with
      | none =>
          have hguardNone :
              masterGuardedQuery? program master layer previous.1 = none := by
            simpa [guarded, query] using hquery
          have hnext :
              (guarded.next layer previous.1 none).2 =
                previous.1.2 := by
            simp [guarded, guardByMasterOrder, masterGuardedNext,
              hguardNone]
          simp only [Option.toList_none, List.append_nil, Option.map_none]
          rw [hnext, hprevious]
      | some coordinate =>
          have hguard : masterGuardedQuery? program master layer previous.1 =
              some coordinate := by
            simpa [guarded, query] using hquery
          rcases (masterGuardedQuery?_eq_some_iff program master layer
              previous.1.1 previous.1.2 coordinate).mp hguard with
            ⟨hcursor, _hbase, hget⟩
          have htake := take_succ_eq_take_append_get master
            previous.1.2.val hcursor
          simp only [hget] at htake
          have hnextVal :
              (guarded.next layer previous.1
                (some (input coordinate))).2.val =
                previous.1.2.val + 1 := by
            simp [guarded, guardByMasterOrder, masterGuardedNext,
              hguard,
              advanceMasterCursor_val_of_lt master previous.1.2 hcursor]
          simp only [Option.toList_some, Option.map_some]
          rw [hnextVal, hprevious]
          exact htake.symm

/-- Every guarded trace is a prefix, hence a sublist, of its master order. -/
theorem guardByMasterOrder_queryTrace_sublist
    {n L : Nat} (program : LayeredQueryProgram n L)
    (master : List (Fin n)) (input : Fin n → Bool) :
    List.Sublist ((guardByMasterOrder program master).queryTrace input)
      master := by
  rw [LayeredQueryProgram.queryTrace,
    guardByMasterOrder_executePrefix_trace_eq_take_cursor]
  exact List.take_sublist _ _

/-- Guarding by a duplicate-free master order makes every adaptive execution
read-once. -/
theorem guardByMasterOrder_isReadOnce
    {n L : Nat} (program : LayeredQueryProgram n L)
    (master : List (Fin n)) (hmaster : master.Nodup) :
    (guardByMasterOrder program master).IsReadOnce := by
  intro input
  exact hmaster.sublist
    (guardByMasterOrder_queryTrace_sublist program master input)

/-- Exact width cost of the master cursor. -/
@[simp]
theorem guardByMasterOrder_width
    {n L : Nat} (program : LayeredQueryProgram n L)
    (master : List (Fin n)) :
    (guardByMasterOrder program master).width =
      program.width * (master.length + 1) := by
  simp [guardByMasterOrder, LayeredQueryProgram.width,
    Fintype.card_prod]

/-- Exact input-specific compatibility needed for semantic preservation.
Every real base query must be the next coordinate after the base prefix in
the master order.  Silent base layers impose no condition. -/
def ExecutionQueriesFollowMaster
    {n L : Nat} (program : LayeredQueryProgram n L)
    (master : List (Fin n)) (input : Fin n → Bool) : Prop :=
  ∀ (k : Nat) (hk : k < L),
    let previous := program.executePrefix input k (Nat.le_of_lt hk)
    match program.query? ⟨k, hk⟩ previous.1 with
    | none => True
    | some query =>
        ∃ hlength : previous.2.length < master.length,
          master.get ⟨previous.2.length, hlength⟩ = query

/-- Under exact master compatibility, the guarded execution simulates the
base state and trace at every layer; its cursor is the trace length. -/
theorem guardByMasterOrder_executePrefix_simulates_of_follows
    {n L : Nat} (program : LayeredQueryProgram n L)
    (master : List (Fin n)) (input : Fin n → Bool)
    (hfollows : ExecutionQueriesFollowMaster program master input)
    (k : Nat) (hk : k ≤ L) :
    let base := program.executePrefix input k hk
    let guarded := (guardByMasterOrder program master).executePrefix input k hk
    guarded.1.1 = base.1 ∧
      guarded.1.2.val = base.2.length ∧
      guarded.2 = base.2 := by
  induction k with
  | zero =>
      simp [LayeredQueryProgram.executePrefix, guardByMasterOrder]
  | succ k ih =>
      let guardedProgram := guardByMasterOrder program master
      let basePrevious := program.executePrefix input k (by omega)
      let guardedPrevious := guardedProgram.executePrefix input k (by omega)
      let layer : Fin L := ⟨k, by omega⟩
      let baseQuery := program.query? layer basePrevious.1
      have hprevious := ih (by omega)
      dsimp only at hprevious
      have hstate : guardedPrevious.1.1 = basePrevious.1 := by
        simpa [guardedPrevious, guardedProgram, basePrevious] using hprevious.1
      have hcursor : guardedPrevious.1.2.val = basePrevious.2.length := by
        simpa [guardedPrevious, guardedProgram, basePrevious] using
          hprevious.2.1
      have htrace : guardedPrevious.2 = basePrevious.2 := by
        simpa [guardedPrevious, guardedProgram, basePrevious] using
          hprevious.2.2
      have hfollow := hfollows k (by omega)
      dsimp only at hfollow
      change (match baseQuery with
        | none => True
        | some query =>
            ∃ hlength : basePrevious.2.length < master.length,
              master.get ⟨basePrevious.2.length, hlength⟩ = query) at hfollow
      cases hbaseQuery : baseQuery with
      | none =>
          have hguardQuery :
              masterGuardedQuery? program master layer guardedPrevious.1 =
                none := by
            simp [masterGuardedQuery?, hstate, baseQuery, hbaseQuery]
          have hbaseQueryStep :
              program.query? ⟨k, by omega⟩
                (program.executePrefix input k (by omega)).1 = none := by
            simpa [baseQuery, basePrevious, layer] using hbaseQuery
          have hguardQueryStep :
              masterGuardedQuery? program master ⟨k, by omega⟩
                ((guardByMasterOrder program master).executePrefix
                  input k (by omega)).1 = none := by
            simpa [guardedProgram, guardedPrevious, layer] using hguardQuery
          have hguardedQueryStep :
              (guardByMasterOrder program master).query? ⟨k, by omega⟩
                ((guardByMasterOrder program master).executePrefix
                  input k (by omega)).1 = none := by
            exact hguardQueryStep
          have hguardedNextStep :
              (guardByMasterOrder program master).next ⟨k, by omega⟩
                ((guardByMasterOrder program master).executePrefix
                  input k (by omega)).1 none =
                (program.next ⟨k, by omega⟩
                    ((guardByMasterOrder program master).executePrefix
                      input k (by omega)).1.1 none,
                  ((guardByMasterOrder program master).executePrefix
                    input k (by omega)).1.2) := by
            change masterGuardedNext program master _ _ none = _
            simp [masterGuardedNext, hguardQueryStep]
          simp only [LayeredQueryProgram.executePrefix]
          rw [hguardedQueryStep, hbaseQueryStep]
          simp only [Option.map_none, Option.toList_none, List.append_nil]
          rw [hguardedNextStep]
          constructor
          · exact congrArg
              (fun state => program.next ⟨k, by omega⟩ state none)
              hprevious.1
          · exact hprevious.2
      | some query =>
          simp [hbaseQuery] at hfollow
          rcases hfollow with ⟨hlength, hget⟩
          have hcursorLength : guardedPrevious.1.2.val < master.length := by
            simpa [hcursor] using hlength
          have hmasterQuery :
              masterCursorQuery? master guardedPrevious.1.2 = some query := by
            rw [masterCursorQuery?, dif_pos hcursorLength]
            apply congrArg some
            simpa [hcursor] using hget
          have hguardQuery :
              masterGuardedQuery? program master layer guardedPrevious.1 =
                some query := by
            simp [masterGuardedQuery?, hstate, baseQuery, hbaseQuery,
              hmasterQuery]
          have hbaseQueryStep :
              program.query? ⟨k, by omega⟩
                (program.executePrefix input k (by omega)).1 =
                  some query := by
            simpa [baseQuery, basePrevious, layer] using hbaseQuery
          have hguardQueryStep :
              masterGuardedQuery? program master ⟨k, by omega⟩
                ((guardByMasterOrder program master).executePrefix
                  input k (by omega)).1 = some query := by
            simpa [guardedProgram, guardedPrevious, layer] using hguardQuery
          have hguardedQueryStep :
              (guardByMasterOrder program master).query? ⟨k, by omega⟩
                ((guardByMasterOrder program master).executePrefix
                  input k (by omega)).1 = some query := by
            exact hguardQueryStep
          have hcursorLengthStep :
              (((guardByMasterOrder program master).executePrefix
                input k (by omega)).1.2).val < master.length := by
            simpa [guardedProgram, guardedPrevious] using hcursorLength
          have hguardedNextStep :
              (guardByMasterOrder program master).next ⟨k, by omega⟩
                ((guardByMasterOrder program master).executePrefix
                  input k (by omega)).1 (some (input query)) =
                (program.next ⟨k, by omega⟩
                    ((guardByMasterOrder program master).executePrefix
                      input k (by omega)).1.1 (some (input query)),
                  advanceMasterCursor master
                    ((guardByMasterOrder program master).executePrefix
                      input k (by omega)).1.2) := by
            change masterGuardedNext program master _ _ _ = _
            simp [masterGuardedNext, hguardQueryStep]
          simp only [LayeredQueryProgram.executePrefix]
          rw [hguardedQueryStep, hbaseQueryStep]
          simp only [Option.map_some, Option.toList_some]
          rw [hguardedNextStep]
          constructor
          · exact congrArg
              (fun state => program.next ⟨k, by omega⟩ state
                (some (input query))) hprevious.1
          · constructor
            · rw [advanceMasterCursor_val_of_lt master _ hcursorLengthStep,
                hprevious.2.1]
              simp
            · rw [hprevious.2.2]

/-- Semantic preservation on every input whose base execution follows the
master order exactly. -/
theorem guardByMasterOrder_eval_eq_of_follows
    {n L : Nat} (program : LayeredQueryProgram n L)
    (master : List (Fin n)) (input : Fin n → Bool)
    (hfollows : ExecutionQueriesFollowMaster program master input) :
    (guardByMasterOrder program master).eval input = program.eval input := by
  have hfinal := guardByMasterOrder_executePrefix_simulates_of_follows
    program master input hfollows L le_rfl
  simpa [LayeredQueryProgram.eval, LayeredQueryProgram.finalState,
    guardByMasterOrder] using congrArg program.output hfinal.1

end LayeredQueryProgram

/-! ## Guarded finite cached all-block compiler -/

/-- Schedule-specialized outer program guarded by its clipped stable-grouped
master query order. -/
def compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocks
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
  LayeredQueryProgram.guardByMasterOrder
    (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks
      machine alpha scheduled)
    (finiteCachedTimedAlphaScheduleMasterQueryOrder
      scheduled hmonotone)

/-- Schedule geometry now suffices unconditionally for global read-once: all
off-master adaptive queries are suppressed by the finite cursor guard. -/
theorem compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocks_isReadOnce
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hchained : TimedAlphaScheduledVisitsChained scheduled)
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled) :
    (compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocks
      (n := n) machine alpha scheduled hmonotone).IsReadOnce := by
  apply LayeredQueryProgram.guardByMasterOrder_isReadOnce
  exact finiteCachedTimedAlphaScheduleMasterQueryOrder_nodup
    (n := n) scheduled hchained hmonotone

/-- Exact guarded width: one finite master cursor multiplies the existing
outer width by at most the master-order length plus one. -/
@[simp]
theorem compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocks_width
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled) :
    (compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocks
      (n := n) machine alpha scheduled hmonotone).width =
      (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks
        (n := n) machine alpha scheduled).width *
        (finiteCachedTimedAlphaScheduleMasterQueryOrder
          (n := n) scheduled hmonotone).length.succ := by
  exact LayeredQueryProgram.guardByMasterOrder_width _ _

/-! ## Total checked wrapper -/

/-- Total guarded compiler.  Schedule validity supplies cross-visit chaining,
and the separate endpoint check supplies the monotone half-open intervals used
to build the master order.  Any failed static check produces a query-free
constant rejection program. -/
def compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksTotal
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b)) :
    LayeredQueryProgram n
      (finiteCachedAllBlocksFuel
        (fun block => timedAlphaBlockVisits block scheduled)) := by
  letI : DecidableEq (cachedInputMachine machine).State :=
    cachedInputStateDecidableEq machine
  exact
    if hschedule : timedAlphaVisitScheduleCheck
        (cachedInputMachine machine) alpha scheduled = true then
      if hmonotone :
          timedAlphaScheduledVisitsInputMonotoneCheck scheduled = true then
        compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocks
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

/-- The checked compiler is globally read-once for every supplied schedule and
every Boolean input.  This theorem has no semantic correctness premise. -/
theorem compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksTotal_isReadOnce
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b)) :
    (compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksTotal
      (n := n) machine alpha scheduled).IsReadOnce := by
  letI : DecidableEq (cachedInputMachine machine).State :=
    cachedInputStateDecidableEq machine
  unfold compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksTotal
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
      obtain ⟨_hword, _finalCursor, _visitsSoFar, _hfold, _hfinish,
        hchained⟩ := hschedule
      exact
        compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocks_isReadOnce
          machine alpha scheduled hchained hmonotone
    · exact LayeredQueryProgram.constantReject_isReadOnce _ _
  · exact LayeredQueryProgram.constantReject_isReadOnce _ _

/-- Schedule-specialized spelling of the exact operational premise under
which the guard is semantically invisible on one input. -/
def FiniteCachedTimedAlphaScheduleExecutionQueriesFollowMaster
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled)
    (input : Fin n → Bool) : Prop :=
  LayeredQueryProgram.ExecutionQueriesFollowMaster
    (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks
      machine alpha scheduled)
    (finiteCachedTimedAlphaScheduleMasterQueryOrder
      scheduled hmonotone)
    input

/-- On a statically accepted schedule, the total wrapper has exactly the base
program's output whenever the base execution follows the advertised master
order. -/
theorem compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksTotal_eval_eq_base_of_follows
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (input : Fin n → Bool)
    (hschedule : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha scheduled)
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled)
    (hfollows : FiniteCachedTimedAlphaScheduleExecutionQueriesFollowMaster
      machine alpha scheduled hmonotone input) :
    (compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksTotal
        machine alpha scheduled).eval input =
      (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks
        machine alpha scheduled).eval input := by
  letI : DecidableEq (cachedInputMachine machine).State :=
    cachedInputStateDecidableEq machine
  have hscheduleCheck : timedAlphaVisitScheduleCheck
      (cachedInputMachine machine) alpha scheduled = true :=
    (timedAlphaVisitScheduleCheck_eq_true_iff
      (cachedInputMachine machine) alpha scheduled).2 hschedule
  have hmonotoneCheck :
      timedAlphaScheduledVisitsInputMonotoneCheck scheduled = true :=
    (timedAlphaScheduledVisitsInputMonotoneCheck_eq_true_iff scheduled).2
      hmonotone
  unfold compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksTotal
  rw [dif_pos hscheduleCheck, dif_pos hmonotoneCheck]
  exact LayeredQueryProgram.guardByMasterOrder_eval_eq_of_follows
    (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks
      machine alpha scheduled)
    (finiteCachedTimedAlphaScheduleMasterQueryOrder
      scheduled hmonotone)
    input hfollows

/-- Accepted all-block schedules retain completeness through the total guard,
modulo the two already explicit operational interfaces: outer reflection and
master-order following on the concrete input. -/
theorem compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksTotal_eval_eq_true_of_accepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    [DecidableEq (cachedInputMachine machine).State]
    (semanticInput : List Bool) {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (input : Fin n → Bool)
    (hschedule : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha scheduled)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      (cachedInputMachine machine) semanticInput alpha scheduled)
    (hreflect : FiniteCachedTimedAlphaScheduleAllBlocksReflects machine
      semanticInput alpha scheduled input)
    (hfollows :
      let hmonotone :=
        allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
          (cachedInputMachine machine) semanticInput alpha scheduled haccepted
      FiniteCachedTimedAlphaScheduleExecutionQueriesFollowMaster
        machine alpha scheduled hmonotone input) :
    (compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksTotal
      machine alpha scheduled).eval input = true := by
  let hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled :=
    allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
      (cachedInputMachine machine) semanticInput alpha scheduled haccepted
  have hallCheck : timedAlphaAllBlockVisitsCheckFromBlank
      (cachedInputMachine machine) semanticInput alpha scheduled = true :=
    (timedAlphaAllBlockVisitsCheckFromBlank_eq_true_iff
      (cachedInputMachine machine) semanticInput alpha scheduled).2 haccepted
  have hbase :
      (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks
        machine alpha scheduled).eval input = true := by
    have hreflect' :
        (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks
          machine alpha scheduled).eval input =
        timedAlphaAllBlockVisitsCheckFromBlank
          (cachedInputMachine machine) semanticInput alpha scheduled := by
      simpa only [FiniteCachedTimedAlphaScheduleAllBlocksReflects] using
        hreflect
    exact hreflect'.trans hallCheck
  rw [compileMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksTotal_eval_eq_base_of_follows
    machine alpha scheduled input hschedule hmonotone]
  · exact hbase
  · simpa [hmonotone] using hfollows

end OneTapeMagnification
end Frontier
end Pnp4
