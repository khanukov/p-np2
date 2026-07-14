import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedVisitStreamingVerifier

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Adaptive collapse of silent verifier steps

`compileFixedOrder` deliberately queries a pre-supplied permutation.  The
base `LayeredQueryProgram` model is more general: its query coordinate may
depend on the live state.  This file uses that capability directly.

At every layer the compiler closes all currently available silent steps,
asks `queryIndex?` for the coordinate requested by the closed state, and
either supplies that answer while spending one unit of fuel or retains the
closed state.  The executable definitions contain no actual-run semantic
objects.  The live carrier remains exactly `State × Fin (H+1)`.
-/

namespace FiniteStreamingVerifier

variable {Symbol : Type}

/-- Query exposed by a silently closed fueled state.  The external index
selector is consulted only at a live, positive-fuel input request. -/
def adaptiveQuery? (verifier : FiniteStreamingVerifier Symbol)
    {H n : Nat} (queryIndex? : verifier.State → Option (Fin n))
    (state : verifier.FueledState H) : Option (Fin n) :=
  let closed := verifier.silentClosure state
  if 0 < closed.2.val && !verifier.halted closed.1 &&
      verifier.requestsInput closed.1 then
    queryIndex? closed.1
  else
    none

/-- One adaptive layer transition.  `answer = none` retains the silent
closure.  A real answer is consumed exactly when the corresponding adaptive
query exists. -/
def adaptiveNext (verifier : FiniteStreamingVerifier Symbol)
    {H n : Nat} (encode : Bool → Symbol)
    (queryIndex? : verifier.State → Option (Fin n))
    (state : verifier.FueledState H) (answer : Option Bool) :
    verifier.FueledState H :=
  let closed := verifier.silentClosure state
  match verifier.adaptiveQuery? queryIndex? state, answer with
  | some _, some bit =>
      (verifier.step closed.1 (some (encode bit)), spendOne closed.2)
  | _, _ => closed

/-- State transformer induced by one adaptive layer on a concrete Boolean
input. -/
def adaptiveInputStep (verifier : FiniteStreamingVerifier Symbol)
    {H n : Nat} (encode : Bool → Symbol)
    (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) (state : verifier.FueledState H) :
    verifier.FueledState H :=
  let query := verifier.adaptiveQuery? queryIndex? state
  verifier.adaptiveNext encode queryIndex? state (query.map input)

/-- Iterate the adaptive state transformer from an arbitrary fueled state. -/
def runAdaptiveFrom (verifier : FiniteStreamingVerifier Symbol)
    {H n : Nat} (encode : Bool → Symbol)
    (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) : Nat → verifier.FueledState H →
      verifier.FueledState H
  | 0, state => state
  | layers + 1, state =>
      verifier.adaptiveInputStep encode queryIndex? input
        (verifier.runAdaptiveFrom encode queryIndex? input layers state)

/-- Run all `H` adaptive layers from the canonical initial fueled state. -/
def runAdaptive (verifier : FiniteStreamingVerifier Symbol)
    (H : Nat) {n : Nat} (encode : Bool → Symbol)
    (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) : verifier.FueledState H :=
  verifier.runAdaptiveFrom encode queryIndex? input H
    (verifier.initialFueledState H)

/-- Compile a finite streaming verifier to `H` adaptive query layers. -/
def compileAdaptive (verifier : FiniteStreamingVerifier Symbol)
    (H n : Nat) (encode : Bool → Symbol) (endSymbol : Symbol)
    (queryIndex? : verifier.State → Option (Fin n)) :
    LayeredQueryProgram n H where
  State := verifier.FueledState H
  stateFintype := inferInstance
  start := verifier.initialFueledState H
  query? := fun _ state => verifier.adaptiveQuery? queryIndex? state
  next := fun _ state answer =>
    verifier.adaptiveNext encode queryIndex? state answer
  output := fun state =>
    verifier.accept (verifier.finishWithEndSymbol endSymbol state)

/-- Exact characterization of a real adaptive query. -/
theorem adaptiveQuery?_eq_some_iff
    (verifier : FiniteStreamingVerifier Symbol) {H n : Nat}
    (queryIndex? : verifier.State → Option (Fin n))
    (state : verifier.FueledState H) (index : Fin n) :
    verifier.adaptiveQuery? queryIndex? state = some index ↔
      let closed := verifier.silentClosure state
      0 < closed.2.val ∧
        verifier.halted closed.1 = false ∧
        verifier.requestsInput closed.1 = true ∧
        queryIndex? closed.1 = some index := by
  dsimp only [adaptiveQuery?]
  by_cases hactive :
      (decide (0 < (verifier.silentClosure state).2.val) &&
        !verifier.halted (verifier.silentClosure state).1 &&
        verifier.requestsInput (verifier.silentClosure state).1) = true
  · rw [if_pos hactive]
    have hparts :
        0 < (verifier.silentClosure state).2.val ∧
          verifier.halted (verifier.silentClosure state).1 = false ∧
          verifier.requestsInput (verifier.silentClosure state).1 = true := by
      have hpairs :
          (0 < (verifier.silentClosure state).2.val ∧
            verifier.halted (verifier.silentClosure state).1 = false) ∧
            verifier.requestsInput (verifier.silentClosure state).1 = true := by
        simpa [Bool.and_eq_true] using hactive
      exact ⟨hpairs.1.1, hpairs.1.2, hpairs.2⟩
    constructor
    · intro hquery
      exact ⟨hparts.1, hparts.2.1, hparts.2.2, hquery⟩
    · rintro ⟨_, _, _, hquery⟩
      exact hquery
  · rw [if_neg hactive]
    constructor
    · intro hquery
      contradiction
    · rintro ⟨hpositive, hhalt, hrequest, _⟩
      exfalso
      apply hactive
      simp [hpositive, hhalt, hrequest]

/-- The program query at every layer is exactly the query selected from the
silent closure; layer number plays no role. -/
theorem compileAdaptive_query?
    (verifier : FiniteStreamingVerifier Symbol) (H n : Nat)
    (encode : Bool → Symbol) (endSymbol : Symbol)
    (queryIndex? : verifier.State → Option (Fin n))
    (layer : Fin H) (state : verifier.FueledState H) :
    (verifier.compileAdaptive H n encode endSymbol queryIndex?).query?
        layer state =
      verifier.adaptiveQuery? queryIndex? state := rfl

/-- Exact state equation for every compiled prefix. -/
theorem compileAdaptive_executePrefix_state
    (verifier : FiniteStreamingVerifier Symbol) (H n : Nat)
    (encode : Bool → Symbol) (endSymbol : Symbol)
    (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) (k : Nat) (hk : k ≤ H) :
    ((verifier.compileAdaptive H n encode endSymbol queryIndex?).executePrefix
      input k hk).1 =
      verifier.runAdaptiveFrom encode queryIndex? input k
        (verifier.initialFueledState H) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [LayeredQueryProgram.executePrefix]
      rw [ih (by omega)]
      rfl

/-- The final live state is exactly the adaptive `H`-layer run. -/
theorem compileAdaptive_finalState
    (verifier : FiniteStreamingVerifier Symbol) (H n : Nat)
    (encode : Bool → Symbol) (endSymbol : Symbol)
    (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) :
    (verifier.compileAdaptive H n encode endSymbol queryIndex?).finalState
        input =
      verifier.runAdaptive H encode queryIndex? input := by
  simpa [LayeredQueryProgram.finalState, runAdaptive] using
    verifier.compileAdaptive_executePrefix_state H n encode endSymbol
      queryIndex? input H le_rfl

/-- Exact semantic equation for adaptive compilation. -/
theorem compileAdaptive_eval
    (verifier : FiniteStreamingVerifier Symbol) (H n : Nat)
    (encode : Bool → Symbol) (endSymbol : Symbol)
    (queryIndex? : verifier.State → Option (Fin n))
    (input : Fin n → Bool) :
    (verifier.compileAdaptive H n encode endSymbol queryIndex?).eval input =
      verifier.accept
        (verifier.finishWithEndSymbol endSymbol
          (verifier.runAdaptive H encode queryIndex? input)) := by
  rw [LayeredQueryProgram.eval, verifier.compileAdaptive_finalState]
  rfl

/-- Adaptive query selection costs no live width. -/
@[simp]
theorem compileAdaptive_width
    (verifier : FiniteStreamingVerifier Symbol) (H n : Nat)
    (encode : Bool → Symbol) (endSymbol : Symbol)
    (queryIndex? : verifier.State → Option (Fin n)) :
    (verifier.compileAdaptive H n encode endSymbol queryIndex?).width =
      Fintype.card verifier.State * (H + 1) := by
  simp [compileAdaptive, LayeredQueryProgram.width]

/-- State-level invariant sufficient for read-once: at every prefix, a newly
exposed query is strictly larger than every earlier query in that execution.
This is intentionally a premise, not an unproved property of arbitrary
adaptive verifiers. -/
def FreshQueriesStrictlyIncrease {n L : Nat}
    (program : LayeredQueryProgram n L) : Prop :=
  ∀ (input : Fin n → Bool) (k : Nat) (hk : k < L)
    (prior current : Fin n),
    prior ∈ (program.executePrefix input k (Nat.le_of_lt hk)).2 →
    program.query? ⟨k, hk⟩
        (program.executePrefix input k (Nat.le_of_lt hk)).1 = some current →
    prior < current

/-- The strict-prefix invariant implies read-once for any adaptive layered
query program. -/
theorem isReadOnce_of_freshQueriesStrictlyIncrease
    {n L : Nat} (program : LayeredQueryProgram n L)
    (hstrict : FreshQueriesStrictlyIncrease program) :
    program.IsReadOnce := by
  intro input
  unfold LayeredQueryProgram.queryTrace
  have hprefix : ∀ (k : Nat) (hk : k ≤ L),
      (program.executePrefix input k hk).2.Nodup := by
    intro k
    induction k with
    | zero =>
        intro hk
        simp [LayeredQueryProgram.executePrefix]
    | succ k ih =>
        intro hk
        simp only [LayeredQueryProgram.executePrefix]
        let previous := program.executePrefix input k (by omega)
        let layer : Fin L := ⟨k, by omega⟩
        let query := program.query? layer previous.1
        have hprev : previous.2.Nodup := ih (by omega)
        cases hquery : query with
        | none => simpa [previous, layer, query, hquery] using hprev
        | some current =>
            have hnotmem : current ∉ previous.2 := by
              intro hmem
              have hlt := hstrict input k (by omega) current current
                (by simpa [previous] using hmem)
                (by simpa [previous, layer, query] using hquery)
              exact (lt_irrefl current) hlt
            change (previous.2 ++ query.toList).Nodup
            rw [hquery]
            simpa [List.concat_eq_append] using
              (List.Nodup.concat hnotmem hprev)
  exact hprefix L le_rfl

end FiniteStreamingVerifier

/-- The adaptive coordinate selector for a cached visit: a running phase
names precisely its current in-range input-head position. -/
def finiteCachedVisitAdaptiveQueryIndex?
    (machine : DeterministicMachine) (n : Nat) {H w : Nat} :
    FiniteCachedVisitStreamingState
        (cachedInputMachine machine).State H w → Option (Fin n)
  | .running _ live =>
      if hhead : live.inputHead.val < n then
        some ⟨live.inputHead.val, hhead⟩
      else
        none
  | .completed _ => none
  | .rejected _ => none

/-- Exact coordinate characterization of the cached-visit selector. -/
theorem finiteCachedVisitAdaptiveQueryIndex?_running_eq_some_iff
    (machine : DeterministicMachine) (n : Nat) {H w : Nat}
    (remaining : Fin (H + 1))
    (live : LocalReplayState (cachedInputMachine machine).State H w)
    (index : Fin n) :
    finiteCachedVisitAdaptiveQueryIndex? machine n
        (.running remaining live) = some index ↔
      live.inputHead.val < n ∧ index.val = live.inputHead.val := by
  by_cases hhead : live.inputHead.val < n
  · rw [finiteCachedVisitAdaptiveQueryIndex?, dif_pos hhead]
    constructor
    · intro heq
      have hfin : (⟨live.inputHead.val, hhead⟩ : Fin n) = index :=
        Option.some.inj heq
      exact ⟨hhead, (congrArg (fun i : Fin n => i.val) hfin).symm⟩
    · rintro ⟨_, hval⟩
      apply congrArg some
      apply Fin.ext
      exact hval.symm
  · rw [finiteCachedVisitAdaptiveQueryIndex?, dif_neg hhead]
    simp only [reduceCtorEq, false_iff]
    exact fun h => hhead h.1

/-- A selector result exists exactly for a running phase, and its coordinate
is exactly that phase's current in-range input head. -/
theorem finiteCachedVisitAdaptiveQueryIndex?_eq_some_iff
    (machine : DeterministicMachine) (n : Nat) {H w : Nat}
    (phase : FiniteCachedVisitStreamingState
      (cachedInputMachine machine).State H w)
    (index : Fin n) :
    finiteCachedVisitAdaptiveQueryIndex? machine n phase = some index ↔
      ∃ (remaining : Fin (H + 1))
          (live : LocalReplayState
            (cachedInputMachine machine).State H w),
        phase = .running remaining live ∧
          live.inputHead.val < n ∧ index.val = live.inputHead.val := by
  cases phase with
  | running remaining live =>
      rw [finiteCachedVisitAdaptiveQueryIndex?_running_eq_some_iff]
      constructor
      · rintro ⟨hhead, hindex⟩
        exact ⟨remaining, live, rfl, hhead, hindex⟩
      · rintro ⟨otherRemaining, otherLive, heq, hhead, hindex⟩
        cases heq
        exact ⟨hhead, hindex⟩
  | completed final =>
      simp [finiteCachedVisitAdaptiveQueryIndex?]
  | rejected failure =>
      simp [finiteCachedVisitAdaptiveQueryIndex?]

/-- Adaptive compiler for one finite cached fixed-alpha visit.  Its
executable data depend only on the finite verifier and the current live input
head, never on an actual run or semantic unread trace. -/
def compileAdaptiveFiniteCachedFixedAlphaVisit
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
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
    LayeredQueryProgram n T :=
  let verifier := finiteCachedFixedAlphaVisitStreamingVerifier machine n
    alpha block visit carried hentry
  verifier.compileAdaptive T n (fun bit => .bit bit) .rightEnd
    (finiteCachedVisitAdaptiveQueryIndex? machine n)

/-- Exact query-index characterization for the compiled cached visit.  A
layer queries precisely when silent closure stops at a positive-fuel live
request whose running phase has an in-range head; the queried coordinate is
that head. -/
theorem compileAdaptiveFiniteCachedFixedAlphaVisit_query?_eq_some_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
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
    (layer : Fin T)
    (state :
      (finiteCachedFixedAlphaVisitStreamingVerifier machine n alpha block
        visit carried hentry).FueledState T)
    (index : Fin n) :
    (compileAdaptiveFiniteCachedFixedAlphaVisit (n := n) machine alpha block
      visit carried hentry).query? layer state = some index ↔
      let verifier := finiteCachedFixedAlphaVisitStreamingVerifier machine n
        alpha block visit carried hentry
      let closed := verifier.silentClosure state
      0 < closed.2.val ∧
        verifier.halted closed.1 = false ∧
        verifier.requestsInput closed.1 = true ∧
        ∃ (remaining : Fin (T + 1))
            (live : LocalReplayState
              (cachedInputMachine machine).State T
                (advertisedBlockWidth alpha.offsets block)),
          closed.1 = .running remaining live ∧
            live.inputHead.val < n ∧ index.val = live.inputHead.val := by
  change
    (finiteCachedFixedAlphaVisitStreamingVerifier machine n alpha block visit
      carried hentry).adaptiveQuery?
        (finiteCachedVisitAdaptiveQueryIndex? machine n) state = some index ↔ _
  rw [FiniteStreamingVerifier.adaptiveQuery?_eq_some_iff]
  simp only [finiteCachedVisitAdaptiveQueryIndex?_eq_some_iff]

/-- Exact width of the adaptive cached-visit program. -/
@[simp]
theorem compileAdaptiveFiniteCachedFixedAlphaVisit_width
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
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
    (compileAdaptiveFiniteCachedFixedAlphaVisit (n := n) machine alpha block visit
      carried hentry).width =
      @Fintype.card (FiniteCachedVisitStreamingState
        (cachedInputMachine machine).State T
        (advertisedBlockWidth alpha.offsets block))
        (cachedFiniteVisitStreamingStateFintype machine T
          (advertisedBlockWidth alpha.offsets block)) * (T + 1) := by
  exact FiniteStreamingVerifier.compileAdaptive_width
    (finiteCachedFixedAlphaVisitStreamingVerifier machine n alpha block visit
      carried hentry) T n (fun bit => .bit bit) .rightEnd
      (finiteCachedVisitAdaptiveQueryIndex? machine n)

/-- Exact final-state equation for the specialized adaptive compiler. -/
theorem compileAdaptiveFiniteCachedFixedAlphaVisit_finalState
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
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
    (input : Fin n → Bool) :
    (compileAdaptiveFiniteCachedFixedAlphaVisit (n := n) machine alpha block visit
      carried hentry).finalState input =
      (finiteCachedFixedAlphaVisitStreamingVerifier machine n alpha block
        visit carried hentry).runAdaptive T (fun bit => .bit bit)
          (finiteCachedVisitAdaptiveQueryIndex? machine n) input := by
  exact FiniteStreamingVerifier.compileAdaptive_finalState
    (finiteCachedFixedAlphaVisitStreamingVerifier machine n alpha block visit
      carried hentry) T n (fun bit => .bit bit) .rightEnd
      (finiteCachedVisitAdaptiveQueryIndex? machine n) input

end OneTapeMagnification
end Frontier
end Pnp4
