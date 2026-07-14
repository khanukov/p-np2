import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedBlockVisitListCompiler

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Read-once adaptive compilation for a fixed-block visit list

Within one cached visit, every fresh input query strictly raises the finite
input-head rank.  At a visit boundary the list verifier performs a silent
endpoint/carry transition.  The exact additional premise needed to preserve
that rank is that the advertised exit head of each visit is at most the
advertised entry head of its immediate successor.

This file keeps that cross-visit premise explicit.  It does not assume that
arbitrary advertised visit lists satisfy it.
-/

/-- Exact adjacent cross-visit premise: every advertised exit input head is
at most the advertised entry input head of the immediately following visit.
The indexed form matches the finite cursor used by the executable verifier. -/
def FixedAlphaBlockVisitInputHeadsOrdered
    {State : Type} {T : Nat}
    (visits : List (FixedAlphaBlockVisit State T)) : Prop :=
  ∀ (cursor : Fin visits.length)
      (hnext : cursor.val + 1 < visits.length),
    (visits.get cursor).exit.inputHead.val ≤
      (visits.get ⟨cursor.val + 1, hnext⟩).entry.inputHead.val

/-- Input-head rank of the whole list verifier.  Active states inherit the
one-visit phase rank; global completion and rejection receive the strict
horizon upper bound. -/
def finiteCachedBlockVisitListInputRank
    {State : Type} {H w k : Nat} :
    FiniteCachedBlockVisitListStreamingState State H w k → Nat
  | .active _ phase => finiteCachedVisitPhaseInputRank phase
  | .completed _ => H + 1
  | .rejected => H + 1

/-- The selector of the list verifier returns an index exactly when its
active one-visit phase is running at that in-range input head. -/
theorem finiteCachedBlockVisitListAdaptiveQueryIndex?_eq_some_iff
    (machine : DeterministicMachine) (n : Nat) {T w k : Nat}
    (state : FiniteCachedBlockVisitListStreamingState
      (cachedInputMachine machine).State T w k)
    (index : Fin n) :
    finiteCachedBlockVisitListAdaptiveQueryIndex? machine n state =
        some index ↔
      ∃ (cursor : Fin k) (remaining : Fin (T + 1))
          (live : LocalReplayState
            (cachedInputMachine machine).State T w),
        state = .active cursor (.running remaining live) ∧
          live.inputHead.val < n ∧ index.val = live.inputHead.val := by
  cases state with
  | completed slab =>
      simp [finiteCachedBlockVisitListAdaptiveQueryIndex?]
  | rejected =>
      simp [finiteCachedBlockVisitListAdaptiveQueryIndex?]
  | active cursor phase =>
      rw [finiteCachedBlockVisitListAdaptiveQueryIndex?]
      rw [finiteCachedVisitAdaptiveQueryIndex?_eq_some_iff]
      constructor
      · rintro ⟨remaining, live, hphase, hhead, hindex⟩
        exact ⟨cursor, remaining, live, by simp [hphase], hhead, hindex⟩
      · rintro ⟨otherCursor, remaining, live, hstate, hhead, hindex⟩
        cases hstate
        exact ⟨remaining, live, rfl, hhead, hindex⟩

/-- One list-verifier microstep never lowers the global input rank under the
explicit adjacent advertised-head premise. -/
theorem finiteCachedBlockVisitListStreamingStep_inputRank_mono
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (hordered : FixedAlphaBlockVisitInputHeadsOrdered visits)
    (state : FiniteCachedBlockVisitListStreamingState
      (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block) visits.length)
    (supplied : Option ReadOnlySymbol) :
    finiteCachedBlockVisitListInputRank state ≤
      finiteCachedBlockVisitListInputRank
        (finiteCachedBlockVisitListStreamingStep machine n alpha block visits
          hentries state supplied) := by
  cases state with
  | completed slab =>
      simp [finiteCachedBlockVisitListStreamingStep,
        finiteCachedBlockVisitListInputRank]
  | rejected =>
      simp [finiteCachedBlockVisitListStreamingStep,
        finiteCachedBlockVisitListInputRank]
  | active cursor phase =>
      cases phase with
      | rejected failure =>
          simp [finiteCachedBlockVisitListStreamingStep,
            finiteCachedBlockVisitListInputRank,
            finiteCachedVisitPhaseInputRank]
      | running remaining live =>
          have hmono := finiteCachedVisitStreamingStep_inputRank_mono
            machine n T (advertisedBlockWidth alpha.offsets block)
              (advertisedBlockLower alpha.offsets block)
              (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
              (.running remaining live) supplied
          cases hphase : finiteCachedVisitStreamingStep machine n T
              (advertisedBlockWidth alpha.offsets block)
              (advertisedBlockLower alpha.offsets block)
              (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
              (.running remaining live) supplied with
          | running nextRemaining next =>
              simpa [finiteCachedBlockVisitListStreamingStep, hphase,
                liftFiniteCachedBlockVisitPhase,
                finiteCachedBlockVisitListInputRank] using hmono
          | completed final =>
              simpa [finiteCachedBlockVisitListStreamingStep, hphase,
                liftFiniteCachedBlockVisitPhase,
                finiteCachedBlockVisitListInputRank] using hmono
          | rejected nextFailure =>
              simpa [finiteCachedBlockVisitListStreamingStep, hphase,
                liftFiniteCachedBlockVisitPhase,
                finiteCachedBlockVisitListInputRank] using hmono
      | completed final =>
          by_cases haccept : @finiteCachedVisitPhaseAccept
              (cachedInputMachine machine).State
              (cachedInputStateDecidableEq machine) T
              (advertisedBlockWidth alpha.offsets block)
              (visits.get cursor).exit (.completed final) = true
          · dsimp only [finiteCachedBlockVisitListStreamingStep]
            rw [if_pos haccept]
            cases supplied with
            | some unread =>
                simp only [finiteCachedBlockVisitListInputRank,
                  finiteCachedVisitPhaseInputRank]
                exact Nat.le_of_lt final.inputHead.isLt
            | none =>
                by_cases hnext : cursor.val + 1 < visits.length
                · rw [dif_pos hnext]
                  have hacceptParts :=
                    (@finiteCachedVisitPhaseAccept_completed_eq_true_iff
                      (cachedInputMachine machine).State
                      (cachedInputStateDecidableEq machine) T
                      (advertisedBlockWidth alpha.offsets block)
                      (visits.get cursor).exit final).mp haccept
                  have hboundary := hordered cursor hnext
                  change final.inputHead.val ≤ _
                  calc
                    final.inputHead.val =
                        (visits.get cursor).exit.inputHead.val := by
                      exact congrArg Fin.val hacceptParts.2.1.symm
                    _ ≤ (visits.get ⟨cursor.val + 1, hnext⟩).entry.inputHead.val :=
                      hboundary
                    _ = finiteCachedBlockVisitListInputRank
                        (finiteCachedBlockVisitListActiveState machine alpha
                          block visits hentries ⟨cursor.val + 1, hnext⟩
                            final.workSlab) := by
                      simp [finiteCachedBlockVisitListActiveState,
                        finiteCachedBlockVisitListInputRank,
                        finiteCachedVisitPhaseInputRank,
                        finiteCachedStateOfVisitEntry]
                · rw [dif_neg hnext]
                  simp only [finiteCachedBlockVisitListInputRank,
                    finiteCachedVisitPhaseInputRank]
                  exact Nat.le_of_lt final.inputHead.isLt
          · dsimp only [finiteCachedBlockVisitListStreamingStep]
            rw [if_neg haccept]
            simp only [finiteCachedBlockVisitListInputRank,
              finiteCachedVisitPhaseInputRank]
            exact Nat.le_of_lt final.inputHead.isLt

/-- Consuming a symbol at a genuine list-level request raises the global
input rank strictly.  This local strictness does not use the boundary premise
because a request can occur only inside an active running phase. -/
theorem finiteCachedBlockVisitListStreamingStep_inputRank_lt_of_requestsInput
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (state : FiniteCachedBlockVisitListStreamingState
      (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block) visits.length)
    (unread : ReadOnlySymbol)
    (hrequest : finiteCachedBlockVisitListRequestsInput machine n state =
      true) :
    finiteCachedBlockVisitListInputRank state <
      finiteCachedBlockVisitListInputRank
        (finiteCachedBlockVisitListStreamingStep machine n alpha block visits
          hentries state (some unread)) := by
  cases state with
  | completed slab =>
      simp [finiteCachedBlockVisitListRequestsInput] at hrequest
  | rejected =>
      simp [finiteCachedBlockVisitListRequestsInput] at hrequest
  | active cursor phase =>
      cases phase with
      | completed final =>
          simp [finiteCachedBlockVisitListRequestsInput,
            finiteCachedVisitPhaseRequestsInput] at hrequest
      | rejected failure =>
          simp [finiteCachedBlockVisitListRequestsInput,
            finiteCachedVisitPhaseRequestsInput] at hrequest
      | running remaining live =>
          have hstrict :=
            finiteCachedVisitStreamingStep_inputRank_lt_of_requestsInput
              machine n T (advertisedBlockWidth alpha.offsets block)
              (advertisedBlockLower alpha.offsets block)
              (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
              (.running remaining live) unread hrequest
          cases hphase : finiteCachedVisitStreamingStep machine n T
              (advertisedBlockWidth alpha.offsets block)
              (advertisedBlockLower alpha.offsets block)
              (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
              (.running remaining live) (some unread) with
          | running nextRemaining next =>
              simpa [finiteCachedBlockVisitListStreamingStep, hphase,
                liftFiniteCachedBlockVisitPhase,
                finiteCachedBlockVisitListInputRank] using hstrict
          | completed final =>
              simpa [finiteCachedBlockVisitListStreamingStep, hphase,
                liftFiniteCachedBlockVisitPhase,
                finiteCachedBlockVisitListInputRank] using hstrict
          | rejected nextFailure =>
              simpa [finiteCachedBlockVisitListStreamingStep, hphase,
                liftFiniteCachedBlockVisitPhase,
                finiteCachedBlockVisitListInputRank] using hstrict

/-- Silent closure of the list verifier preserves the global input rank.
The only new case beyond one visit is the silent endpoint/carry boundary,
which is exactly where `hordered` is used. -/
theorem finiteCachedBlockVisitListStreamingVerifier_silentClosure_inputRank_mono
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (hordered : FixedAlphaBlockVisitInputHeadsOrdered visits)
    {K : Nat}
    (state : (finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine n
      alpha block initialSlab visits hentries).FueledState K) :
    finiteCachedBlockVisitListInputRank state.1 ≤
      finiteCachedBlockVisitListInputRank
        ((finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine n
          alpha block initialSlab visits hentries).silentClosure state).1 := by
  let verifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
    machine n alpha block initialSlab visits hentries
  apply FiniteStreamingVerifier.silentClosure_rank_mono verifier
    finiteCachedBlockVisitListInputRank
  intro current
  exact finiteCachedBlockVisitListStreamingStep_inputRank_mono machine n alpha
    block visits hentries hordered current none

/-- One adaptive layer of the list compiler never lowers the global input
rank. -/
theorem finiteCachedBlockVisitListAdaptiveInputStep_inputRank_mono
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (hordered : FixedAlphaBlockVisitInputHeadsOrdered visits)
    {K : Nat} (input : Fin n → Bool)
    (state : (finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine n
      alpha block initialSlab visits hentries).FueledState K) :
    finiteCachedBlockVisitListInputRank state.1 ≤
      finiteCachedBlockVisitListInputRank
        ((finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine n
          alpha block initialSlab visits hentries).adaptiveInputStep
            (fun bit => .bit bit)
            (finiteCachedBlockVisitListAdaptiveQueryIndex? machine n)
            input state).1 := by
  let verifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
    machine n alpha block initialSlab visits hentries
  let selector : verifier.State → Option (Fin n) :=
    finiteCachedBlockVisitListAdaptiveQueryIndex? machine n
  change finiteCachedBlockVisitListInputRank state.1 ≤
    finiteCachedBlockVisitListInputRank
      (verifier.adaptiveInputStep (fun bit => .bit bit) selector input state).1
  have hclosure : finiteCachedBlockVisitListInputRank state.1 ≤
      finiteCachedBlockVisitListInputRank (verifier.silentClosure state).1 :=
    finiteCachedBlockVisitListStreamingVerifier_silentClosure_inputRank_mono
      machine n alpha block initialSlab visits hentries hordered state
  cases hquery : verifier.adaptiveQuery? selector state with
  | none =>
      calc
        finiteCachedBlockVisitListInputRank state.1 ≤
            finiteCachedBlockVisitListInputRank
              (verifier.silentClosure state).1 := hclosure
        _ = finiteCachedBlockVisitListInputRank
              (verifier.adaptiveInputStep (fun bit => .bit bit) selector
                input state).1 := by
          simp [FiniteStreamingVerifier.adaptiveInputStep,
            FiniteStreamingVerifier.adaptiveNext, hquery]
  | some index =>
      have hcharacterization :=
        (FiniteStreamingVerifier.adaptiveQuery?_eq_some_iff verifier selector
          state index).mp hquery
      have hrequest := hcharacterization.2.2.1
      have hstrict :
          finiteCachedBlockVisitListInputRank
              (verifier.silentClosure state).1 <
            finiteCachedBlockVisitListInputRank
              (verifier.step (verifier.silentClosure state).1
                (some (.bit (input index)))) := by
        change finiteCachedBlockVisitListRequestsInput machine n
          (verifier.silentClosure state).1 = true at hrequest
        exact
          finiteCachedBlockVisitListStreamingStep_inputRank_lt_of_requestsInput
            machine n alpha block visits hentries
              (verifier.silentClosure state).1 (.bit (input index)) hrequest
      have hnext :
          verifier.adaptiveInputStep (fun bit => .bit bit) selector input state =
            (verifier.step (verifier.silentClosure state).1
                (some (.bit (input index))),
              FiniteStreamingVerifier.spendOne
                (verifier.silentClosure state).2) := by
        simp [FiniteStreamingVerifier.adaptiveInputStep,
          FiniteStreamingVerifier.adaptiveNext, hquery]
      rw [hnext]
      exact hclosure.trans (Nat.le_of_lt hstrict)

/-- Every genuine list-level adaptive query lies strictly below the global
rank after its answer has been consumed. -/
theorem finiteCachedBlockVisitListAdaptiveInputStep_query_lt_inputRank
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    {K : Nat} (input : Fin n → Bool)
    (state : (finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine n
      alpha block initialSlab visits hentries).FueledState K)
    (index : Fin n)
    (hquery :
      (finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine n alpha
        block initialSlab visits hentries).adaptiveQuery?
          (finiteCachedBlockVisitListAdaptiveQueryIndex? machine n) state =
            some index) :
    index.val < finiteCachedBlockVisitListInputRank
      ((finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine n alpha
        block initialSlab visits hentries).adaptiveInputStep
          (fun bit => .bit bit)
          (finiteCachedBlockVisitListAdaptiveQueryIndex? machine n)
          input state).1 := by
  let verifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
    machine n alpha block initialSlab visits hentries
  let selector : verifier.State → Option (Fin n) :=
    finiteCachedBlockVisitListAdaptiveQueryIndex? machine n
  change verifier.adaptiveQuery? selector state = some index at hquery
  change index.val < finiteCachedBlockVisitListInputRank
    (verifier.adaptiveInputStep (fun bit => .bit bit) selector input state).1
  have hcharacterization :=
    (FiniteStreamingVerifier.adaptiveQuery?_eq_some_iff verifier selector
      state index).mp hquery
  have hrequest := hcharacterization.2.2.1
  have hselector := hcharacterization.2.2.2
  rcases (finiteCachedBlockVisitListAdaptiveQueryIndex?_eq_some_iff machine n
      (verifier.silentClosure state).1 index).mp hselector with
    ⟨cursor, remaining, live, hstate, hhead, hindex⟩
  have hstrict :
      finiteCachedBlockVisitListInputRank
          (verifier.silentClosure state).1 <
        finiteCachedBlockVisitListInputRank
          (verifier.step (verifier.silentClosure state).1
            (some (.bit (input index)))) := by
    change finiteCachedBlockVisitListRequestsInput machine n
      (verifier.silentClosure state).1 = true at hrequest
    exact finiteCachedBlockVisitListStreamingStep_inputRank_lt_of_requestsInput
      machine n alpha block visits hentries (verifier.silentClosure state).1
        (.bit (input index)) hrequest
  have hnext :
      verifier.adaptiveInputStep (fun bit => .bit bit) selector input state =
        (verifier.step (verifier.silentClosure state).1
            (some (.bit (input index))),
          FiniteStreamingVerifier.spendOne
            (verifier.silentClosure state).2) := by
    simp [FiniteStreamingVerifier.adaptiveInputStep,
      FiniteStreamingVerifier.adaptiveNext, hquery]
  calc
    index.val = finiteCachedBlockVisitListInputRank
        (verifier.silentClosure state).1 := by
      simp [hstate, finiteCachedBlockVisitListInputRank,
        finiteCachedVisitPhaseInputRank, hindex]
    _ < finiteCachedBlockVisitListInputRank
        (verifier.step (verifier.silentClosure state).1
          (some (.bit (input index)))) := hstrict
    _ = finiteCachedBlockVisitListInputRank
        (verifier.adaptiveInputStep (fun bit => .bit bit) selector input
          state).1 := by rw [hnext]

/-- Before a genuine list-level adaptive query, the global rank is at most
the queried coordinate. -/
theorem finiteCachedBlockVisitListAdaptiveQuery_inputRank_le
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (hordered : FixedAlphaBlockVisitInputHeadsOrdered visits)
    {K : Nat}
    (state : (finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine n
      alpha block initialSlab visits hentries).FueledState K)
    (index : Fin n)
    (hquery :
      (finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine n alpha
        block initialSlab visits hentries).adaptiveQuery?
          (finiteCachedBlockVisitListAdaptiveQueryIndex? machine n) state =
            some index) :
    finiteCachedBlockVisitListInputRank state.1 ≤ index.val := by
  let verifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
    machine n alpha block initialSlab visits hentries
  let selector : verifier.State → Option (Fin n) :=
    finiteCachedBlockVisitListAdaptiveQueryIndex? machine n
  change verifier.adaptiveQuery? selector state = some index at hquery
  have hclosure : finiteCachedBlockVisitListInputRank state.1 ≤
      finiteCachedBlockVisitListInputRank (verifier.silentClosure state).1 :=
    finiteCachedBlockVisitListStreamingVerifier_silentClosure_inputRank_mono
      machine n alpha block initialSlab visits hentries hordered state
  have hcharacterization :=
    (FiniteStreamingVerifier.adaptiveQuery?_eq_some_iff verifier selector
      state index).mp hquery
  have hselector := hcharacterization.2.2.2
  rcases (finiteCachedBlockVisitListAdaptiveQueryIndex?_eq_some_iff machine n
      (verifier.silentClosure state).1 index).mp hselector with
    ⟨cursor, remaining, live, hstate, hhead, hindex⟩
  calc
    finiteCachedBlockVisitListInputRank state.1 ≤
        finiteCachedBlockVisitListInputRank
          (verifier.silentClosure state).1 := hclosure
    _ = index.val := by
      simp [hstate, finiteCachedBlockVisitListInputRank,
        finiteCachedVisitPhaseInputRank, hindex]

/-- Every coordinate already queried by a compiled list prefix is strictly
below the resulting global input rank. -/
theorem compileAdaptiveFiniteCachedFixedAlphaBlockVisitList_executePrefix_query_lt_rank
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (hordered : FixedAlphaBlockVisitInputHeadsOrdered visits)
    (input : Fin n → Bool) (k : Nat)
    (hk : k ≤ finiteCachedBlockVisitListFuel visits)
    (index : Fin n)
    (hmem : index ∈
      ((compileAdaptiveFiniteCachedFixedAlphaBlockVisitList (n := n) machine
        alpha block initialSlab visits hentries).executePrefix input k hk).2) :
    index.val < finiteCachedBlockVisitListInputRank
      ((compileAdaptiveFiniteCachedFixedAlphaBlockVisitList (n := n) machine
        alpha block initialSlab visits hentries).executePrefix input k hk).1.1 := by
  let verifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
    machine n alpha block initialSlab visits hentries
  let selector : verifier.State → Option (Fin n) :=
    finiteCachedBlockVisitListAdaptiveQueryIndex? machine n
  let program := compileAdaptiveFiniteCachedFixedAlphaBlockVisitList
    (n := n) machine alpha block initialSlab visits hentries
  change index ∈ (program.executePrefix input k hk).2 at hmem
  change index.val < finiteCachedBlockVisitListInputRank
    (program.executePrefix input k hk).1.1
  induction k generalizing index with
  | zero =>
      simp [LayeredQueryProgram.executePrefix] at hmem
  | succ k ih =>
      let previous := program.executePrefix input k (by omega)
      let layer : Fin (finiteCachedBlockVisitListFuel visits) :=
        ⟨k, by omega⟩
      let query := program.query? layer previous.1
      have hmemAppend : index ∈ previous.2 ++ query.toList := by
        simpa [LayeredQueryProgram.executePrefix, previous, layer, query] using
          hmem
      have hnextEq :
          program.next layer previous.1 (query.map input) =
            verifier.adaptiveInputStep (fun bit => .bit bit) selector input
              previous.1 := by
        rfl
      have hnextMono :
          finiteCachedBlockVisitListInputRank previous.1.1 ≤
            finiteCachedBlockVisitListInputRank
              (program.next layer previous.1 (query.map input)).1 := by
        rw [hnextEq]
        exact finiteCachedBlockVisitListAdaptiveInputStep_inputRank_mono
          machine n alpha block initialSlab visits hentries hordered input
            previous.1
      have hresult : index.val < finiteCachedBlockVisitListInputRank
          (program.next layer previous.1 (query.map input)).1 := by
        rw [List.mem_append] at hmemAppend
        rcases hmemAppend with hprevious | hcurrent
        · have hprior : index.val <
              finiteCachedBlockVisitListInputRank previous.1.1 := by
            exact ih (by omega) index (by simpa [previous] using hprevious)
          exact hprior.trans_le hnextMono
        · have hquerySome : query = some index := by
            cases hquery : query with
            | none =>
                simp [hquery] at hcurrent
            | some current =>
                simp only [hquery, Option.toList_some,
                  List.mem_singleton] at hcurrent
                subst current
                rfl
          have hadaptive : verifier.adaptiveQuery? selector previous.1 =
              some index := by
            change query = some index
            exact hquerySome
          rw [hnextEq]
          exact finiteCachedBlockVisitListAdaptiveInputStep_query_lt_inputRank
            machine n alpha block initialSlab visits hentries input previous.1
              index hadaptive
      simpa [LayeredQueryProgram.executePrefix, previous, layer, query] using
        hresult

/-- Under the exact adjacent advertised-head premise, every newly exposed
query of the compiled visit list is strictly larger than every prior query. -/
theorem compileAdaptiveFiniteCachedFixedAlphaBlockVisitList_freshQueriesStrictlyIncrease
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (hordered : FixedAlphaBlockVisitInputHeadsOrdered visits) :
    FiniteStreamingVerifier.FreshQueriesStrictlyIncrease
      (compileAdaptiveFiniteCachedFixedAlphaBlockVisitList (n := n) machine
        alpha block initialSlab visits hentries) := by
  intro input k hk prior current hprior hcurrent
  let verifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
    machine n alpha block initialSlab visits hentries
  let selector : verifier.State → Option (Fin n) :=
    finiteCachedBlockVisitListAdaptiveQueryIndex? machine n
  let program := compileAdaptiveFiniteCachedFixedAlphaBlockVisitList
    (n := n) machine alpha block initialSlab visits hentries
  let executed := program.executePrefix input k (Nat.le_of_lt hk)
  have hpriorRank : prior.val <
      finiteCachedBlockVisitListInputRank executed.1.1 := by
    exact
      compileAdaptiveFiniteCachedFixedAlphaBlockVisitList_executePrefix_query_lt_rank
        machine alpha block initialSlab visits hentries hordered input k
          (Nat.le_of_lt hk) prior (by simpa [program, executed] using hprior)
  have hadaptive : verifier.adaptiveQuery? selector executed.1 =
      some current := by
    change program.query? ⟨k, hk⟩ executed.1 = some current
    simpa [program, executed] using hcurrent
  have hcurrentRank : finiteCachedBlockVisitListInputRank executed.1.1 ≤
      current.val :=
    finiteCachedBlockVisitListAdaptiveQuery_inputRank_le machine n alpha block
      initialSlab visits hentries hordered executed.1 current hadaptive
  have hvalues : prior.val < current.val :=
    hpriorRank.trans_le hcurrentRank
  exact hvalues

/-- The adaptive fixed-block visit-list compiler is read-once under exactly
the static adjacent advertised-head premise. -/
theorem compileAdaptiveFiniteCachedFixedAlphaBlockVisitList_isReadOnce
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (hordered : FixedAlphaBlockVisitInputHeadsOrdered visits) :
    (compileAdaptiveFiniteCachedFixedAlphaBlockVisitList (n := n) machine
      alpha block initialSlab visits hentries).IsReadOnce := by
  exact FiniteStreamingVerifier.isReadOnce_of_freshQueriesStrictlyIncrease _
    (compileAdaptiveFiniteCachedFixedAlphaBlockVisitList_freshQueriesStrictlyIncrease
      (n := n) machine alpha block initialSlab visits hentries hordered)

end OneTapeMagnification
end Frontier
end Pnp4
