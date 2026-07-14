import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.AdaptiveCachedBlockVisitListCorrectness

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Head-segment correctness for the adaptive cached block-visit list

This file closes the operational gap between the already established
one-visit streaming certificate and the single finite verifier for a whole
fixed-block visit list.  Exactly the advertised number of input-driven
microsteps keeps the list cursor fixed and runs the selected one-visit phase.
The following silent microstep checks the advertised endpoint and carries the
completed slab to the next cursor.
-/

/-- While the selected visit still has advertised transitions left, the list
verifier is an exact cursor-preserving lifting of the established one-visit
streaming run. -/
theorem finiteCachedBlockVisitList_inputDrivenCore_active_eq_streaming
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (cursor : Fin visits.length)
    (remaining : Fin (T + 1))
    (live : LocalReplayState (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block))
    (unreads : List ReadOnlySymbol)
    (hnonempty : unreads ≠ [])
    (hlength : remaining.val = unreads.length)
    (hagree : FiniteCachedVisitSymbolsAgree machine input T
      (advertisedBlockWidth alpha.offsets block)
      (advertisedBlockLower alpha.offsets block) unreads live) :
    let verifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
      machine input.length alpha block initialSlab visits hentries
    verifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length)
        (fun index => input.get index) unreads.length
        (.active cursor (.running remaining live)) =
      liftFiniteCachedBlockVisitPhase cursor
        (runFiniteCachedVisitStreamingWithUnreads machine input.length T
          (advertisedBlockWidth alpha.offsets block)
          (advertisedBlockLower alpha.offsets block)
          (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
          unreads (.running remaining live)) := by
  dsimp only
  induction unreads generalizing remaining live with
  | nil => contradiction
  | cons unread rest ih =>
      have hpositive : 0 < remaining.val := by
        rw [hlength]
        simp
      have hread : readOnlySymbol input live.inputHead.val = unread := by
        cases rest with
        | nil => simpa [FiniteCachedVisitSymbolsAgree] using hagree
        | cons nextUnread tail =>
            exact (finiteCachedVisitSymbolsAgree_cons_cons machine input T
              (advertisedBlockWidth alpha.offsets block)
              (advertisedBlockLower alpha.offsets block) unread nextUnread
              tail live).mp hagree |>.1
      have hanswer :=
        finiteCachedVisit_inputDrivenAnswer_eq_streamingAnswer machine input
          remaining live unread hpositive hread
      simp only [List.length_cons,
        FiniteStreamingVerifier.inputDrivenCore]
      simp only [finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
        finiteCachedBlockVisitListHalted, Bool.false_eq_true,
        ↓reduceIte, finiteCachedBlockVisitListRequestsInput,
        finiteCachedBlockVisitListAdaptiveQueryIndex?,
        finiteCachedBlockVisitListStreamingStep_active_running]
      rw [runFiniteCachedVisitStreamingWithUnreads_cons]
      simp only [streamingAnswerForPhaseUnread]
      rw [hanswer]
      cases rest with
      | nil => rfl
      | cons nextUnread tail =>
          have hend : cachedLocalStepNeedsUnread machine live = true →
              ¬ live.inputHead.val < input.length → unread = .rightEnd := by
            intro _ hhead
            calc
              unread = readOnlySymbol input live.inputHead.val := hread.symm
              _ = .rightEnd := readOnlySymbol_eq_rightEnd_of_length_le input
                live.inputHead.val (Nat.le_of_not_gt hhead)
          have hstreamStep := finiteCachedVisitStreamingStep_answerForUnread
            machine input.length
              (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
              remaining live unread hend
          rw [hstreamStep]
          have hzero : remaining.val ≠ 0 := by omega
          have hone : remaining.val ≠ 1 := by
            rw [hlength]
            simp
          cases hlocal : finiteLocalCachedStep machine T
              (advertisedBlockWidth alpha.offsets block)
              (advertisedBlockLower alpha.offsets block) unread live with
          | inside next =>
              have htailAgree : FiniteCachedVisitSymbolsAgree machine input T
                  (advertisedBlockWidth alpha.offsets block)
                  (advertisedBlockLower alpha.offsets block)
                  (nextUnread :: tail) next := by
                rw [finiteCachedVisitSymbolsAgree_cons_cons, hlocal] at hagree
                exact hagree.2
              have htailLength : (spendVisitStep remaining).val =
                  (nextUnread :: tail).length := by
                simp only [spendVisitStep]
                rw [hlength]
                simp
              simpa [advanceFiniteCachedVisitPhase, hzero, hone, hlocal,
                liftFiniteCachedBlockVisitPhase] using
                  ih (spendVisitStep remaining) next (by simp) htailLength
                    htailAgree
          | halted outcome =>
              have htailAgree : FiniteCachedVisitSymbolsAgree machine input T
                  (advertisedBlockWidth alpha.offsets block)
                  (advertisedBlockLower alpha.offsets block)
                  (nextUnread :: tail) live := by
                rw [finiteCachedVisitSymbolsAgree_cons_cons, hlocal] at hagree
                exact hagree.2
              have htailLength : (spendVisitStep remaining).val =
                  (nextUnread :: tail).length := by
                simp only [spendVisitStep]
                rw [hlength]
                simp
              simpa [advanceFiniteCachedVisitPhase, hzero, hone, hlocal,
                liftFiniteCachedBlockVisitPhase] using
                  ih (spendVisitStep remaining) live (by simp) htailLength
                    htailAgree
          | workHeadExit =>
              rw [finiteCachedVisitSymbolsAgree_cons_cons, hlocal] at hagree
              have hfalse : False := by simpa using hagree.2
              exact hfalse.elim
          | inputHorizonExceeded =>
              rw [finiteCachedVisitSymbolsAgree_cons_cons, hlocal] at hagree
              have hfalse : False := by simpa using hagree.2
              exact hfalse.elim

/-- Tail embedding is independent of the two verifiers' proof-only start
slabs.  Their transition, halt, request, and selector fields are identical;
only the state supplied explicitly to `inputDrivenCore` matters. -/
theorem finiteCachedBlockVisitList_inputDrivenCore_prepend_twoStarts
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (first : FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)
    (rest : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (consInitial tailInitial : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (hcons : FixedAlphaBlockVisitEntriesInside alpha block (first :: rest))
    (htail : FixedAlphaBlockVisitEntriesInside alpha block rest)
    (fuel : Nat)
    (state : FiniteCachedBlockVisitListStreamingState
      (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block) rest.length) :
    let consVerifier :=
      finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine
        input.length alpha block consInitial (first :: rest) hcons
    let tailVerifier :=
      finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine
        input.length alpha block tailInitial rest htail
    consVerifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length)
        (fun index => input.get index) fuel
        (prependFiniteCachedBlockVisitListState first rest state) =
      prependFiniteCachedBlockVisitListState first rest
        (tailVerifier.inputDrivenCore (fun bit => .bit bit)
          (finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length)
          (fun index => input.get index) fuel state) := by
  dsimp only
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simp only [FiniteStreamingVerifier.inputDrivenCore]
      simp only [finiteCachedFixedAlphaBlockVisitListStreamingVerifier]
      rw [finiteCachedBlockVisitListHalted_prepend]
      by_cases hhalt : finiteCachedBlockVisitListHalted state = true
      · simp [hhalt]
      · have hhaltFalse : finiteCachedBlockVisitListHalted state = false := by
          cases h : finiteCachedBlockVisitListHalted state <;> simp_all
        simp only [hhaltFalse, Bool.false_eq_true, ↓reduceIte]
        simp only [finiteCachedBlockVisitListRequestsInput_prepend,
          finiteCachedBlockVisitListAdaptiveQueryIndex?_prepend]
        rw [finiteCachedBlockVisitListStreamingStep_prepend]
        exact ih _

/-- A certified head visit consumes exactly its advertised transition count
and leaves the list verifier at the same cursor with the certified completed
finite phase.  The endpoint/carry transition has deliberately not yet been
taken. -/
theorem finiteCachedBlockVisitList_inputDrivenCore_head_completed_of_stepCertificate
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (first : FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)
    (rest : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block (first :: rest))
    (final : FiniteLocalFinalState (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block))
    (hcertificate : FiniteCachedFixedAlphaVisitStreamingStepCertificate
      machine input alpha block first initialSlab final) :
    let verifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
      machine input.length alpha block initialSlab (first :: rest) hentries
    verifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length)
        (fun index => input.get index) first.steps verifier.start =
      .active ⟨0, by simp⟩ (.completed final) := by
  rcases hcertificate with
    ⟨certificateEntry, hagree, hstream, hstate, hinput, hwork⟩
  let cursor : Fin (first :: rest).length := ⟨0, by simp⟩
  let listEntry : WorkCellInSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      first.entry.workHead.val := hentries first (by simp)
  have hentryEq : certificateEntry = listEntry := Subsingleton.elim _ _
  subst certificateEntry
  let unreads := cachedRunUnreadSymbols machine input
    (fixedAlphaBlockVisitEntryConfiguration alpha block first initialSlab)
    first.steps
  let initial := finiteCachedStateOfVisitEntry machine alpha block first
    initialSlab listEntry
  let verifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
    machine input.length alpha block initialSlab (first :: rest) hentries
  have hstart : verifier.start =
      .active cursor (.running (fixedAlphaVisitRemaining first) initial) := by
    change finiteCachedBlockVisitListStart machine alpha block initialSlab
      (first :: rest) hentries = _
    rw [finiteCachedBlockVisitListStart]
    split
    · simp [finiteCachedBlockVisitListActiveState, cursor, initial]
    · simp_all
  have hnonempty : unreads ≠ [] := by
    apply List.ne_nil_of_length_pos
    simp [unreads, FixedAlphaBlockVisit.steps_pos]
  have hlength : (fixedAlphaVisitRemaining first).val = unreads.length := by
    simp [fixedAlphaVisitRemaining, unreads]
  have hsegment :=
    finiteCachedBlockVisitList_inputDrivenCore_active_eq_streaming
      machine input alpha block initialSlab (first :: rest) hentries cursor
      (fixedAlphaVisitRemaining first) initial unreads hnonempty hlength
      (by simpa [unreads, initial, listEntry] using hagree)
  change verifier.inputDrivenCore (fun bit => .bit bit)
      (finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length)
      (fun index => input.get index) first.steps verifier.start = _
  rw [hstart]
  have hsteps : unreads.length = first.steps := by simp [unreads]
  rw [← hsteps]
  rw [hsegment]
  have hstream' :
      runFiniteCachedVisitStreamingWithUnreads machine input.length T
        (advertisedBlockWidth alpha.offsets block)
        (advertisedBlockLower alpha.offsets block)
        (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
        unreads (.running (fixedAlphaVisitRemaining first) initial) =
          .completed final := by
    simpa [unreads, initial, listEntry] using hstream
  rw [hstream']
  rfl

/-- Recursively certified visit replay makes the single list verifier reach a
global completed state in exactly its advertised transition-plus-boundary
fuel. -/
theorem finiteCachedBlockVisitList_inputDrivenCore_completed_of_certificate
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (hcertificate : FiniteCachedFixedAlphaBlockVisitListStreamingCertificate
      machine input alpha block initialSlab visits) :
    ∃ finalSlab,
      let verifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
        machine input.length alpha block initialSlab visits hentries
      verifier.inputDrivenCore (fun bit => .bit bit)
          (finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length)
          (fun index => input.get index)
          (finiteCachedBlockVisitListFuel visits) verifier.start =
        .completed finalSlab := by
  induction visits generalizing initialSlab with
  | nil =>
      refine ⟨initialSlab, ?_⟩
      change (finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine
        input.length alpha block initialSlab [] hentries).inputDrivenCore
          (fun bit => .bit bit)
          (finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length)
          (fun index => input.get index) 0 (.completed initialSlab) =
            .completed initialSlab
      rfl
  | cons first rest ih =>
      rcases hcertificate with ⟨firstFinal, hfirst, htail⟩
      let tailEntries : FixedAlphaBlockVisitEntriesInside alpha block rest :=
        fun visit hmem => hentries visit (by simp [hmem])
      obtain ⟨finalSlab, htailCore⟩ :=
        ih firstFinal.workSlab tailEntries htail
      let consVerifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
        machine input.length alpha block initialSlab (first :: rest) hentries
      let tailVerifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
        machine input.length alpha block firstFinal.workSlab rest tailEntries
      let consSelector : FiniteCachedBlockVisitListStreamingState
          (cachedInputMachine machine).State T
          (advertisedBlockWidth alpha.offsets block) (first :: rest).length →
          Option (Fin input.length) :=
        finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length
      let tailSelector : FiniteCachedBlockVisitListStreamingState
          (cachedInputMachine machine).State T
          (advertisedBlockWidth alpha.offsets block) rest.length →
          Option (Fin input.length) :=
        finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length
      let inputBits : Fin input.length → Bool := fun index => input.get index
      let cursor : Fin (first :: rest).length := ⟨0, by simp⟩
      have hhead : consVerifier.inputDrivenCore (fun bit => .bit bit)
          consSelector inputBits first.steps consVerifier.start =
          .active cursor (.completed firstFinal) := by
        simpa [consVerifier, consSelector, inputBits, cursor] using
          finiteCachedBlockVisitList_inputDrivenCore_head_completed_of_stepCertificate
            machine input alpha block initialSlab first rest hentries
              firstFinal hfirst
      rcases hfirst with
        ⟨firstEntry, firstAgree, firstStream, firstState, firstInput,
          firstWork⟩
      have hfirstAccept : @finiteCachedVisitPhaseAccept
          (cachedInputMachine machine).State
          (cachedInputStateDecidableEq machine) T
          (advertisedBlockWidth alpha.offsets block) first.exit
          (.completed firstFinal) = true :=
        (@finiteCachedVisitPhaseAccept_completed_eq_true_iff
          (cachedInputMachine machine).State
          (cachedInputStateDecidableEq machine) T
          (advertisedBlockWidth alpha.offsets block) first.exit firstFinal).2
            ⟨firstState, firstInput, firstWork⟩
      have hboundary : consVerifier.inputDrivenCore (fun bit => .bit bit)
          consSelector inputBits 1 (.active cursor (.completed firstFinal)) =
          prependFiniteCachedBlockVisitListState first rest
            tailVerifier.start := by
        cases rest with
        | nil =>
            simp [consVerifier, tailVerifier, cursor,
              FiniteStreamingVerifier.inputDrivenCore,
              finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
              finiteCachedBlockVisitListStart,
              finiteCachedBlockVisitListHalted,
              finiteCachedBlockVisitListRequestsInput,
              finiteCachedVisitPhaseRequestsInput,
              finiteCachedBlockVisitListStreamingStep,
              prependFiniteCachedBlockVisitListState, hfirstAccept]
        | cons second remaining =>
            simp [consVerifier, tailVerifier, cursor,
              FiniteStreamingVerifier.inputDrivenCore,
              finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
              finiteCachedBlockVisitListStart,
              finiteCachedBlockVisitListHalted,
              finiteCachedBlockVisitListRequestsInput,
              finiteCachedVisitPhaseRequestsInput,
              finiteCachedBlockVisitListStreamingStep, hfirstAccept,
              finiteCachedBlockVisitListActiveState,
              prependFiniteCachedBlockVisitListState]
      have htailEmbedded : consVerifier.inputDrivenCore (fun bit => .bit bit)
          consSelector inputBits (finiteCachedBlockVisitListFuel rest)
          (prependFiniteCachedBlockVisitListState first rest
            tailVerifier.start) = .completed finalSlab := by
        change tailVerifier.inputDrivenCore (fun bit => .bit bit)
            tailSelector inputBits (finiteCachedBlockVisitListFuel rest)
            tailVerifier.start = .completed finalSlab at htailCore
        have hembed :=
          finiteCachedBlockVisitList_inputDrivenCore_prepend_twoStarts
            machine input alpha block first rest initialSlab
              firstFinal.workSlab hentries tailEntries
              (finiteCachedBlockVisitListFuel rest) tailVerifier.start
        have hembed' : consVerifier.inputDrivenCore
            (fun bit => .bit bit) consSelector inputBits
              (finiteCachedBlockVisitListFuel rest)
              (prependFiniteCachedBlockVisitListState first rest
                tailVerifier.start) =
            prependFiniteCachedBlockVisitListState first rest
              (tailVerifier.inputDrivenCore (fun bit => .bit bit)
                tailSelector inputBits (finiteCachedBlockVisitListFuel rest)
                  tailVerifier.start) := by
          simpa [consVerifier, tailVerifier, consSelector, tailSelector,
            inputBits] using hembed
        rw [htailCore] at hembed'
        simpa using hembed'
      refine ⟨finalSlab, ?_⟩
      change consVerifier.inputDrivenCore (fun bit => .bit bit) consSelector
          inputBits (finiteCachedBlockVisitListFuel (first :: rest))
          consVerifier.start = .completed finalSlab
      have hfuel : finiteCachedBlockVisitListFuel (first :: rest) =
          first.steps + 1 + finiteCachedBlockVisitListFuel rest := by
        simp [finiteCachedBlockVisitListFuel,
          fixedAlphaBlockVisitsTotalSteps]
        omega
      rw [hfuel]
      rw [consVerifier.inputDrivenCore_add (fun bit => .bit bit) consSelector
        inputBits (first.steps + 1) (finiteCachedBlockVisitListFuel rest)]
      rw [consVerifier.inputDrivenCore_add (fun bit => .bit bit) consSelector
        inputBits first.steps 1]
      rw [hhead, hboundary]
      exact htailEmbedded

/-- The list-level selector is total whenever the active cached phase really
requests an in-range immutable-input symbol. -/
theorem finiteCachedBlockVisitListAdaptiveQueryIndex?_total_of_requestsInput
    (machine : DeterministicMachine) (n : Nat) {T w k : Nat}
    (state : FiniteCachedBlockVisitListStreamingState
      (cachedInputMachine machine).State T w k)
    (hrequest : finiteCachedBlockVisitListRequestsInput machine n state =
      true) :
    ∃ index,
      finiteCachedBlockVisitListAdaptiveQueryIndex? machine n state =
        some index := by
  cases state with
  | completed slab =>
      simp [finiteCachedBlockVisitListRequestsInput] at hrequest
  | rejected =>
      simp [finiteCachedBlockVisitListRequestsInput] at hrequest
  | active cursor phase =>
      exact finiteCachedVisitAdaptiveQueryIndex?_total_of_requestsInput
        machine n phase hrequest

/-- Unconditional list completeness on the canonical Boolean input view.
Semantic replay is used only in this proof; the executable program itself
depends on the advertised alpha, block, slab, visits, and erased entry-inside
evidence. -/
theorem compileAdaptiveFiniteCachedFixedAlphaBlockVisitList_eval_eq_true_of_replayAccepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (haccepted : FixedAlphaBlockVisitReplayAccepted
      (cachedInputMachine machine) input alpha block initialSlab visits) :
    (compileAdaptiveFiniteCachedFixedAlphaBlockVisitList machine alpha block
      initialSlab visits hentries).eval (fun index => input.get index) =
        true := by
  let verifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
    machine input.length alpha block initialSlab visits hentries
  let selector : verifier.State → Option (Fin input.length) :=
    finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length
  let inputBits : Fin input.length → Bool := fun index => input.get index
  have hcertificate :=
    (finiteCachedFixedAlphaBlockVisitListStreamingCertificate_iff
      machine input alpha block initialSlab visits).mpr haccepted
  obtain ⟨finalSlab, hcore⟩ :=
    finiteCachedBlockVisitList_inputDrivenCore_completed_of_certificate
      machine input alpha block initialSlab visits hentries hcertificate
  change verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
      (finiteCachedBlockVisitListFuel visits) verifier.start =
        .completed finalSlab at hcore
  have htotal : ∀ state, verifier.requestsInput state = true →
      ∃ index, selector state = some index := by
    intro state hrequest
    exact finiteCachedBlockVisitListAdaptiveQueryIndex?_total_of_requestsInput
      machine input.length state hrequest
  have hrunPhase :
      (verifier.runAdaptive (finiteCachedBlockVisitListFuel visits)
        (fun bit => .bit bit) selector inputBits).1 =
      verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
        (finiteCachedBlockVisitListFuel visits) verifier.start := by
    simpa [FiniteStreamingVerifier.runAdaptive,
      FiniteStreamingVerifier.initialFueledState] using
        verifier.runAdaptiveFrom_state_eq_inputDrivenCore_of_fuel_le_layers
          (fun bit => .bit bit) selector inputBits htotal
          (verifier.initialFueledState
            (finiteCachedBlockVisitListFuel visits))
          (finiteCachedBlockVisitListFuel visits) le_rfl
  have hrun :
      (verifier.runAdaptive (finiteCachedBlockVisitListFuel visits)
        (fun bit => .bit bit) selector inputBits).1 = .completed finalSlab :=
    hrunPhase.trans hcore
  have hhalted : verifier.halted
      (verifier.runAdaptive (finiteCachedBlockVisitListFuel visits)
        (fun bit => .bit bit) selector inputBits).1 = true := by
    rw [hrun]
    rfl
  have hfinish : verifier.finishWithEndSymbol .rightEnd
      (verifier.runAdaptive (finiteCachedBlockVisitListFuel visits)
        (fun bit => .bit bit) selector inputBits) = .completed finalSlab := by
    calc
      verifier.finishWithEndSymbol .rightEnd
          (verifier.runAdaptive (finiteCachedBlockVisitListFuel visits)
            (fun bit => .bit bit) selector inputBits) =
        (verifier.runAdaptive (finiteCachedBlockVisitListFuel visits)
          (fun bit => .bit bit) selector inputBits).1 :=
        verifier.finishWithEndSymbol_eq_of_halted .rightEnd _ hhalted
      _ = .completed finalSlab := hrun
  change (verifier.compileAdaptive (finiteCachedBlockVisitListFuel visits)
      input.length (fun bit => .bit bit) .rightEnd selector).eval
        inputBits = true
  rw [FiniteStreamingVerifier.compileAdaptive_eval]
  change finiteCachedBlockVisitListAccept
      (verifier.finishWithEndSymbol .rightEnd
        (verifier.runAdaptive (finiteCachedBlockVisitListFuel visits)
          (fun bit => .bit bit) selector inputBits)) = true
  rw [hfinish]
  rfl

end OneTapeMagnification
end Frontier
end Pnp4
