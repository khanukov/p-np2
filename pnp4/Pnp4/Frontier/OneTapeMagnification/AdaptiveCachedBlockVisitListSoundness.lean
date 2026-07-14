import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.AdaptiveCachedBlockVisitListSegmentCorrectness

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Soundness of the adaptive cached block-visit list

This module proves the reverse operational direction.  Canonical execution
of the compiled finite list program can accept only if every advertised visit
is a valid slab-threaded semantic replay.
-/

/-- For exactly the phase's remaining transition counter, canonical execution
inside the list verifier is the cursor-preserving lift of the standalone
canonical one-visit runner.  No semantic trace or symbol-agreement premise is
used. -/
theorem finiteCachedBlockVisitList_inputDrivenCore_active_eq_inputDriven
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
      (advertisedBlockWidth alpha.offsets block)) :
    let verifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
      machine input.length alpha block initialSlab visits hentries
    verifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length)
        (fun index => input.get index) remaining.val
        (.active cursor (.running remaining live)) =
      liftFiniteCachedBlockVisitPhase cursor
        (runFiniteCachedVisitInputDriven machine input T
          (advertisedBlockWidth alpha.offsets block)
          (advertisedBlockLower alpha.offsets block)
          (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
          remaining.val (.running remaining live)) := by
  dsimp only
  have go : ∀ fuel : Nat, ∀ (currentRemaining : Fin (T + 1))
      (currentLive : LocalReplayState (cachedInputMachine machine).State T
        (advertisedBlockWidth alpha.offsets block)),
      currentRemaining.val = fuel →
      (finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine
          input.length alpha block initialSlab visits hentries).inputDrivenCore
          (fun bit => .bit bit)
          (finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length)
          (fun index => input.get index) fuel
          (.active cursor (.running currentRemaining currentLive)) =
        liftFiniteCachedBlockVisitPhase cursor
          (runFiniteCachedVisitInputDriven machine input T
            (advertisedBlockWidth alpha.offsets block)
            (advertisedBlockLower alpha.offsets block)
            (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
            fuel (.running currentRemaining currentLive)) := by
    intro fuel
    induction fuel with
    | zero =>
        intro currentRemaining currentLive hremaining
        rfl
    | succ fuel ih =>
        intro currentRemaining currentLive hremaining
        let unread := readOnlySymbol input currentLive.inputHead.val
        have hpositive : 0 < currentRemaining.val := by omega
        have hphaseNotHalted :
            finiteCachedVisitPhaseHalted
              (.running currentRemaining currentLive) = false := by
          simp [finiteCachedVisitPhaseHalted, Nat.ne_of_gt hpositive]
        have hanswer :=
          finiteCachedVisit_inputDrivenAnswer_eq_streamingAnswer machine input
            currentRemaining currentLive unread hpositive rfl
        simp only [FiniteStreamingVerifier.inputDrivenCore,
          finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
          finiteCachedBlockVisitListHalted, Bool.false_eq_true, ↓reduceIte,
          finiteCachedBlockVisitListRequestsInput,
          finiteCachedBlockVisitListAdaptiveQueryIndex?,
          finiteCachedBlockVisitListStreamingStep_active_running,
          runFiniteCachedVisitInputDriven, hphaseNotHalted]
        rw [hanswer]
        have hend : cachedLocalStepNeedsUnread machine currentLive = true →
            ¬ currentLive.inputHead.val < input.length →
              unread = .rightEnd := by
          intro _ hhead
          exact readOnlySymbol_eq_rightEnd_of_length_le input
            currentLive.inputHead.val (Nat.le_of_not_gt hhead)
        rw [finiteCachedVisitStreamingStep_answerForUnread machine input.length
          (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
          currentRemaining currentLive unread hend]
        by_cases htailZero : fuel = 0
        · subst fuel
          rfl
        · have hzero : currentRemaining.val ≠ 0 := by omega
          have hone : currentRemaining.val ≠ 1 := by omega
          cases hlocal : finiteLocalCachedStep machine T
              (advertisedBlockWidth alpha.offsets block)
              (advertisedBlockLower alpha.offsets block) unread currentLive with
          | inside next =>
              have htailRemaining : (spendVisitStep currentRemaining).val =
                  fuel := by
                simp only [spendVisitStep]
                omega
              simpa [advanceFiniteCachedVisitPhase, hzero, hone, hlocal,
                liftFiniteCachedBlockVisitPhase] using
                  ih (spendVisitStep currentRemaining) next htailRemaining
          | halted outcome =>
              have htailRemaining : (spendVisitStep currentRemaining).val =
                  fuel := by
                simp only [spendVisitStep]
                omega
              simpa [advanceFiniteCachedVisitPhase, hzero, hone, hlocal,
                liftFiniteCachedBlockVisitPhase] using
                  ih (spendVisitStep currentRemaining) currentLive
                    htailRemaining
          | workHeadExit =>
              simp [advanceFiniteCachedVisitPhase, hzero, hone, hlocal,
                FiniteStreamingVerifier.inputDrivenCore_eq_self_of_halted,
                runFiniteCachedVisitInputDriven_eq_self_of_halted,
                finiteCachedBlockVisitListHalted,
                finiteCachedVisitPhaseHalted,
                liftFiniteCachedBlockVisitPhase]
          | inputHorizonExceeded =>
              simp [advanceFiniteCachedVisitPhase, hzero, hone, hlocal,
                FiniteStreamingVerifier.inputDrivenCore_eq_self_of_halted,
                runFiniteCachedVisitInputDriven_eq_self_of_halted,
                finiteCachedBlockVisitListHalted,
                finiteCachedVisitPhaseHalted,
                liftFiniteCachedBlockVisitPhase]
  exact go remaining.val remaining live rfl

/-- A completed canonical one-visit runner whose endpoint check succeeds is
the exact semantic visit, including equality of the carried output slab. -/
theorem finiteCachedFixedAlphaVisit_valid_and_outputSlab_of_inputDriven_completed
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
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
    (final : FiniteLocalFinalState (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block))
    (hcompleted : runFiniteCachedVisitInputDriven machine input T
      (advertisedBlockWidth alpha.offsets block)
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
      (fixedAlphaVisitRemaining visit).val
      (.running (fixedAlphaVisitRemaining visit)
        (finiteCachedStateOfVisitEntry machine alpha block visit carried
          hentry)) = .completed final)
    (haccept : @finiteCachedVisitPhaseAccept
      (cachedInputMachine machine).State
      (cachedInputStateDecidableEq machine) T
      (advertisedBlockWidth alpha.offsets block) visit.exit
      (.completed final) = true) :
    FixedAlphaBlockVisitValid (cachedInputMachine machine) input alpha block
        visit carried ∧
      final.workSlab = fixedAlphaBlockVisitOutputSlab
        (cachedInputMachine machine) input alpha block visit carried := by
  let width := advertisedBlockWidth alpha.offsets block
  let base := advertisedBlockLower alpha.offsets block
  let hbound := advertisedBlockLower_add_width_le_horizon alpha.offsets block
  let remaining := fixedAlphaVisitRemaining visit
  let initial := finiteCachedStateOfVisitEntry machine alpha block visit
    carried hentry
  have hendpoint :=
    (@finiteCachedVisitPhaseAccept_completed_eq_true_iff
      (cachedInputMachine machine).State
      (cachedInputStateDecidableEq machine) T width visit.exit final).mp
        (by simpa [width] using haccept)
  have hcompleted' :
      runFiniteCachedVisitInputDriven machine input T width base hbound
        remaining.val (.running remaining initial) = .completed final := by
    simpa [width, base, hbound, remaining, initial] using hcompleted
  obtain ⟨unreads, htraceLength, hagree, hstream⟩ :=
    runFiniteCachedVisitInputDriven_completed_has_agreeing_trace
      machine input hbound remaining initial final hcompleted'
  have hnonempty : unreads ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [htraceLength]
    simp [remaining, fixedAlphaVisitRemaining,
      FixedAlphaBlockVisit.steps_pos]
  have hremainingLength : remaining.val = unreads.length :=
    htraceLength.symm
  have hrespect : FiniteCachedVisitUnreadsRespectEnd machine input.length T
      width base unreads initial :=
    finiteCachedVisitSymbolsAgree_implies_respectEnd machine input unreads
      initial hagree
  have hstreamReplay := runFiniteCachedVisitStreamingWithUnreads_eq_replay
    machine input.length hbound unreads remaining initial hnonempty
      hremainingLength hrespect
  have hmapped : streamingStateOfFiniteReplayResult
      (finiteCachedVisitReplay machine T width base hbound unreads initial) =
        .completed final := hstreamReplay.symm.trans hstream
  have hreplay : finiteCachedVisitReplay machine T width base hbound unreads
      initial = .completed final := by
    cases hresult : finiteCachedVisitReplay machine T width base hbound
        unreads initial with
    | completed replayFinal =>
        simp [hresult, streamingStateOfFiniteReplayResult] at hmapped
        subst replayFinal
        rfl
    | emptyTrace =>
        simp [hresult, streamingStateOfFiniteReplayResult] at hmapped
    | intermediateWorkHeadExit =>
        simp [hresult, streamingStateOfFiniteReplayResult] at hmapped
    | inputHorizonExceeded =>
        simp [hresult, streamingStateOfFiniteReplayResult] at hmapped
    | finalWorkHorizonExceeded =>
        simp [hresult, streamingStateOfFiniteReplayResult] at hmapped
  have htraceVisitLength : unreads.length = visit.steps := by
    rw [htraceLength]
    rfl
  have hreplayFixed : finiteCachedFixedAlphaBlockVisitReplay machine alpha
      block visit carried hentry unreads = .completed final := by
    simpa [finiteCachedFixedAlphaBlockVisitReplay, width, base, hbound,
      initial] using hreplay
  exact finiteCachedFixedAlphaBlockVisitReplay_completed_sound machine input
    alpha block visit carried hentry unreads final htraceVisitLength hagree
      hreplayFixed ⟨hendpoint.1, hendpoint.2.1, hendpoint.2.2⟩

/-- If exact-fuel canonical execution of the single list verifier reaches a
global completed state, the advertised list has the recursively slab-threaded
finite streaming certificate. -/
theorem finiteCachedFixedAlphaBlockVisitListStreamingCertificate_of_inputDrivenCore_completed
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
    (finalSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (hcompleted :
      let verifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
        machine input.length alpha block initialSlab visits hentries
      verifier.inputDrivenCore (fun bit => .bit bit)
          (finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length)
          (fun index => input.get index)
          (finiteCachedBlockVisitListFuel visits) verifier.start =
        .completed finalSlab) :
    FiniteCachedFixedAlphaBlockVisitListStreamingCertificate
      machine input alpha block initialSlab visits := by
  induction visits generalizing initialSlab finalSlab with
  | nil =>
      trivial
  | cons first rest ih =>
      let tailEntries : FixedAlphaBlockVisitEntriesInside alpha block rest :=
        fun visit hmem => hentries visit (by simp [hmem])
      let consVerifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
        machine input.length alpha block initialSlab (first :: rest) hentries
      let consSelector : consVerifier.State → Option (Fin input.length) :=
        finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length
      let inputBits : Fin input.length → Bool := fun index => input.get index
      let cursor : Fin (first :: rest).length := ⟨0, by simp⟩
      let firstEntry : WorkCellInSlab
          (advertisedBlockLower alpha.offsets block)
          (advertisedBlockWidth alpha.offsets block)
          first.entry.workHead.val := hentries first (by simp)
      let remaining := fixedAlphaVisitRemaining first
      let initial := finiteCachedStateOfVisitEntry machine alpha block first
        initialSlab firstEntry
      let shortPhase := runFiniteCachedVisitInputDriven machine input T
        (advertisedBlockWidth alpha.offsets block)
        (advertisedBlockLower alpha.offsets block)
        (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
        remaining.val (.running remaining initial)
      have hstart : consVerifier.start =
          .active cursor (.running remaining initial) := by
        change finiteCachedBlockVisitListStart machine alpha block initialSlab
          (first :: rest) hentries = _
        rw [finiteCachedBlockVisitListStart]
        split
        · simp [finiteCachedBlockVisitListActiveState, cursor, remaining,
            initial]
        · simp_all
      have hhead : consVerifier.inputDrivenCore (fun bit => .bit bit)
          consSelector inputBits first.steps consVerifier.start =
          liftFiniteCachedBlockVisitPhase cursor shortPhase := by
        rw [hstart]
        have hlift :=
          finiteCachedBlockVisitList_inputDrivenCore_active_eq_inputDriven
            machine input alpha block initialSlab (first :: rest) hentries
              cursor remaining initial
        simpa [consVerifier, consSelector, inputBits, shortPhase, remaining,
          initial] using hlift
      have hfuel : finiteCachedBlockVisitListFuel (first :: rest) =
          first.steps + 1 + finiteCachedBlockVisitListFuel rest := by
        simp [finiteCachedBlockVisitListFuel,
          fixedAlphaBlockVisitsTotalSteps]
        omega
      have hafter : consVerifier.inputDrivenCore (fun bit => .bit bit)
          consSelector inputBits (finiteCachedBlockVisitListFuel rest)
          (consVerifier.inputDrivenCore (fun bit => .bit bit) consSelector
            inputBits 1 (liftFiniteCachedBlockVisitPhase cursor shortPhase)) =
            .completed finalSlab := by
        change consVerifier.inputDrivenCore (fun bit => .bit bit) consSelector
          inputBits (finiteCachedBlockVisitListFuel (first :: rest))
            consVerifier.start = .completed finalSlab at hcompleted
        rw [hfuel] at hcompleted
        rw [consVerifier.inputDrivenCore_add (fun bit => .bit bit)
          consSelector inputBits (first.steps + 1)
            (finiteCachedBlockVisitListFuel rest)] at hcompleted
        rw [consVerifier.inputDrivenCore_add (fun bit => .bit bit)
          consSelector inputBits first.steps 1] at hcompleted
        rw [hhead] at hcompleted
        exact hcompleted
      have hshortHalted : finiteCachedVisitPhaseHalted shortPhase = true := by
        exact runFiniteCachedVisitInputDriven_halted_of_remaining machine input
          (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
          remaining initial
      cases hshort : shortPhase with
      | running otherRemaining otherLive =>
          have hzero : otherRemaining = 0 := by
            simpa [hshort, finiteCachedVisitPhaseHalted] using hshortHalted
          subst otherRemaining
          have hone : consVerifier.inputDrivenCore (fun bit => .bit bit)
              consSelector inputBits 1
              (liftFiniteCachedBlockVisitPhase cursor shortPhase) =
                .rejected := by
            rw [hshort]
            by_cases hneeds :
                cachedLocalStepNeedsUnread machine otherLive = true
            · by_cases hhead : otherLive.inputHead.val < input.length
              · simp [consVerifier, cursor,
                  FiniteStreamingVerifier.inputDrivenCore,
                  finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
                  finiteCachedBlockVisitListHalted,
                  finiteCachedBlockVisitListRequestsInput,
                  finiteCachedVisitPhaseRequestsInput,
                  finiteCachedBlockVisitListStreamingStep,
                  finiteCachedVisitStreamingStep,
                  liftFiniteCachedBlockVisitPhase, hneeds, hhead]
              · simp [consVerifier, cursor,
                  FiniteStreamingVerifier.inputDrivenCore,
                  finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
                  finiteCachedBlockVisitListHalted,
                  finiteCachedBlockVisitListRequestsInput,
                  finiteCachedVisitPhaseRequestsInput,
                  finiteCachedBlockVisitListStreamingStep,
                  finiteCachedVisitStreamingStep,
                  advanceFiniteCachedVisitPhase,
                  liftFiniteCachedBlockVisitPhase, hneeds, hhead]
            · simp [consVerifier, cursor,
                FiniteStreamingVerifier.inputDrivenCore,
                finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
                finiteCachedBlockVisitListHalted,
                finiteCachedBlockVisitListRequestsInput,
                finiteCachedVisitPhaseRequestsInput,
                finiteCachedBlockVisitListStreamingStep,
                finiteCachedVisitStreamingStep,
                advanceFiniteCachedVisitPhase,
                liftFiniteCachedBlockVisitPhase, hneeds]
          rw [hone] at hafter
          have htailFixed := consVerifier.inputDrivenCore_eq_self_of_halted
            (fun bit => .bit bit) consSelector inputBits
            (finiteCachedBlockVisitListFuel rest) .rejected rfl
          rw [htailFixed] at hafter
          contradiction
      | rejected failure =>
          have hone : consVerifier.inputDrivenCore (fun bit => .bit bit)
              consSelector inputBits 1
              (liftFiniteCachedBlockVisitPhase cursor shortPhase) =
                .rejected := by
            rw [hshort]
            exact consVerifier.inputDrivenCore_eq_self_of_halted
              (fun bit => .bit bit) consSelector inputBits 1 .rejected rfl
          rw [hone] at hafter
          have htailFixed := consVerifier.inputDrivenCore_eq_self_of_halted
            (fun bit => .bit bit) consSelector inputBits
            (finiteCachedBlockVisitListFuel rest) .rejected rfl
          rw [htailFixed] at hafter
          contradiction
      | completed firstFinal =>
          have hrunCompleted : runFiniteCachedVisitInputDriven machine input T
              (advertisedBlockWidth alpha.offsets block)
              (advertisedBlockLower alpha.offsets block)
              (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
              (fixedAlphaVisitRemaining first).val
              (.running (fixedAlphaVisitRemaining first)
                (finiteCachedStateOfVisitEntry machine alpha block first
                  initialSlab firstEntry)) = .completed firstFinal := by
            simpa [shortPhase, remaining, initial] using hshort
          have haccept : @finiteCachedVisitPhaseAccept
              (cachedInputMachine machine).State
              (cachedInputStateDecidableEq machine) T
              (advertisedBlockWidth alpha.offsets block) first.exit
              (.completed firstFinal) = true := by
            by_contra hnot
            have hboundaryRejected :
                consVerifier.inputDrivenCore (fun bit => .bit bit)
                  consSelector inputBits 1
                  (liftFiniteCachedBlockVisitPhase cursor shortPhase) =
                    .rejected := by
              rw [hshort]
              simp [consVerifier, cursor,
                FiniteStreamingVerifier.inputDrivenCore,
                finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
                finiteCachedBlockVisitListHalted,
                finiteCachedBlockVisitListRequestsInput,
                finiteCachedVisitPhaseRequestsInput,
                finiteCachedBlockVisitListStreamingStep,
                liftFiniteCachedBlockVisitPhase, hnot]
            rw [hboundaryRejected] at hafter
            have htailFixed := consVerifier.inputDrivenCore_eq_self_of_halted
              (fun bit => .bit bit) consSelector inputBits
              (finiteCachedBlockVisitListFuel rest) .rejected rfl
            rw [htailFixed] at hafter
            contradiction
          have hfirst :=
            finiteCachedFixedAlphaVisit_valid_and_outputSlab_of_inputDriven_completed
              machine input alpha block first initialSlab firstEntry firstFinal
                hrunCompleted haccept
          obtain ⟨certificateFinal, hstep⟩ :=
            (exists_finiteCachedFixedAlphaVisitStreamingStepCertificate_iff
              machine input alpha block first initialSlab).mpr hfirst.1
          cases rest with
          | nil =>
              exact ⟨certificateFinal, hstep, trivial⟩
          | cons second remainingVisits =>
              let tailVerifier :=
                finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine
                  input.length alpha block firstFinal.workSlab
                  (second :: remainingVisits) tailEntries
              let tailSelector : tailVerifier.State →
                  Option (Fin input.length) :=
                finiteCachedBlockVisitListAdaptiveQueryIndex? machine
                  input.length
              have hboundary : consVerifier.inputDrivenCore
                  (fun bit => .bit bit) consSelector inputBits 1
                  (liftFiniteCachedBlockVisitPhase cursor shortPhase) =
                prependFiniteCachedBlockVisitListState first
                  (second :: remainingVisits) tailVerifier.start := by
                rw [hshort]
                simp [consVerifier, tailVerifier, cursor,
                  FiniteStreamingVerifier.inputDrivenCore,
                  finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
                  finiteCachedBlockVisitListStart,
                  finiteCachedBlockVisitListHalted,
                  finiteCachedBlockVisitListRequestsInput,
                  finiteCachedVisitPhaseRequestsInput,
                  finiteCachedBlockVisitListStreamingStep,
                  finiteCachedBlockVisitListActiveState,
                  prependFiniteCachedBlockVisitListState,
                  liftFiniteCachedBlockVisitPhase, haccept]
              rw [hboundary] at hafter
              have hembed :=
                finiteCachedBlockVisitList_inputDrivenCore_prepend_twoStarts
                  machine input alpha block first (second :: remainingVisits)
                    initialSlab firstFinal.workSlab hentries tailEntries
                    (finiteCachedBlockVisitListFuel
                      (second :: remainingVisits)) tailVerifier.start
              have hprepTail : prependFiniteCachedBlockVisitListState first
                  (second :: remainingVisits)
                  (tailVerifier.inputDrivenCore (fun bit => .bit bit)
                    tailSelector inputBits
                    (finiteCachedBlockVisitListFuel
                      (second :: remainingVisits)) tailVerifier.start) =
                    .completed finalSlab := by
                calc
                  prependFiniteCachedBlockVisitListState first
                      (second :: remainingVisits)
                      (tailVerifier.inputDrivenCore (fun bit => .bit bit)
                        tailSelector inputBits
                        (finiteCachedBlockVisitListFuel
                          (second :: remainingVisits)) tailVerifier.start) =
                    consVerifier.inputDrivenCore (fun bit => .bit bit)
                      consSelector inputBits
                      (finiteCachedBlockVisitListFuel
                        (second :: remainingVisits))
                      (prependFiniteCachedBlockVisitListState first
                        (second :: remainingVisits) tailVerifier.start) := by
                          simpa [consVerifier, tailVerifier, consSelector,
                            tailSelector, inputBits] using hembed.symm
                  _ = .completed finalSlab := hafter
              cases htailResult : tailVerifier.inputDrivenCore
                  (fun bit => .bit bit) tailSelector inputBits
                  (finiteCachedBlockVisitListFuel
                    (second :: remainingVisits)) tailVerifier.start with
              | active tailCursor tailPhase =>
                  simp [htailResult,
                    prependFiniteCachedBlockVisitListState] at hprepTail
              | rejected =>
                  simp [htailResult,
                    prependFiniteCachedBlockVisitListState] at hprepTail
              | completed tailFinalSlab =>
                  have htailSlab : tailFinalSlab = finalSlab := by
                    simpa [htailResult,
                      prependFiniteCachedBlockVisitListState] using hprepTail
                  have htailCompleted : tailVerifier.inputDrivenCore
                      (fun bit => .bit bit) tailSelector inputBits
                      (finiteCachedBlockVisitListFuel
                        (second :: remainingVisits)) tailVerifier.start =
                        .completed finalSlab := by
                    rw [htailResult, htailSlab]
                  have htailCertificate := ih firstFinal.workSlab tailEntries
                    finalSlab (by
                      simpa [tailVerifier, tailSelector, inputBits] using
                        htailCompleted)
                  have hcertificateSlab := hstep.outputSlab_eq machine input
                    alpha block first initialSlab certificateFinal
                  have hcarry : certificateFinal.workSlab =
                      firstFinal.workSlab := hcertificateSlab.trans hfirst.2.symm
                  refine ⟨certificateFinal, hstep, ?_⟩
                  rw [hcarry]
                  exact htailCertificate

/-- Exact transition-plus-boundary fuel always leaves the list verifier in a
global terminal state, independently of semantic validity. -/
theorem finiteCachedBlockVisitList_inputDrivenCore_halted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits) :
    let verifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
      machine input.length alpha block initialSlab visits hentries
    verifier.halted
      (verifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length)
        (fun index => input.get index)
        (finiteCachedBlockVisitListFuel visits) verifier.start) = true := by
  induction visits generalizing initialSlab with
  | nil =>
      rfl
  | cons first rest ih =>
      let tailEntries : FixedAlphaBlockVisitEntriesInside alpha block rest :=
        fun visit hmem => hentries visit (by simp [hmem])
      let consVerifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
        machine input.length alpha block initialSlab (first :: rest) hentries
      let consSelector : consVerifier.State → Option (Fin input.length) :=
        finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length
      let inputBits : Fin input.length → Bool := fun index => input.get index
      let cursor : Fin (first :: rest).length := ⟨0, by simp⟩
      let firstEntry : WorkCellInSlab
          (advertisedBlockLower alpha.offsets block)
          (advertisedBlockWidth alpha.offsets block)
          first.entry.workHead.val := hentries first (by simp)
      let remaining := fixedAlphaVisitRemaining first
      let initial := finiteCachedStateOfVisitEntry machine alpha block first
        initialSlab firstEntry
      let shortPhase := runFiniteCachedVisitInputDriven machine input T
        (advertisedBlockWidth alpha.offsets block)
        (advertisedBlockLower alpha.offsets block)
        (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
        remaining.val (.running remaining initial)
      have hstart : consVerifier.start =
          .active cursor (.running remaining initial) := by
        change finiteCachedBlockVisitListStart machine alpha block initialSlab
          (first :: rest) hentries = _
        rw [finiteCachedBlockVisitListStart]
        split
        · simp [finiteCachedBlockVisitListActiveState, cursor, remaining,
            initial]
        · simp_all
      have hhead : consVerifier.inputDrivenCore (fun bit => .bit bit)
          consSelector inputBits first.steps consVerifier.start =
          liftFiniteCachedBlockVisitPhase cursor shortPhase := by
        rw [hstart]
        have hlift :=
          finiteCachedBlockVisitList_inputDrivenCore_active_eq_inputDriven
            machine input alpha block initialSlab (first :: rest) hentries
              cursor remaining initial
        simpa [consVerifier, consSelector, inputBits, shortPhase, remaining,
          initial] using hlift
      have hfuel : finiteCachedBlockVisitListFuel (first :: rest) =
          first.steps + 1 + finiteCachedBlockVisitListFuel rest := by
        simp [finiteCachedBlockVisitListFuel,
          fixedAlphaBlockVisitsTotalSteps]
        omega
      change consVerifier.halted
        (consVerifier.inputDrivenCore (fun bit => .bit bit) consSelector
          inputBits (finiteCachedBlockVisitListFuel (first :: rest))
            consVerifier.start) = true
      rw [hfuel]
      rw [consVerifier.inputDrivenCore_add (fun bit => .bit bit)
        consSelector inputBits (first.steps + 1)
          (finiteCachedBlockVisitListFuel rest)]
      rw [consVerifier.inputDrivenCore_add (fun bit => .bit bit)
        consSelector inputBits first.steps 1]
      rw [hhead]
      have hshortHalted : finiteCachedVisitPhaseHalted shortPhase = true :=
        runFiniteCachedVisitInputDriven_halted_of_remaining machine input
          (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
          remaining initial
      cases hshort : shortPhase with
      | running otherRemaining otherLive =>
          have hzero : otherRemaining = 0 := by
            simpa [hshort, finiteCachedVisitPhaseHalted] using hshortHalted
          subst otherRemaining
          have hone : consVerifier.inputDrivenCore (fun bit => .bit bit)
              consSelector inputBits 1
              (liftFiniteCachedBlockVisitPhase cursor shortPhase) =
                .rejected := by
            rw [hshort]
            by_cases hneeds :
                cachedLocalStepNeedsUnread machine otherLive = true
            · by_cases hinput : otherLive.inputHead.val < input.length
              · simp [consVerifier, cursor,
                  FiniteStreamingVerifier.inputDrivenCore,
                  finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
                  finiteCachedBlockVisitListHalted,
                  finiteCachedBlockVisitListRequestsInput,
                  finiteCachedVisitPhaseRequestsInput,
                  finiteCachedBlockVisitListStreamingStep,
                  finiteCachedVisitStreamingStep,
                  liftFiniteCachedBlockVisitPhase, hneeds, hinput]
              · simp [consVerifier, cursor,
                  FiniteStreamingVerifier.inputDrivenCore,
                  finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
                  finiteCachedBlockVisitListHalted,
                  finiteCachedBlockVisitListRequestsInput,
                  finiteCachedVisitPhaseRequestsInput,
                  finiteCachedBlockVisitListStreamingStep,
                  finiteCachedVisitStreamingStep,
                  advanceFiniteCachedVisitPhase,
                  liftFiniteCachedBlockVisitPhase, hneeds, hinput]
            · simp [consVerifier, cursor,
                FiniteStreamingVerifier.inputDrivenCore,
                finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
                finiteCachedBlockVisitListHalted,
                finiteCachedBlockVisitListRequestsInput,
                finiteCachedVisitPhaseRequestsInput,
                finiteCachedBlockVisitListStreamingStep,
                finiteCachedVisitStreamingStep,
                advanceFiniteCachedVisitPhase,
                liftFiniteCachedBlockVisitPhase, hneeds]
          have hone' := hone
          rw [hshort] at hone'
          rw [hone']
          rw [consVerifier.inputDrivenCore_eq_self_of_halted
            (fun bit => .bit bit) consSelector inputBits
            (finiteCachedBlockVisitListFuel rest) .rejected rfl]
          rfl
      | rejected failure =>
          change consVerifier.halted
            (consVerifier.inputDrivenCore (fun bit => .bit bit) consSelector
              inputBits (finiteCachedBlockVisitListFuel rest)
              (consVerifier.inputDrivenCore (fun bit => .bit bit)
                consSelector inputBits 1 .rejected)) = true
          rw [consVerifier.inputDrivenCore_eq_self_of_halted
            (fun bit => .bit bit) consSelector inputBits 1 .rejected rfl]
          rw [consVerifier.inputDrivenCore_eq_self_of_halted
            (fun bit => .bit bit) consSelector inputBits
            (finiteCachedBlockVisitListFuel rest) .rejected rfl]
          rfl
      | completed firstFinal =>
          by_cases haccept : @finiteCachedVisitPhaseAccept
              (cachedInputMachine machine).State
              (cachedInputStateDecidableEq machine) T
              (advertisedBlockWidth alpha.offsets block) first.exit
              (.completed firstFinal) = true
          · cases rest with
            | nil =>
                simp [consVerifier,
                  FiniteStreamingVerifier.inputDrivenCore,
                  finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
                  finiteCachedBlockVisitListHalted,
                  finiteCachedBlockVisitListRequestsInput,
                  finiteCachedVisitPhaseRequestsInput,
                  finiteCachedBlockVisitListStreamingStep,
                  liftFiniteCachedBlockVisitPhase,
                  finiteCachedBlockVisitListFuel,
                  fixedAlphaBlockVisitsTotalSteps, haccept]
            | cons second remainingVisits =>
                let tailVerifier :=
                  finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine
                    input.length alpha block firstFinal.workSlab
                    (second :: remainingVisits) tailEntries
                let tailSelector : tailVerifier.State →
                    Option (Fin input.length) :=
                  finiteCachedBlockVisitListAdaptiveQueryIndex? machine
                    input.length
                have hboundary : consVerifier.inputDrivenCore
                    (fun bit => .bit bit) consSelector inputBits 1
                    (liftFiniteCachedBlockVisitPhase cursor shortPhase) =
                  prependFiniteCachedBlockVisitListState first
                    (second :: remainingVisits) tailVerifier.start := by
                  rw [hshort]
                  simp [consVerifier, tailVerifier, cursor,
                    FiniteStreamingVerifier.inputDrivenCore,
                    finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
                    finiteCachedBlockVisitListStart,
                    finiteCachedBlockVisitListHalted,
                    finiteCachedBlockVisitListRequestsInput,
                    finiteCachedVisitPhaseRequestsInput,
                    finiteCachedBlockVisitListStreamingStep,
                    finiteCachedBlockVisitListActiveState,
                    prependFiniteCachedBlockVisitListState,
                    liftFiniteCachedBlockVisitPhase, haccept]
                have hboundary' := hboundary
                rw [hshort] at hboundary'
                rw [hboundary']
                have hembed :=
                  finiteCachedBlockVisitList_inputDrivenCore_prepend_twoStarts
                    machine input alpha block first
                      (second :: remainingVisits) initialSlab
                      firstFinal.workSlab hentries tailEntries
                      (finiteCachedBlockVisitListFuel
                        (second :: remainingVisits)) tailVerifier.start
                have hembed' : consVerifier.inputDrivenCore
                    (fun bit => .bit bit) consSelector inputBits
                    (finiteCachedBlockVisitListFuel
                      (second :: remainingVisits))
                    (prependFiniteCachedBlockVisitListState first
                      (second :: remainingVisits) tailVerifier.start) =
                  prependFiniteCachedBlockVisitListState first
                    (second :: remainingVisits)
                    (tailVerifier.inputDrivenCore (fun bit => .bit bit)
                      tailSelector inputBits
                      (finiteCachedBlockVisitListFuel
                        (second :: remainingVisits)) tailVerifier.start) := by
                  simpa [consVerifier, tailVerifier, consSelector,
                    tailSelector, inputBits] using hembed
                rw [hembed']
                change finiteCachedBlockVisitListHalted
                  (prependFiniteCachedBlockVisitListState first
                    (second :: remainingVisits)
                    (tailVerifier.inputDrivenCore (fun bit => .bit bit)
                      tailSelector inputBits
                      (finiteCachedBlockVisitListFuel
                        (second :: remainingVisits)) tailVerifier.start)) = true
                rw [finiteCachedBlockVisitListHalted_prepend]
                simpa [tailVerifier, tailSelector, inputBits] using
                  ih firstFinal.workSlab tailEntries
          · have hboundary : consVerifier.inputDrivenCore
                (fun bit => .bit bit) consSelector inputBits 1
                (liftFiniteCachedBlockVisitPhase cursor shortPhase) =
              .rejected := by
              rw [hshort]
              simp [consVerifier, cursor,
                FiniteStreamingVerifier.inputDrivenCore,
                finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
                finiteCachedBlockVisitListHalted,
                finiteCachedBlockVisitListRequestsInput,
                finiteCachedVisitPhaseRequestsInput,
                finiteCachedBlockVisitListStreamingStep,
                liftFiniteCachedBlockVisitPhase, haccept]
            have hboundary' := hboundary
            rw [hshort] at hboundary'
            rw [hboundary']
            rw [consVerifier.inputDrivenCore_eq_self_of_halted
              (fun bit => .bit bit) consSelector inputBits
              (finiteCachedBlockVisitListFuel rest) .rejected rfl]
            rfl

/-- Unconditional soundness of the adaptive list compiler on the canonical
Boolean input view. -/
theorem compileAdaptiveFiniteCachedFixedAlphaBlockVisitList_replayAccepted_of_eval_eq_true
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
    (heval : (compileAdaptiveFiniteCachedFixedAlphaBlockVisitList machine alpha
      block initialSlab visits hentries).eval
        (fun index => input.get index) = true) :
    FixedAlphaBlockVisitReplayAccepted (cachedInputMachine machine) input
      alpha block initialSlab visits := by
  let verifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
    machine input.length alpha block initialSlab visits hentries
  let selector : verifier.State → Option (Fin input.length) :=
    finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length
  let inputBits : Fin input.length → Bool := fun index => input.get index
  let fuel := finiteCachedBlockVisitListFuel visits
  have htotal : ∀ state, verifier.requestsInput state = true →
      ∃ index, selector state = some index := by
    intro state hrequest
    exact finiteCachedBlockVisitListAdaptiveQueryIndex?_total_of_requestsInput
      machine input.length state hrequest
  have hrunPhase :
      (verifier.runAdaptive fuel (fun bit => .bit bit) selector inputBits).1 =
      verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits fuel
        verifier.start := by
    simpa [FiniteStreamingVerifier.runAdaptive,
      FiniteStreamingVerifier.initialFueledState] using
        verifier.runAdaptiveFrom_state_eq_inputDrivenCore_of_fuel_le_layers
          (fun bit => .bit bit) selector inputBits htotal
          (verifier.initialFueledState fuel) fuel le_rfl
  have hcoreHalted : verifier.halted
      (verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits fuel
        verifier.start) = true := by
    simpa [verifier, selector, inputBits, fuel] using
      finiteCachedBlockVisitList_inputDrivenCore_halted machine input alpha
        block initialSlab visits hentries
  have hrunHalted : verifier.halted
      (verifier.runAdaptive fuel (fun bit => .bit bit) selector inputBits).1 =
        true := by
    rw [hrunPhase]
    exact hcoreHalted
  have hfinish : verifier.finishWithEndSymbol .rightEnd
      (verifier.runAdaptive fuel (fun bit => .bit bit) selector inputBits) =
      (verifier.runAdaptive fuel (fun bit => .bit bit) selector inputBits).1 :=
    verifier.finishWithEndSymbol_eq_of_halted .rightEnd _ hrunHalted
  change (verifier.compileAdaptive fuel input.length (fun bit => .bit bit)
      .rightEnd selector).eval inputBits = true at heval
  rw [FiniteStreamingVerifier.compileAdaptive_eval] at heval
  rw [hfinish] at heval
  change finiteCachedBlockVisitListAccept
      (verifier.runAdaptive fuel (fun bit => .bit bit) selector
        inputBits).1 = true at heval
  cases hrunState :
      (verifier.runAdaptive fuel (fun bit => .bit bit) selector inputBits).1
      with
  | active cursor phase =>
      rw [hrunState] at heval
      simp [finiteCachedBlockVisitListAccept] at heval
  | rejected =>
      rw [hrunState] at heval
      simp [finiteCachedBlockVisitListAccept] at heval
  | completed finalSlab =>
      have hcoreCompleted : verifier.inputDrivenCore (fun bit => .bit bit)
          selector inputBits fuel verifier.start = .completed finalSlab :=
        hrunPhase.symm.trans hrunState
      have hcertificate :=
        finiteCachedFixedAlphaBlockVisitListStreamingCertificate_of_inputDrivenCore_completed
          machine input alpha block initialSlab visits hentries finalSlab
            (by simpa [verifier, selector, inputBits, fuel] using hcoreCompleted)
      exact
        (finiteCachedFixedAlphaBlockVisitListStreamingCertificate_iff
          machine input alpha block initialSlab visits).mp hcertificate

/-- Exact semantic correctness of the adaptive list compiler on the canonical
input view.  Chronological separation remains a separate public-list check;
this theorem characterizes precisely the slab-threaded replay component. -/
theorem compileAdaptiveFiniteCachedFixedAlphaBlockVisitList_eval_eq_true_iff_replayAccepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits) :
    (compileAdaptiveFiniteCachedFixedAlphaBlockVisitList machine alpha block
      initialSlab visits hentries).eval (fun index => input.get index) = true ↔
      FixedAlphaBlockVisitReplayAccepted (cachedInputMachine machine) input
        alpha block initialSlab visits := by
  constructor
  · exact
      compileAdaptiveFiniteCachedFixedAlphaBlockVisitList_replayAccepted_of_eval_eq_true
        machine input alpha block initialSlab visits hentries
  · exact
      compileAdaptiveFiniteCachedFixedAlphaBlockVisitList_eval_eq_true_of_replayAccepted
        machine input alpha block initialSlab visits hentries

end OneTapeMagnification
end Frontier
end Pnp4
