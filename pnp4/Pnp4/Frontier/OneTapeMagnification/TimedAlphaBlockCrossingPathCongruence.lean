import Pnp4.Frontier.OneTapeMagnification.AcceptedMasterOrderExecution
import Pnp4.Frontier.OneTapeMagnification.AdaptiveCachedBlockVisitListSoundness
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedBlockVisitListRollingOperational
import Pnp4.Frontier.OneTapeMagnification.OnePassAdvertisedBlockCutCheck

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Crossing-counter congruence on one advertised block path

An accepted fixed-alpha block-list replay exposes exactly its advertised
fresh-coordinate path.  Agreement on that path therefore preserves the
entire rolling-verifier state, not only acceptance.  In particular it
preserves every carried crossing counter, the adjacent two-window counter
vector, and (under the usual total-step budget) the full semantic crossing
profile.
-/

local instance scratchCachedStateDecidableEq
    (machine : DeterministicMachine) [DecidableEq machine.State] :
    DecidableEq (cachedInputMachine machine).State :=
  cachedInputStateDecidableEq machine

private def inputViewAtLength {n : Nat} (input : List Bool)
    (hlength : input.length = n) : Fin n -> Bool :=
  fun coordinate => input.get (Fin.cast hlength.symm coordinate)

private theorem rollingBlockList_inputDrivenCore_completed_atLength
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b m : Nat} (input : List Bool) (hlength : input.length = n)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (boundaries : Fin m -> Nat)
    (initialCounters : BoundedCrossingCounterVector T m)
    (haccepted : FixedAlphaBlockVisitReplayAccepted
      (cachedInputMachine machine) input alpha block initialSlab visits) :
    let rolling :=
      finiteCachedFixedAlphaBlockVisitListRollingStreamingVerifier machine n
        alpha block initialSlab visits hentries boundaries initialCounters
    let selector :=
      finiteCachedBlockVisitListRollingAdaptiveQueryIndex? machine n
    let result := runFiniteCachedFixedAlphaBlockVisitListRollingCounters
      machine input alpha block boundaries visits hentries initialSlab
        initialCounters
    rolling.inputDrivenCore (fun bit => .bit bit) selector
      (inputViewAtLength input hlength)
      (finiteCachedBlockVisitListFuel visits) rolling.start =
        ⟨.completed result.finalSlab, result.counters⟩ := by
  subst n
  simpa [inputViewAtLength] using
    (finiteCachedBlockVisitListRolling_inputDrivenCore_completed_of_replayAccepted
      machine input alpha block initialSlab visits hentries boundaries
        initialCounters haccepted)

private theorem blockListCertificate_of_inputDrivenCore_completed_atLength
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat} (input : List Bool) (hlength : input.length = n)
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
      let ordinary := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
        machine n alpha block initialSlab visits hentries
      ordinary.inputDrivenCore (fun bit => .bit bit)
          (finiteCachedBlockVisitListAdaptiveQueryIndex? machine n)
          (inputViewAtLength input hlength)
          (finiteCachedBlockVisitListFuel visits) ordinary.start =
        .completed finalSlab) :
    FiniteCachedFixedAlphaBlockVisitListStreamingCertificate machine input
      alpha block initialSlab visits := by
  subst n
  apply
    finiteCachedFixedAlphaBlockVisitListStreamingCertificate_of_inputDrivenCore_completed
      machine input alpha block initialSlab visits hentries finalSlab
  simpa [inputViewAtLength] using hcompleted

/-- Erase the rolling counters from an exact one-block-list trace. -/
private theorem rollingBlockListExactAdaptiveQueryOrder_erase
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b m : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (boundaries : Fin m -> Nat)
    (initialCounters : BoundedCrossingCounterVector T m)
    (input : Fin n -> Bool)
    {steps : Nat}
    {start target : FiniteCachedBlockVisitListRollingCounterState
      (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block) visits.length m}
    {queries : List (Fin n)}
    (trace :
      let rolling :=
        finiteCachedFixedAlphaBlockVisitListRollingStreamingVerifier machine n
          alpha block initialSlab visits hentries boundaries initialCounters
      FiniteStreamingVerifier.ExactAdaptiveQueryOrder rolling
        (fun bit => .bit bit)
        (finiteCachedBlockVisitListRollingAdaptiveQueryIndex? machine n)
        input steps start queries target) :
    let ordinary := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
      machine n alpha block initialSlab visits hentries
    FiniteStreamingVerifier.ExactAdaptiveQueryOrder ordinary
      (fun bit => .bit bit)
      (finiteCachedBlockVisitListAdaptiveQueryIndex? machine n)
      input steps start.listState queries target.listState := by
  dsimp only at trace ⊢
  let rolling :=
    finiteCachedFixedAlphaBlockVisitListRollingStreamingVerifier machine n
      alpha block initialSlab visits hentries boundaries initialCounters
  let ordinary := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
    machine n alpha block initialSlab visits hentries
  let rollingSelector : rolling.State -> Option (Fin n) :=
    finiteCachedBlockVisitListRollingAdaptiveQueryIndex? machine n
  let ordinarySelector : ordinary.State -> Option (Fin n) :=
    finiteCachedBlockVisitListAdaptiveQueryIndex? machine n
  let erase : rolling.State -> ordinary.State := fun state => state.listState
  change FiniteStreamingVerifier.ExactAdaptiveQueryOrder rolling
    (fun bit => .bit bit) rollingSelector input steps start queries target
      at trace
  change FiniteStreamingVerifier.ExactAdaptiveQueryOrder ordinary
    (fun bit => .bit bit) ordinarySelector input steps (erase start) queries
      (erase target)
  have hrollingTargetHalted : rolling.halted target = true :=
    FiniteStreamingVerifier.ExactAdaptiveQueryOrder.target_halted rolling
      (fun bit => .bit bit) rollingSelector input trace
  have hordinaryTargetHalted : ordinary.halted (erase target) = true := by
    exact hrollingTargetHalted
  have terminal : FiniteStreamingVerifier.ExactAdaptiveQueryOrder ordinary
      (fun bit => .bit bit) ordinarySelector input 0 (erase target) []
        (erase target) :=
    FiniteStreamingVerifier.ExactAdaptiveQueryOrder.halted _
      hordinaryTargetHalted
  have hhalted : forall state, rolling.halted state = false ->
      ordinary.halted (erase state) = false := by
    intro state hstate
    exact hstate
  have hrequests : forall state, rolling.halted state = false ->
      ordinary.requestsInput (erase state) = rolling.requestsInput state := by
    intro state _
    rfl
  have hselector : forall state, rolling.halted state = false ->
      ordinarySelector (erase state) = rollingSelector state := by
    intro state _
    rfl
  have hstep : forall state supplied, rolling.halted state = false ->
      ordinary.step (erase state) supplied = erase (rolling.step state supplied) := by
    intro state supplied _
    exact (finiteCachedBlockVisitListStreamingRollingCounterStep_listState
      machine n alpha block visits hentries boundaries state supplied).symm
  have mapped :=
    FiniteStreamingVerifier.ExactAdaptiveQueryOrder.map_append rolling ordinary
      (fun bit => .bit bit) rollingSelector ordinarySelector input erase
        hhalted hrequests hselector hstep trace terminal
  simpa using mapped

/-- On an accepted source, the rolling verifier exposes the advertised order. -/
private theorem rollingBlockList_queryTrace_eq_advertised_of_replayAccepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b m : Nat}
    (input : List Bool) (hlength : input.length = n)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (boundaries : Fin m -> Nat)
    (initialCounters : BoundedCrossingCounterVector T m)
    (haccepted : FixedAlphaBlockVisitReplayAccepted
      (cachedInputMachine machine) input alpha block initialSlab visits) :
    let rolling :=
      finiteCachedFixedAlphaBlockVisitListRollingStreamingVerifier machine n
        alpha block initialSlab visits hentries boundaries initialCounters
    let selector :=
      finiteCachedBlockVisitListRollingAdaptiveQueryIndex? machine n
    (rolling.compileAdaptive (finiteCachedBlockVisitListFuel visits) n
      (fun bit => .bit bit) .rightEnd selector).queryTrace
        (inputViewAtLength input hlength) =
        finiteCachedBlockVisitListAdvertisedQueryOrder n visits := by
  subst n
  dsimp only
  let rolling :=
    finiteCachedFixedAlphaBlockVisitListRollingStreamingVerifier machine
      input.length
      alpha block initialSlab visits hentries boundaries initialCounters
  let ordinary := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
    machine input.length alpha block initialSlab visits hentries
  let rollingSelector : rolling.State -> Option (Fin input.length) :=
    finiteCachedBlockVisitListRollingAdaptiveQueryIndex? machine input.length
  let ordinarySelector : ordinary.State -> Option (Fin input.length) :=
    finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length
  let inputBits : Fin input.length -> Bool := fun index => input.get index
  let fuel := finiteCachedBlockVisitListFuel visits
  let result := runFiniteCachedFixedAlphaBlockVisitListRollingCounters
    machine input alpha block boundaries visits hentries initialSlab
      initialCounters
  have hcore : rolling.inputDrivenCore (fun bit => .bit bit)
      rollingSelector inputBits fuel rolling.start =
        ⟨.completed result.finalSlab, result.counters⟩ := by
    simpa [rolling, rollingSelector, inputBits, fuel, result] using
      (rollingBlockList_inputDrivenCore_completed_atLength machine input rfl
        alpha block initialSlab visits hentries boundaries initialCounters
          haccepted)
  have hhalted : rolling.halted
      (rolling.inputDrivenCore (fun bit => .bit bit) rollingSelector inputBits
        fuel rolling.start) = true := by
    rw [hcore]
    rfl
  have htotal : forall state, rolling.requestsInput state = true ->
      exists index, rollingSelector state = some index := by
    intro state hrequest
    exact finiteCachedBlockVisitListAdaptiveQueryIndex?_total_of_requestsInput
      machine input.length state.listState hrequest
  obtain ⟨steps, queries, hsteps, rollingTrace⟩ :=
    FiniteStreamingVerifier.exists_exactAdaptiveQueryOrder_of_inputDrivenCore_halted
      rolling (fun bit => .bit bit) rollingSelector inputBits htotal fuel
        rolling.start hhalted
  have erasedTrace := rollingBlockListExactAdaptiveQueryOrder_erase
    machine alpha block initialSlab visits hentries boundaries initialCounters
      inputBits rollingTrace
  have herasedStart : rolling.start.listState = ordinary.start := rfl
  rw [herasedStart] at erasedTrace
  have erasedTrace' : FiniteStreamingVerifier.ExactAdaptiveQueryOrder ordinary
      (fun bit => .bit bit) ordinarySelector inputBits steps ordinary.start queries
      (rolling.inputDrivenCore (fun bit => .bit bit) rollingSelector inputBits
        fuel rolling.start).listState := by
    simpa [rolling, ordinary, rollingSelector, ordinarySelector, inputBits] using
      erasedTrace
  have hcertificate :=
    (finiteCachedFixedAlphaBlockVisitListStreamingCertificate_iff
      machine input alpha block initialSlab visits).mpr haccepted
  obtain ⟨ordinaryFinal, ordinaryTrace⟩ :=
    finiteCachedBlockVisitList_exactAdaptiveQueryOrder_of_certificate
      machine input alpha block initialSlab visits hentries hcertificate
  have ordinaryTrace' : FiniteStreamingVerifier.ExactAdaptiveQueryOrder ordinary
      (fun bit => .bit bit) ordinarySelector inputBits fuel ordinary.start
      (finiteCachedBlockVisitListAdvertisedQueryOrder input.length visits)
      (.completed ordinaryFinal) := by
    simpa [ordinary, ordinarySelector, inputBits, fuel] using ordinaryTrace
  have hqueries : queries =
      finiteCachedBlockVisitListAdvertisedQueryOrder input.length visits :=
    FiniteStreamingVerifier.ExactAdaptiveQueryOrder.queries_eq_of_same_start
      ordinary (fun bit => .bit bit) ordinarySelector inputBits erasedTrace'
        ordinaryTrace'
  have htrace :=
    FiniteStreamingVerifier.ExactAdaptiveQueryOrder.compileAdaptive_queryTrace_eq
      rolling (fun bit => .bit bit) .rightEnd rollingSelector inputBits
        rollingTrace hsteps
  simpa [inputViewAtLength, inputBits] using htrace.trans hqueries

/-- Equality of all one-pass crossing counters under source-path agreement. -/
theorem onePassFixedAlphaBlockListFrom_counters_eq_of_pathAgreement
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b m : Nat}
    (source candidate : Fin n -> Bool)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (boundaries : Fin m -> Nat)
    (initialCounters : BoundedCrossingCounterVector T m)
    (hsource : FixedAlphaBlockVisitReplayAccepted
      (cachedInputMachine machine) (List.ofFn source) alpha block initialSlab
        visits)
    (hagree : forall coordinate,
      coordinate ∈ finiteCachedBlockVisitListAdvertisedQueryOrder n visits ->
        candidate coordinate = source coordinate) :
    (onePassFixedAlphaBlockListFrom (cachedInputMachine machine)
      (List.ofFn candidate) alpha block boundaries initialSlab initialCounters
        visits).counters =
    (onePassFixedAlphaBlockListFrom (cachedInputMachine machine)
      (List.ofFn source) alpha block boundaries initialSlab initialCounters
        visits).counters := by
  let sourceInput := List.ofFn source
  let candidateInput := List.ofFn candidate
  have hsourceLength : sourceInput.length = n := by
    simp [sourceInput]
  have hcandidateLength : candidateInput.length = n := by
    simp [candidateInput]
  have hsourceView : inputViewAtLength sourceInput hsourceLength = source := by
    funext coordinate
    simp [inputViewAtLength, sourceInput]
  have hcandidateView :
      inputViewAtLength candidateInput hcandidateLength = candidate := by
    funext coordinate
    simp [inputViewAtLength, candidateInput]
  let hentries : FixedAlphaBlockVisitEntriesInside alpha block visits :=
    fixedAlphaBlockVisitEntriesInside_of_replayAccepted
      (cachedInputMachine machine) sourceInput alpha block initialSlab visits
        hsource
  let rolling :=
    finiteCachedFixedAlphaBlockVisitListRollingStreamingVerifier machine n
      alpha block initialSlab visits hentries boundaries initialCounters
  let selector : rolling.State -> Option (Fin n) :=
    finiteCachedBlockVisitListRollingAdaptiveQueryIndex? machine n
  let fuel := finiteCachedBlockVisitListFuel visits
  let program := rolling.compileAdaptive fuel n (fun bit => .bit bit)
    .rightEnd selector
  have hsourceTrace : program.queryTrace source =
      finiteCachedBlockVisitListAdvertisedQueryOrder n visits := by
    simpa [program, rolling, selector, fuel, hsourceView] using
      (rollingBlockList_queryTrace_eq_advertised_of_replayAccepted
        machine sourceInput hsourceLength alpha block initialSlab visits
          hentries boundaries initialCounters hsource)
  have hpath : program.InputsAgreeOnQueryTrace source candidate := by
    intro coordinate hcoordinate
    apply hagree coordinate
    simpa [hsourceTrace] using hcoordinate
  have hprogramFinal : program.finalState candidate =
      program.finalState source :=
    program.finalState_eq_of_inputsAgreeOnQueryTrace source candidate hpath
  have htotal : forall state, rolling.requestsInput state = true ->
      exists index, selector state = some index := by
    intro state hrequest
    exact finiteCachedBlockVisitListAdaptiveQueryIndex?_total_of_requestsInput
      machine n state.listState hrequest
  have hrunSource :
      (rolling.runAdaptive fuel (fun bit => .bit bit) selector source).1 =
        rolling.inputDrivenCore (fun bit => .bit bit) selector source fuel
          rolling.start := by
    simpa [FiniteStreamingVerifier.runAdaptive,
      FiniteStreamingVerifier.initialFueledState] using
        rolling.runAdaptiveFrom_state_eq_inputDrivenCore_of_fuel_le_layers
          (fun bit => .bit bit) selector source htotal
          (rolling.initialFueledState fuel) fuel le_rfl
  have hrunCandidate :
      (rolling.runAdaptive fuel (fun bit => .bit bit) selector candidate).1 =
        rolling.inputDrivenCore (fun bit => .bit bit) selector candidate fuel
          rolling.start := by
    simpa [FiniteStreamingVerifier.runAdaptive,
      FiniteStreamingVerifier.initialFueledState] using
        rolling.runAdaptiveFrom_state_eq_inputDrivenCore_of_fuel_le_layers
          (fun bit => .bit bit) selector candidate htotal
          (rolling.initialFueledState fuel) fuel le_rfl
  have hrunEq : rolling.inputDrivenCore (fun bit => .bit bit) selector
      candidate fuel rolling.start =
      rolling.inputDrivenCore (fun bit => .bit bit) selector source fuel
        rolling.start := by
    have hstates : rolling.runAdaptive fuel (fun bit => .bit bit) selector
        candidate = rolling.runAdaptive fuel (fun bit => .bit bit) selector
          source := by
      exact
        (rolling.compileAdaptive_finalState fuel n (fun bit => .bit bit)
          .rightEnd selector candidate).symm.trans
          (hprogramFinal.trans
            (rolling.compileAdaptive_finalState fuel n
              (fun bit => .bit bit) .rightEnd selector source))
    have hfirst := congrArg Prod.fst hstates
    exact hrunCandidate.symm.trans (hfirst.trans hrunSource)
  let sourceResult := runFiniteCachedFixedAlphaBlockVisitListRollingCounters
    machine sourceInput alpha block boundaries visits hentries initialSlab
      initialCounters
  have hsourceCore : rolling.inputDrivenCore (fun bit => .bit bit) selector
      source fuel rolling.start =
        ⟨.completed sourceResult.finalSlab, sourceResult.counters⟩ := by
    simpa [rolling, selector, fuel, sourceResult, hsourceView] using
      (rollingBlockList_inputDrivenCore_completed_atLength machine sourceInput
        hsourceLength alpha block initialSlab visits hentries boundaries
          initialCounters hsource)
  have hcandidateCore : rolling.inputDrivenCore (fun bit => .bit bit) selector
      candidate fuel rolling.start =
        ⟨.completed sourceResult.finalSlab, sourceResult.counters⟩ :=
    hrunEq.trans hsourceCore
  let ordinary := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
    machine n alpha block initialSlab visits hentries
  have hcandidateOrdinaryCore : ordinary.inputDrivenCore
      (fun bit => .bit bit)
      (finiteCachedBlockVisitListAdaptiveQueryIndex? machine n)
      candidate fuel ordinary.start = .completed sourceResult.finalSlab := by
    have herase := finiteCachedBlockVisitListRolling_inputDrivenCore_listState
      machine alpha block initialSlab visits hentries boundaries
        initialCounters candidate fuel rolling.start
    change (rolling.inputDrivenCore (fun bit => .bit bit) selector candidate
        fuel rolling.start).listState =
      ordinary.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedBlockVisitListAdaptiveQueryIndex? machine n)
        candidate fuel ordinary.start at herase
    rw [hcandidateCore] at herase
    exact herase.symm
  have hcandidateCertificate :
      FiniteCachedFixedAlphaBlockVisitListStreamingCertificate machine
        candidateInput alpha block initialSlab visits :=
    blockListCertificate_of_inputDrivenCore_completed_atLength
      machine candidateInput hcandidateLength alpha block initialSlab visits
        hentries sourceResult.finalSlab (by
          simpa [ordinary, fuel, hcandidateView] using hcandidateOrdinaryCore)
  have hcandidate : FixedAlphaBlockVisitReplayAccepted
      (cachedInputMachine machine) candidateInput alpha block initialSlab
        visits :=
    (finiteCachedFixedAlphaBlockVisitListStreamingCertificate_iff
      machine candidateInput alpha block initialSlab visits).mp
        hcandidateCertificate
  let candidateResult := runFiniteCachedFixedAlphaBlockVisitListRollingCounters
    machine candidateInput alpha block boundaries visits hentries initialSlab
      initialCounters
  have hcandidateCore' : rolling.inputDrivenCore (fun bit => .bit bit)
      selector candidate fuel rolling.start =
        ⟨.completed candidateResult.finalSlab, candidateResult.counters⟩ := by
    simpa [rolling, selector, fuel, candidateResult, hcandidateView] using
      (rollingBlockList_inputDrivenCore_completed_atLength machine
        candidateInput hcandidateLength alpha block initialSlab visits
          hentries boundaries initialCounters hcandidate)
  have hrollingCounters : candidateResult.counters = sourceResult.counters := by
    rw [hcandidateCore] at hcandidateCore'
    exact (congrArg
      FiniteCachedBlockVisitListRollingCounterState.counters
      hcandidateCore').symm
  have hcandidateSemantic :=
    runFiniteCachedFixedAlphaBlockVisitListRollingCounters_counters_eq_onePass_of_replayAccepted
      machine candidateInput alpha block boundaries visits initialSlab
        initialCounters hcandidate
  have hsourceSemantic :=
    runFiniteCachedFixedAlphaBlockVisitListRollingCounters_counters_eq_onePass_of_replayAccepted
      machine sourceInput alpha block boundaries visits initialSlab
        initialCounters hsource
  dsimp only at hcandidateSemantic hsourceSemantic
  exact hcandidateSemantic.symm.trans
    (hrollingCounters.trans hsourceSemantic)

/-- The concrete adjacent-two-window counter vector is path-local. -/
theorem onePassAdvertisedBlockTwoWindowRun_counters_eq_of_pathAgreement
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (source candidate : Fin n -> Bool)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hsource : FixedAlphaBlockVisitReplayAccepted
      (cachedInputMachine machine) (List.ofFn source) alpha block initialSlab
        visits)
    (hagree : forall coordinate,
      coordinate ∈ finiteCachedBlockVisitListAdvertisedQueryOrder n visits ->
        candidate coordinate = source coordinate) :
    (onePassAdvertisedBlockTwoWindowRun (cachedInputMachine machine)
      (List.ofFn candidate) alpha block initialSlab visits).counters =
    (onePassAdvertisedBlockTwoWindowRun (cachedInputMachine machine)
      (List.ofFn source) alpha block initialSlab visits).counters := by
  unfold onePassAdvertisedBlockTwoWindowRun onePassFixedAlphaBlockList
  exact onePassFixedAlphaBlockListFrom_counters_eq_of_pathAgreement
    machine source candidate alpha block initialSlab visits
      (advertisedBlockTwoWindowBoundaries block)
      (zeroBoundedCrossingCounterVector T (b + b)) hsource hagree

/-- With the schedule-supplied total-step budget, path-local bounded-counter
equality upgrades to equality of the complete semantic crossing profile. -/
theorem fixedAlphaBlockVisitListCrossingProfile_eq_of_pathAgreement
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (source candidate : Fin n -> Bool)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hsource : FixedAlphaBlockVisitReplayAccepted
      (cachedInputMachine machine) (List.ofFn source) alpha block initialSlab
        visits)
    (hagree : forall coordinate,
      coordinate ∈ finiteCachedBlockVisitListAdvertisedQueryOrder n visits ->
        candidate coordinate = source coordinate)
    (hsteps : fixedAlphaBlockVisitsTotalSteps visits <= T) :
    fixedAlphaBlockVisitListCrossingProfile (cachedInputMachine machine)
      (List.ofFn candidate) alpha block initialSlab visits =
    fixedAlphaBlockVisitListCrossingProfile (cachedInputMachine machine)
      (List.ofFn source) alpha block initialSlab visits := by
  funext boundary
  let boundaries : Fin T -> Nat := fun index => index.val
  have hcounters :=
    onePassFixedAlphaBlockListFrom_counters_eq_of_pathAgreement
      machine source candidate alpha block initialSlab visits boundaries
        (zeroBoundedCrossingCounterVector T T) hsource hagree
  have hcoordinate := congrArg
    (fun counters => (counters boundary).val) hcounters
  dsimp only at hcoordinate
  rw [onePassFixedAlphaBlockListFrom_counter_val
    (cachedInputMachine machine) (List.ofFn candidate) alpha block boundaries
      initialSlab (zeroBoundedCrossingCounterVector T T) visits
      (by
        intro index
        simpa [zeroBoundedCrossingCounterVector] using hsteps) boundary]
      at hcoordinate
  rw [onePassFixedAlphaBlockListFrom_counter_val
    (cachedInputMachine machine) (List.ofFn source) alpha block boundaries
      initialSlab (zeroBoundedCrossingCounterVector T T) visits
      (by
        intro index
        simpa [zeroBoundedCrossingCounterVector] using hsteps) boundary]
      at hcoordinate
  simpa [fixedAlphaBlockVisitListCrossingProfile, boundaries,
    zeroBoundedCrossingCounterVector] using hcoordinate

end OneTapeMagnification
end Frontier
end Pnp4
