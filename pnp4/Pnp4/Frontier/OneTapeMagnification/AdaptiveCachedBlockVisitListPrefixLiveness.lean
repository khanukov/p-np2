import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.AdaptiveCachedBlockVisitListSegmentCorrectness

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Strict-prefix liveness for the cached block-visit list

The list verifier advertises exactly one microstep for every machine
transition and one endpoint/carry microstep for every visit.  This file proves
that a semantically certified run cannot reach a global terminal state before
that fuel is exhausted.

The proof isolates a structural remaining-fuel potential.  A state from which
global completion is still possible cannot lose more than one unit of this
potential in one input-driven microstep.  The start potential is exactly
`finiteCachedBlockVisitListFuel`.
-/

/-- Remaining transition counter of one local cached phase. -/
def finiteCachedVisitPhaseFuel
    {State : Type} {T w : Nat} :
    FiniteCachedVisitStreamingState State T w -> Nat
  | .running remaining _ => remaining.val
  | .completed _ => 0
  | .rejected _ => 0

/-- States which have not structurally ruled out later global completion.
This is only a necessary condition: endpoint mismatch may still reject a
locally completed phase. -/
def FiniteCachedBlockVisitListPotentiallyCompletable
    {State : Type} {T w k : Nat} :
    FiniteCachedBlockVisitListStreamingState State T w k -> Prop
  | .completed _ => True
  | .rejected => False
  | .active _ (.running _ _) => True
  | .active _ (.completed _) => True
  | .active _ (.rejected _) => False

/-- Structural remaining fuel of a list state.  The active cursor owns its
current phase fuel, one endpoint boundary, and the exact advertised fuel of
all visits strictly after that cursor. -/
def finiteCachedBlockVisitListRemainingFuel
    {State : Type} {T w : Nat}
    (visits : List (FixedAlphaBlockVisit State T)) :
    FiniteCachedBlockVisitListStreamingState State T w visits.length -> Nat
  | .completed _ => 0
  | .rejected => 0
  | .active cursor phase =>
      finiteCachedVisitPhaseFuel phase + 1 +
        finiteCachedBlockVisitListFuel
          (visits.drop (cursor.val + 1))

/-- The suffix after an existing successor cursor starts with exactly that
successor visit. -/
theorem finiteCachedBlockVisitListFuel_drop_succ
    {State : Type} {T : Nat}
    (visits : List (FixedAlphaBlockVisit State T))
    (cursor : Fin visits.length)
    (hnext : cursor.val + 1 < visits.length) :
    finiteCachedBlockVisitListFuel (visits.drop (cursor.val + 1)) =
      (visits.get ⟨cursor.val + 1, hnext⟩).steps + 1 +
        finiteCachedBlockVisitListFuel
          (visits.drop (cursor.val + 2)) := by
  rw [List.drop_eq_getElem_cons hnext]
  simp [finiteCachedBlockVisitListFuel,
    fixedAlphaBlockVisitsTotalSteps, Nat.add_assoc]
  omega

/-- The initialized list state carries exactly the advertised list fuel. -/
theorem finiteCachedBlockVisitListRemainingFuel_start
    (machine : DeterministicMachine)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits) :
    finiteCachedBlockVisitListRemainingFuel visits
        (finiteCachedBlockVisitListStart machine alpha block initialSlab
          visits hentries) =
      finiteCachedBlockVisitListFuel visits := by
  cases visits with
  | nil =>
      simp [finiteCachedBlockVisitListStart,
        finiteCachedBlockVisitListRemainingFuel,
        finiteCachedBlockVisitListFuel,
        fixedAlphaBlockVisitsTotalSteps]
  | cons first rest =>
      simp [finiteCachedBlockVisitListStart,
        finiteCachedBlockVisitListActiveState,
        finiteCachedBlockVisitListRemainingFuel,
        finiteCachedVisitPhaseFuel, fixedAlphaVisitRemaining,
        finiteCachedBlockVisitListFuel,
        fixedAlphaBlockVisitsTotalSteps]
      omega

/-- The resolved local phase update cannot spend more than one unit of its
advertised remaining counter unless it rejects. -/
theorem finiteCachedVisitPhaseFuel_le_succ_of_advance_potentiallyCompletable
    (machine : DeterministicMachine)
    (T w base : Nat) (hbound : base + w <= T + 1)
    (remaining : Fin (T + 1))
    (live : LocalReplayState (cachedInputMachine machine).State T w)
    (unread : ReadOnlySymbol)
    (hnext : match advanceFiniteCachedVisitPhase machine T w base hbound
        remaining live unread with
      | .running _ _ => True
      | .completed _ => True
      | .rejected _ => False) :
    remaining.val <=
      finiteCachedVisitPhaseFuel
        (advanceFiniteCachedVisitPhase machine T w base hbound
          remaining live unread) + 1 := by
  unfold advanceFiniteCachedVisitPhase at hnext ⊢
  split
  · simp_all
  · split
    · split <;> simp_all [finiteCachedVisitPhaseFuel]
    · split <;> simp_all [finiteCachedVisitPhaseFuel, spendVisitStep] <;>
        omega
/-- A local phase transition which remains potentially completable loses at
most one unit of phase fuel. -/
theorem finiteCachedVisitPhaseFuel_le_succ_of_step_potentiallyCompletable
    (machine : DeterministicMachine)
    (n T w base : Nat) (hbound : base + w <= T + 1)
    (phase : FiniteCachedVisitStreamingState
      (cachedInputMachine machine).State T w)
    (supplied : Option ReadOnlySymbol)
    (hnext : match finiteCachedVisitStreamingStep machine n T w base hbound
        phase supplied with
      | .running _ _ => True
      | .completed _ => True
      | .rejected _ => False) :
    finiteCachedVisitPhaseFuel phase <=
      finiteCachedVisitPhaseFuel
        (finiteCachedVisitStreamingStep machine n T w base hbound
          phase supplied) + 1 := by
  cases phase with
  | completed final =>
      simp [finiteCachedVisitStreamingStep, finiteCachedVisitPhaseFuel]
  | rejected reason =>
      simp [finiteCachedVisitStreamingStep, finiteCachedVisitPhaseFuel]
  | running remaining live =>
      by_cases hneeds : cachedLocalStepNeedsUnread machine live = true
      ·
        by_cases hin : live.inputHead.val < n
        ·
          cases supplied with
          | none =>
              exfalso
              simp [finiteCachedVisitStreamingStep, hneeds, hin] at hnext
          | some unread =>
              have hnext' : match advanceFiniteCachedVisitPhase machine T w
                  base hbound remaining live unread with
                | .running _ _ => True
                | .completed _ => True
                | .rejected _ => False := by
                simpa [finiteCachedVisitStreamingStep, hneeds, hin] using hnext
              simpa [finiteCachedVisitStreamingStep, hneeds, hin,
                finiteCachedVisitPhaseFuel] using
                finiteCachedVisitPhaseFuel_le_succ_of_advance_potentiallyCompletable
                  machine T w base hbound remaining live unread hnext'
        ·
          cases supplied with
          | none =>
              have hnext' : match advanceFiniteCachedVisitPhase machine T w
                  base hbound remaining live .rightEnd with
                | .running _ _ => True
                | .completed _ => True
                | .rejected _ => False := by
                simpa [finiteCachedVisitStreamingStep, hneeds, hin] using hnext
              simpa [finiteCachedVisitStreamingStep, hneeds, hin,
                finiteCachedVisitPhaseFuel] using
                finiteCachedVisitPhaseFuel_le_succ_of_advance_potentiallyCompletable
                  machine T w base hbound remaining live .rightEnd hnext'
          | some unread =>
              exfalso
              simp [finiteCachedVisitStreamingStep, hneeds, hin] at hnext
      ·
        cases supplied with
        | none =>
            have hnext' : match advanceFiniteCachedVisitPhase machine T w
                base hbound remaining live .rightEnd with
              | .running _ _ => True
              | .completed _ => True
              | .rejected _ => False := by
              simpa [finiteCachedVisitStreamingStep, hneeds] using hnext
            simpa [finiteCachedVisitStreamingStep, hneeds,
              finiteCachedVisitPhaseFuel] using
              finiteCachedVisitPhaseFuel_le_succ_of_advance_potentiallyCompletable
                machine T w base hbound remaining live .rightEnd hnext'
        | some unread =>
            exfalso
            simp [finiteCachedVisitStreamingStep, hneeds] at hnext

/-- Initializing an arbitrary cursor from its carried slab exposes exactly
the advertised fuel of the suffix beginning at that cursor. -/
theorem finiteCachedBlockVisitListRemainingFuel_activeState
    (machine : DeterministicMachine)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (cursor : Fin visits.length)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block)) :
    finiteCachedBlockVisitListRemainingFuel visits
        (finiteCachedBlockVisitListActiveState machine alpha block visits
          hentries cursor carried) =
      finiteCachedBlockVisitListFuel (visits.drop cursor.val) := by
  rw [List.drop_eq_getElem_cons cursor.isLt]
  simp [finiteCachedBlockVisitListActiveState,
    finiteCachedBlockVisitListRemainingFuel, finiteCachedVisitPhaseFuel,
    fixedAlphaVisitRemaining, finiteCachedBlockVisitListFuel,
    fixedAlphaBlockVisitsTotalSteps, Nat.add_assoc]
  omega

/-- One list-verifier transition whose result is still potentially
completable loses at most one unit of structural remaining fuel. -/
theorem finiteCachedBlockVisitListRemainingFuel_le_succ_step
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
    (supplied : Option ReadOnlySymbol)
    (hnext : FiniteCachedBlockVisitListPotentiallyCompletable
      (finiteCachedBlockVisitListStreamingStep machine n alpha block visits
        hentries state supplied)) :
    finiteCachedBlockVisitListRemainingFuel visits state <=
      finiteCachedBlockVisitListRemainingFuel visits
        (finiteCachedBlockVisitListStreamingStep machine n alpha block visits
          hentries state supplied) + 1 := by
  cases state with
  | completed slab =>
      simp [finiteCachedBlockVisitListStreamingStep,
        finiteCachedBlockVisitListRemainingFuel]
  | rejected =>
      simp [finiteCachedBlockVisitListStreamingStep,
        FiniteCachedBlockVisitListPotentiallyCompletable] at hnext
  | active cursor phase =>
      cases phase with
      | rejected reason =>
          simp [finiteCachedBlockVisitListStreamingStep,
            FiniteCachedBlockVisitListPotentiallyCompletable] at hnext
      | running remaining live =>
          cases hphase : finiteCachedVisitStreamingStep machine n T
              (advertisedBlockWidth alpha.offsets block)
              (advertisedBlockLower alpha.offsets block)
              (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
              (.running remaining live) supplied with
          | rejected failure =>
              have hstep : finiteCachedBlockVisitListStreamingStep machine n
                  alpha block visits hentries
                  (.active cursor (.running remaining live)) supplied =
                    .rejected := by
                rw [finiteCachedBlockVisitListStreamingStep_active_running]
                simp [hphase, liftFiniteCachedBlockVisitPhase]
              rw [hstep] at hnext
              exact hnext.elim
          | completed final =>
              have hphaseLe :=
                finiteCachedVisitPhaseFuel_le_succ_of_step_potentiallyCompletable
                  machine n T (advertisedBlockWidth alpha.offsets block)
                  (advertisedBlockLower alpha.offsets block)
                  (advertisedBlockLower_add_width_le_horizon
                    alpha.offsets block)
                  (.running remaining live) supplied (by simp [hphase])
              have hstep : finiteCachedBlockVisitListStreamingStep machine n
                  alpha block visits hentries
                  (.active cursor (.running remaining live)) supplied =
                    .active cursor (.completed final) := by
                rw [finiteCachedBlockVisitListStreamingStep_active_running]
                simp [hphase, liftFiniteCachedBlockVisitPhase]
              rw [hstep]
              simp [finiteCachedBlockVisitListRemainingFuel,
                finiteCachedVisitPhaseFuel, hphase] at hphaseLe ⊢
              omega
          | running nextRemaining nextLive =>
              have hstep : finiteCachedBlockVisitListStreamingStep machine n
                  alpha block visits hentries
                  (.active cursor (.running remaining live)) supplied =
                    .active cursor (.running nextRemaining nextLive) := by
                rw [finiteCachedBlockVisitListStreamingStep_active_running]
                simp [hphase, liftFiniteCachedBlockVisitPhase]
              rw [hstep] at hnext
              have hphaseLe :=
                finiteCachedVisitPhaseFuel_le_succ_of_step_potentiallyCompletable
                  machine n T (advertisedBlockWidth alpha.offsets block)
                  (advertisedBlockLower alpha.offsets block)
                  (advertisedBlockLower_add_width_le_horizon
                    alpha.offsets block)
                  (.running remaining live) supplied (by simp [hphase])
              rw [hstep]
              simp [finiteCachedBlockVisitListRemainingFuel,
                finiteCachedVisitPhaseFuel, hphase] at hphaseLe ⊢
              omega
      | completed final =>
          by_cases haccept : @finiteCachedVisitPhaseAccept
              (cachedInputMachine machine).State
              (cachedInputStateDecidableEq machine) T
              (advertisedBlockWidth alpha.offsets block)
              (visits.get cursor).exit (.completed final) = true
          · cases supplied with
            | some symbol =>
                have hstep :=
                  finiteCachedBlockVisitListStreamingStep_completed_some
                    machine n alpha block visits hentries cursor final symbol
                rw [hstep] at hnext
                exact hnext.elim
            | none =>
                by_cases hcursor : cursor.val + 1 < visits.length
                · let next : Fin visits.length :=
                    ⟨cursor.val + 1, hcursor⟩
                  have hstep :=
                    finiteCachedBlockVisitListStreamingStep_completed_next
                      machine n alpha block visits hentries cursor final
                        haccept hcursor
                  have hactive :=
                    finiteCachedBlockVisitListRemainingFuel_activeState
                      machine alpha block visits hentries next final.workSlab
                  rw [hstep]
                  rw [hactive]
                  simp [finiteCachedBlockVisitListRemainingFuel,
                    finiteCachedVisitPhaseFuel, next]
                  omega
                · have hdrop : visits.drop (cursor.val + 1) = [] :=
                    List.drop_eq_nil_of_le (Nat.le_of_not_gt hcursor)
                  have hstep :=
                    finiteCachedBlockVisitListStreamingStep_completed_last
                      machine n alpha block visits hentries cursor final
                        haccept hcursor
                  rw [hstep]
                  simp [finiteCachedBlockVisitListRemainingFuel,
                    finiteCachedVisitPhaseFuel, hdrop,
                    finiteCachedBlockVisitListFuel,
                    fixedAlphaBlockVisitsTotalSteps]
          · have hstep : finiteCachedBlockVisitListStreamingStep machine n
                alpha block visits hentries
                (.active cursor (.completed final)) supplied = .rejected := by
              simp only [finiteCachedBlockVisitListStreamingStep]
              rw [if_neg haccept]
            rw [hstep] at hnext
            exact hnext.elim

/-- Any state whose canonical input-driven continuation reaches global
completion satisfies the structural potentially-completable predicate. -/
theorem finiteCachedBlockVisitListPotentiallyCompletable_of_completed
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
    (state : FiniteCachedBlockVisitListStreamingState
      (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block) visits.length)
    (fuel : Nat)
    (finalSlab : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (hcomplete :
      let verifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
        machine input.length alpha block initialSlab visits hentries
      verifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length)
        (fun index => input.get index) fuel state = .completed finalSlab) :
    FiniteCachedBlockVisitListPotentiallyCompletable state := by
  let verifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
    machine input.length alpha block initialSlab visits hentries
  let selector : verifier.State -> Option (Fin input.length) :=
    finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length
  let inputBits : Fin input.length -> Bool := fun index => input.get index
  change verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
      fuel state = .completed finalSlab at hcomplete
  cases state with
  | completed slab =>
      trivial
  | rejected =>
      have hself := verifier.inputDrivenCore_eq_self_of_halted
        (fun bit => .bit bit) selector inputBits fuel (.rejected) (by rfl)
      rw [hself] at hcomplete
      contradiction
  | active cursor phase =>
      cases phase with
      | running remaining live =>
          trivial
      | completed final =>
          trivial
      | rejected reason =>
          cases fuel with
          | zero =>
              simp [FiniteStreamingVerifier.inputDrivenCore] at hcomplete
          | succ fuel =>
              have hone : verifier.inputDrivenCore (fun bit => .bit bit)
                  selector inputBits 1 (.active cursor (.rejected reason)) =
                    .rejected := by
                simp [FiniteStreamingVerifier.inputDrivenCore, verifier,
                  finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
                  finiteCachedBlockVisitListHalted,
                  finiteCachedBlockVisitListRequestsInput,
                  finiteCachedVisitPhaseRequestsInput,
                  finiteCachedBlockVisitListStreamingStep]
              rw [verifier.inputDrivenCore_succ_front (fun bit => .bit bit)
                selector inputBits fuel (.active cursor (.rejected reason))]
                at hcomplete
              rw [hone] at hcomplete
              have hself := verifier.inputDrivenCore_eq_self_of_halted
                (fun bit => .bit bit) selector inputBits fuel (.rejected)
                (by rfl)
              rw [hself] at hcomplete
              contradiction

/-- Reaching global completion needs at least the structural remaining fuel
of the starting list state. -/
theorem finiteCachedBlockVisitListRemainingFuel_le_of_completed
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
    (state : FiniteCachedBlockVisitListStreamingState
      (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block) visits.length)
    (fuel : Nat)
    (finalSlab : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (hcomplete :
      let verifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
        machine input.length alpha block initialSlab visits hentries
      verifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length)
        (fun index => input.get index) fuel state = .completed finalSlab) :
    finiteCachedBlockVisitListRemainingFuel visits state <= fuel := by
  let verifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
    machine input.length alpha block initialSlab visits hentries
  let selector : verifier.State -> Option (Fin input.length) :=
    finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length
  let inputBits : Fin input.length -> Bool := fun index => input.get index
  change verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
      fuel state = .completed finalSlab at hcomplete
  induction fuel generalizing state with
  | zero =>
      cases state <;>
        simp [FiniteStreamingVerifier.inputDrivenCore,
          finiteCachedBlockVisitListRemainingFuel] at hcomplete ⊢
  | succ fuel ih =>
      cases state with
      | completed slab =>
          simp [finiteCachedBlockVisitListRemainingFuel]
      | rejected =>
          have hself := verifier.inputDrivenCore_eq_self_of_halted
            (fun bit => .bit bit) selector inputBits (fuel + 1) (.rejected)
              (by rfl)
          rw [hself] at hcomplete
          contradiction
      | active cursor phase =>
          let supplied : Option ReadOnlySymbol :=
            if verifier.requestsInput (.active cursor phase) then
              (selector (.active cursor phase)).map
                (fun index => .bit (inputBits index))
            else none
          let next := finiteCachedBlockVisitListStreamingStep machine
            input.length alpha block visits hentries
            (.active cursor phase) supplied
          have hfront : verifier.inputDrivenCore (fun bit => .bit bit)
              selector inputBits (fuel + 1) (.active cursor phase) =
                verifier.inputDrivenCore (fun bit => .bit bit) selector
                  inputBits fuel next := by
            simp [FiniteStreamingVerifier.inputDrivenCore, verifier,
              finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
              finiteCachedBlockVisitListHalted, supplied, next]
          rw [hfront] at hcomplete
          have hpotential :=
            finiteCachedBlockVisitListPotentiallyCompletable_of_completed
              machine input alpha block initialSlab visits hentries next fuel
                finalSlab (by
                  simpa [verifier, selector, inputBits] using hcomplete)
          have hstep := finiteCachedBlockVisitListRemainingFuel_le_succ_step
            machine input.length alpha block visits hentries
              (.active cursor phase) supplied hpotential
          have hstep' : finiteCachedBlockVisitListRemainingFuel visits
                (.active cursor phase) <=
              finiteCachedBlockVisitListRemainingFuel visits next + 1 := by
            simpa [next] using hstep
          have htail := ih next hcomplete
          omega

/-- Exact strict-prefix invariant used by outer sequential composition. -/
def FiniteCachedBlockVisitListLiveBefore
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
    (input : Fin n -> Bool) (fuel : Nat) : Prop :=
  let verifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
    machine n alpha block initialSlab visits hentries
  ∀ spent : Nat, spent < fuel ->
    verifier.halted
      (verifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedBlockVisitListAdaptiveQueryIndex? machine n)
        input spent verifier.start) = false

/-- A recursive finite streaming certificate forces strict-prefix liveness up
to the exact transition-plus-boundary list fuel. -/
theorem finiteCachedBlockVisitList_liveBefore_of_certificate
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
    FiniteCachedBlockVisitListLiveBefore machine alpha block initialSlab
      visits hentries (fun index => input.get index)
      (finiteCachedBlockVisitListFuel visits) := by
  let verifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
    machine input.length alpha block initialSlab visits hentries
  let selector : verifier.State -> Option (Fin input.length) :=
    finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length
  let inputBits : Fin input.length -> Bool := fun index => input.get index
  obtain ⟨finalSlab, hfull⟩ :=
    finiteCachedBlockVisitList_inputDrivenCore_completed_of_certificate
      machine input alpha block initialSlab visits hentries hcertificate
  change verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
      (finiteCachedBlockVisitListFuel visits) verifier.start =
        .completed finalSlab at hfull
  change ∀ spent : Nat, spent < finiteCachedBlockVisitListFuel visits ->
    verifier.halted
      (verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
        spent verifier.start) = false
  intro spent hspent
  let prefixState := verifier.inputDrivenCore (fun bit => .bit bit)
    selector inputBits spent verifier.start
  cases hhalt : verifier.halted prefixState with
  | false => rfl
  | true =>
      have hsplit : finiteCachedBlockVisitListFuel visits =
          spent + (finiteCachedBlockVisitListFuel visits - spent) := by
        omega
      have hdecomp : verifier.inputDrivenCore (fun bit => .bit bit)
          selector inputBits (finiteCachedBlockVisitListFuel visits)
          verifier.start =
        verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
          (finiteCachedBlockVisitListFuel visits - spent) prefixState := by
        calc
          verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
              (finiteCachedBlockVisitListFuel visits) verifier.start =
            verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
              (spent + (finiteCachedBlockVisitListFuel visits - spent))
              verifier.start :=
            congrArg (fun fuel => verifier.inputDrivenCore
              (fun bit => .bit bit) selector inputBits fuel verifier.start)
              hsplit
          _ = verifier.inputDrivenCore (fun bit => .bit bit) selector
              inputBits (finiteCachedBlockVisitListFuel visits - spent)
              (verifier.inputDrivenCore (fun bit => .bit bit) selector
                inputBits spent verifier.start) :=
            verifier.inputDrivenCore_add (fun bit => .bit bit) selector
              inputBits spent (finiteCachedBlockVisitListFuel visits - spent)
                verifier.start
          _ = verifier.inputDrivenCore (fun bit => .bit bit) selector
              inputBits (finiteCachedBlockVisitListFuel visits - spent)
              prefixState := rfl
      have hself := verifier.inputDrivenCore_eq_self_of_halted
        (fun bit => .bit bit) selector inputBits
        (finiteCachedBlockVisitListFuel visits - spent) prefixState hhalt
      have hprefixState : prefixState = .completed finalSlab := by
        rw [hdecomp, hself] at hfull
        exact hfull
      have hprefixComplete : verifier.inputDrivenCore
          (fun bit => .bit bit) selector inputBits spent verifier.start =
            .completed finalSlab := by
        simpa [prefixState] using hprefixState
      have hminimum :=
        finiteCachedBlockVisitListRemainingFuel_le_of_completed
          machine input alpha block initialSlab visits hentries
            verifier.start spent finalSlab (by
              simpa [verifier, selector, inputBits] using hprefixComplete)
      have hstart := finiteCachedBlockVisitListRemainingFuel_start
        machine alpha block initialSlab visits hentries
      have hstart' : finiteCachedBlockVisitListRemainingFuel visits
          verifier.start = finiteCachedBlockVisitListFuel visits := by
        simpa [verifier,
          finiteCachedFixedAlphaBlockVisitListStreamingVerifier] using hstart
      omega

/-- Semantic replay acceptance supplies the certificate and therefore the
strict-prefix liveness invariant without any extra hypothesis. -/
theorem finiteCachedBlockVisitList_liveBefore_of_replayAccepted
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
    FiniteCachedBlockVisitListLiveBefore machine alpha block initialSlab
      visits hentries (fun index => input.get index)
      (finiteCachedBlockVisitListFuel visits) := by
  apply finiteCachedBlockVisitList_liveBefore_of_certificate
  exact (finiteCachedFixedAlphaBlockVisitListStreamingCertificate_iff
    machine input alpha block initialSlab visits).2 haccepted

end OneTapeMagnification
end Frontier
end Pnp4
