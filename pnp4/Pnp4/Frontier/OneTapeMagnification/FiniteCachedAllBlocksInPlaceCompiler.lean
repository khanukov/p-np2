import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedAllBlocksInPlaceRollingFold
import Pnp4.Frontier.OneTapeMagnification.FiniteCachedAllBlocksHomogeneousEmbedding

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Finite compiler for the fused all-block in-place rolling state

The live state from `FiniteCachedAllBlocksInPlaceRollingFold` is first put in
explicit equivalence with the earlier outer-plus-fold carrier, and therefore
embeds in the homogeneous carrier already counted by the magnification
argument.  The second half of the file packages the live transition as a
total finite streaming verifier and its adaptive compilation.
-/

/-- The rolling list state and its two accumulated flags are exactly the same
data as one list phase paired with an `InPlaceTwoWindowFoldState`. -/
def finiteCachedAllBlocksInPlaceRollingStateEquivWithFold
    (machine : DeterministicMachine) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)) :
    FiniteCachedAllBlocksInPlaceRollingState machine alpha blockVisits ≃
      FiniteCachedAllBlocksWithFoldState machine alpha blockVisits where
  toFun
    | .active block state allVisits allCuts =>
        .active block state.listState
          { allBlockVisitsValid := allVisits
            allClosedCutsValid := allCuts
            counters := state.counters }
    | .completed fold => .completed fold
    | .rejected => .rejected
  invFun
    | .active block phase fold =>
        .active block ⟨phase, fold.counters⟩
          fold.allBlockVisitsValid fold.allClosedCutsValid
    | .completed fold => .completed fold
    | .rejected => .rejected
  left_inv state := by cases state <;> rfl
  right_inv state := by cases state <;> rfl

/-- Sum/sigma presentation used only to construct a controlled finite
instance for the earlier outer-plus-fold carrier. -/
def finiteCachedAllBlocksWithFoldStateEquivSigma
    (machine : DeterministicMachine) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)) :
    FiniteCachedAllBlocksWithFoldState machine alpha blockVisits ≃
      Sum
        (Sigma fun block : Fin (T / b + 1) =>
          FiniteCachedBlockVisitListStreamingState
              (cachedInputMachine machine).State T
              (advertisedBlockWidth alpha.offsets block)
              (blockVisits block).length ×
            InPlaceTwoWindowFoldState T b)
        (Sum (InPlaceTwoWindowFoldState T b) Unit) where
  toFun
    | .active block phase fold => .inl ⟨block, phase, fold⟩
    | .completed fold => .inr (.inl fold)
    | .rejected => .inr (.inr ())
  invFun
    | .inl ⟨block, phase, fold⟩ => .active block phase fold
    | .inr (.inl fold) => .completed fold
    | .inr (.inr _) => .rejected
  left_inv state := by cases state <;> rfl
  right_inv encoded := by
    rcases encoded with active | terminal
    · rcases active with ⟨block, phase, fold⟩
      rfl
    · rcases terminal with completed | rejected
      · rfl
      · cases rejected
        rfl

/-- Named finite instance for the outer-plus-fold carrier. -/
def finiteCachedAllBlocksWithFoldStateFintype
    (machine : DeterministicMachine) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)) :
    Fintype (FiniteCachedAllBlocksWithFoldState machine alpha blockVisits) := by
  letI := (cachedInputMachine machine).stateFintype
  letI := inPlaceTwoWindowFoldStateFintype T b
  exact Fintype.ofEquiv _
    (finiteCachedAllBlocksWithFoldStateEquivSigma
      machine alpha blockVisits).symm

/-- Explicit finite instance for the fused rolling state, transported through
the exact equivalence above. -/
def finiteCachedAllBlocksInPlaceRollingStateFintype
    (machine : DeterministicMachine) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)) :
    Fintype
      (FiniteCachedAllBlocksInPlaceRollingState machine alpha blockVisits) :=
  @Fintype.ofEquiv
    (FiniteCachedAllBlocksInPlaceRollingState machine alpha blockVisits)
    (FiniteCachedAllBlocksWithFoldState machine alpha blockVisits)
    (finiteCachedAllBlocksWithFoldStateFintype machine alpha blockVisits)
    (finiteCachedAllBlocksInPlaceRollingStateEquivWithFold
      machine alpha blockVisits).symm

/-- Generic embedding into the homogeneous counted carrier whenever block
width and visit-count geometry fit its uniform coordinates. -/
def finiteCachedAllBlocksInPlaceRollingEmbedding
    (machine : DeterministicMachine) {T b : Nat} (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hlength : ∀ block, (blockVisits block).length ≤ T) :
    FiniteCachedAllBlocksInPlaceRollingState machine alpha blockVisits ↪
      FixedAlphaMultiVisitValidatorState machine T b where
  toFun state := encodeFiniteCachedAllBlocksWithFoldState machine hb alpha
    blockVisits hlength
      (finiteCachedAllBlocksInPlaceRollingStateEquivWithFold
        machine alpha blockVisits state)
  inj' := by
    intro left right heq
    apply (finiteCachedAllBlocksInPlaceRollingStateEquivWithFold
      machine alpha blockVisits).injective
    exact encodeFiniteCachedAllBlocksWithFoldState_injective machine hb alpha
      blockVisits hlength heq

/-- A valid timed schedule supplies the uniform visit-count hypothesis, so
the fused state has a first-class homogeneous embedding. -/
def finiteCachedTimedAlphaScheduleInPlaceRollingEmbedding
    (machine : DeterministicMachine) {T b : Nat} (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hschedule : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha scheduled) :
    FiniteCachedAllBlocksInPlaceRollingState machine alpha
        (fun block => timedAlphaBlockVisits block scheduled) ↪
      FixedAlphaMultiVisitValidatorState machine T b :=
  finiteCachedAllBlocksInPlaceRollingEmbedding machine hb alpha
    (fun block => timedAlphaBlockVisits block scheduled)
    (timedAlphaSchedule_blockVisits_length_le_horizon machine alpha scheduled
      hschedule)

/-- Cardinal inequality for an arbitrary geometrically bounded block family. -/
theorem card_finiteCachedAllBlocksInPlaceRollingState_le
    (machine : DeterministicMachine) {T b : Nat} (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hlength : ∀ block, (blockVisits block).length ≤ T) :
    letI := finiteCachedAllBlocksInPlaceRollingStateFintype machine alpha
      blockVisits
    letI := (cachedInputMachine machine).stateFintype
    letI := inPlaceTwoWindowFoldStateFintype T b
    Fintype.card
        (FiniteCachedAllBlocksInPlaceRollingState machine alpha blockVisits) ≤
      Fintype.card (FixedAlphaMultiVisitValidatorState machine T b) := by
  letI := finiteCachedAllBlocksInPlaceRollingStateFintype machine alpha
    blockVisits
  letI := (cachedInputMachine machine).stateFintype
  letI := inPlaceTwoWindowFoldStateFintype T b
  exact Fintype.card_le_of_injective
    (finiteCachedAllBlocksInPlaceRollingEmbedding machine hb alpha blockVisits
      hlength)
    (finiteCachedAllBlocksInPlaceRollingEmbedding machine hb alpha blockVisits
      hlength).injective

/-- The explicit embedding gives the corresponding sharp carrier-cardinality
inequality. -/
theorem card_finiteCachedTimedAlphaScheduleInPlaceRollingState_le
    (machine : DeterministicMachine) {T b : Nat} (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hschedule : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha scheduled) :
    letI := finiteCachedAllBlocksInPlaceRollingStateFintype machine alpha
      (fun block => timedAlphaBlockVisits block scheduled)
    letI := (cachedInputMachine machine).stateFintype
    letI := inPlaceTwoWindowFoldStateFintype T b
    Fintype.card
        (FiniteCachedAllBlocksInPlaceRollingState machine alpha
          (fun block => timedAlphaBlockVisits block scheduled)) ≤
      Fintype.card (FixedAlphaMultiVisitValidatorState machine T b) := by
  letI := finiteCachedAllBlocksInPlaceRollingStateFintype machine alpha
    (fun block => timedAlphaBlockVisits block scheduled)
  letI := (cachedInputMachine machine).stateFintype
  letI := inPlaceTwoWindowFoldStateFintype T b
  exact Fintype.card_le_of_injective
    (finiteCachedTimedAlphaScheduleInPlaceRollingEmbedding machine hb alpha
      scheduled hschedule)
    (finiteCachedTimedAlphaScheduleInPlaceRollingEmbedding machine hb alpha
      scheduled hschedule).injective

/-- Erase counters and accumulated flags to the already verified outer list
state. -/
def eraseFiniteCachedAllBlocksInPlaceRolling
    (machine : DeterministicMachine) {T b : Nat}
    {alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b}
    {blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)} :
    FiniteCachedAllBlocksInPlaceRollingState machine alpha blockVisits →
      FiniteCachedTimedAlphaAllBlocksStreamingState machine alpha blockVisits
  | .active block state _ _ => .active block state.listState
  | .completed _ => .completed
  | .rejected => .rejected

/-- Only global completion and rejection halt the fused verifier. -/
def finiteCachedAllBlocksInPlaceRollingHalted
    (machine : DeterministicMachine) {T b : Nat}
    {alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b}
    {blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)} :
    FiniteCachedAllBlocksInPlaceRollingState machine alpha blockVisits → Bool
  | .active _ _ _ _ => false
  | .completed _ => true
  | .rejected => true

/-- Input requests are exactly those of the active dependent list phase. -/
def finiteCachedAllBlocksInPlaceRollingRequestsInput
    (machine : DeterministicMachine) (n : Nat) {T b : Nat}
    {alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b}
    {blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)} :
    FiniteCachedAllBlocksInPlaceRollingState machine alpha blockVisits → Bool
  | .active _ state _ _ =>
      finiteCachedBlockVisitListRequestsInput machine n state.listState
  | .completed _ => false
  | .rejected => false

/-- A completed fused state accepts exactly when both accumulated in-place
flags accept. -/
def finiteCachedAllBlocksInPlaceRollingAccept
    (machine : DeterministicMachine) {T b : Nat}
    {alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b}
    {blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)} :
    FiniteCachedAllBlocksInPlaceRollingState machine alpha blockVisits → Bool
  | .completed fold =>
      fold.allBlockVisitsValid && fold.allClosedCutsValid
  | _ => false

/-- State-dependent immutable-input selector of the active list phase. -/
def finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex?
    (machine : DeterministicMachine) (n : Nat) {T b : Nat}
    {alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b}
    {blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)} :
    FiniteCachedAllBlocksInPlaceRollingState machine alpha blockVisits →
      Option (Fin n)
  | .active _ state _ _ =>
      finiteCachedBlockVisitListAdaptiveQueryIndex? machine n state.listState
  | .completed _ => none
  | .rejected => none

/-- The selector is total whenever the fused verifier requests input. -/
theorem finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex?_total
    (machine : DeterministicMachine) (n : Nat) {T b : Nat}
    {alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b}
    {blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)}
    (state : FiniteCachedAllBlocksInPlaceRollingState
      machine alpha blockVisits)
    (hrequest : finiteCachedAllBlocksInPlaceRollingRequestsInput
      machine n state = true) :
    ∃ index,
      finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex?
        machine n state = some index := by
  cases state with
  | active block state allVisits allCuts =>
      exact finiteCachedBlockVisitListAdaptiveQueryIndex?_total_of_requestsInput
        machine n state.listState hrequest
  | completed fold =>
      simp [finiteCachedAllBlocksInPlaceRollingRequestsInput] at hrequest
  | rejected =>
      simp [finiteCachedAllBlocksInPlaceRollingRequestsInput] at hrequest

/-- Proof-indexed finite streaming verifier on the genuinely fused state. -/
def finiteCachedTimedAlphaAllBlocksInPlaceRollingStreamingVerifier
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits) :
    FiniteStreamingVerifier ReadOnlySymbol where
  State := FiniteCachedAllBlocksInPlaceRollingState machine alpha blockVisits
  stateFintype := finiteCachedAllBlocksInPlaceRollingStateFintype
    machine alpha blockVisits
  start := finiteCachedAllBlocksInPlaceRollingStart machine alpha blockVisits
    hentries
  halted := finiteCachedAllBlocksInPlaceRollingHalted machine
  requestsInput := finiteCachedAllBlocksInPlaceRollingRequestsInput machine n
  step := finiteCachedAllBlocksInPlaceRollingStreamingStep machine n alpha
    blockVisits hentries
  accept := finiteCachedAllBlocksInPlaceRollingAccept machine

/-- Total bad-geometry wrapper: malformed dependent entries start in and stay
in the unique fused rejection sink. -/
def finiteCachedAllBlocksInPlaceRollingTotalStart
    (machine : DeterministicMachine) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)) :
    FiniteCachedAllBlocksInPlaceRollingState machine alpha blockVisits :=
  if hcheck : fixedAlphaAllBlockVisitEntriesInsideCheck alpha blockVisits = true
  then
    finiteCachedAllBlocksInPlaceRollingStart machine alpha blockVisits
      ((fixedAlphaAllBlockVisitEntriesInsideCheck_eq_true_iff
        alpha blockVisits).mp hcheck)
  else .rejected

/-- Total fused transition with absorbing rejection on malformed geometry. -/
def finiteCachedAllBlocksInPlaceRollingTotalStreamingStep
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)) :
    FiniteCachedAllBlocksInPlaceRollingState machine alpha blockVisits →
      Option ReadOnlySymbol →
      FiniteCachedAllBlocksInPlaceRollingState machine alpha blockVisits :=
  if hcheck : fixedAlphaAllBlockVisitEntriesInsideCheck alpha blockVisits = true
  then
    finiteCachedAllBlocksInPlaceRollingStreamingStep machine n alpha blockVisits
      ((fixedAlphaAllBlockVisitEntriesInsideCheck_eq_true_iff
        alpha blockVisits).mp hcheck)
  else fun _ _ => .rejected

/-- Total fused finite streaming verifier. -/
def finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)) :
    FiniteStreamingVerifier ReadOnlySymbol where
  State := FiniteCachedAllBlocksInPlaceRollingState machine alpha blockVisits
  stateFintype := finiteCachedAllBlocksInPlaceRollingStateFintype
    machine alpha blockVisits
  start := finiteCachedAllBlocksInPlaceRollingTotalStart machine alpha
    blockVisits
  halted := finiteCachedAllBlocksInPlaceRollingHalted machine
  requestsInput := finiteCachedAllBlocksInPlaceRollingRequestsInput machine n
  step := finiteCachedAllBlocksInPlaceRollingTotalStreamingStep machine n alpha
    blockVisits
  accept := finiteCachedAllBlocksInPlaceRollingAccept machine

/-- Erasing the fused proof-indexed start recovers the established outer
start exactly. -/
@[simp]
theorem eraseFiniteCachedAllBlocksInPlaceRolling_start
    (machine : DeterministicMachine) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits) :
    eraseFiniteCachedAllBlocksInPlaceRolling machine
        (finiteCachedAllBlocksInPlaceRollingStart machine alpha blockVisits
          hentries) =
      finiteCachedAllBlocksStart machine alpha blockVisits hentries := by
  rfl

/-- Halting is preserved by erasure. -/
@[simp]
theorem finiteCachedAllBlocksInPlaceRollingHalted_erase
    (machine : DeterministicMachine) {T b : Nat}
    {alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b}
    {blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)}
    (state : FiniteCachedAllBlocksInPlaceRollingState
      machine alpha blockVisits) :
    finiteCachedAllBlocksInPlaceRollingHalted machine state =
      finiteCachedAllBlocksHalted
        (eraseFiniteCachedAllBlocksInPlaceRolling machine state) := by
  cases state <;> rfl

/-- Input requests are preserved by erasure. -/
@[simp]
theorem finiteCachedAllBlocksInPlaceRollingRequestsInput_erase
    (machine : DeterministicMachine) (n : Nat) {T b : Nat}
    {alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b}
    {blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)}
    (state : FiniteCachedAllBlocksInPlaceRollingState
      machine alpha blockVisits) :
    finiteCachedAllBlocksInPlaceRollingRequestsInput machine n state =
      finiteCachedAllBlocksRequestsInput machine n
        (eraseFiniteCachedAllBlocksInPlaceRolling machine state) := by
  cases state <;> rfl

/-- The adaptive selector is preserved by erasure. -/
@[simp]
theorem finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex?_erase
    (machine : DeterministicMachine) (n : Nat) {T b : Nat}
    {alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b}
    {blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)}
    (state : FiniteCachedAllBlocksInPlaceRollingState
      machine alpha blockVisits) :
    finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex? machine n state =
      finiteCachedAllBlocksAdaptiveQueryIndex? machine n
        (eraseFiniteCachedAllBlocksInPlaceRolling machine state) := by
  cases state <;> rfl

/-- One fused microstep erases to exactly one old outer microstep. -/
theorem eraseFiniteCachedAllBlocksInPlaceRolling_step
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (state : FiniteCachedAllBlocksInPlaceRollingState
      machine alpha blockVisits)
    (supplied : Option ReadOnlySymbol) :
    eraseFiniteCachedAllBlocksInPlaceRolling machine
        (finiteCachedAllBlocksInPlaceRollingStreamingStep machine n alpha
          blockVisits hentries state supplied) =
      finiteCachedAllBlocksStreamingStep machine n alpha blockVisits hentries
        (eraseFiniteCachedAllBlocksInPlaceRolling machine state) supplied := by
  cases state with
  | completed fold => rfl
  | rejected => rfl
  | active block rolling allVisits allCuts =>
      rcases rolling with ⟨listState, counters⟩
      cases listState with
      | rejected => rfl
      | completed slab =>
          cases supplied with
          | some symbol => rfl
          | none =>
              by_cases hnext : block.val < T / b
              · simp [finiteCachedAllBlocksInPlaceRollingStreamingStep,
                  finiteCachedAllBlocksStreamingStep,
                  eraseFiniteCachedAllBlocksInPlaceRolling, hnext]
              · simp [finiteCachedAllBlocksInPlaceRollingStreamingStep,
                  finiteCachedAllBlocksStreamingStep,
                  eraseFiniteCachedAllBlocksInPlaceRolling, hnext]
      | active cursor phase =>
          simp only [finiteCachedAllBlocksInPlaceRollingStreamingStep,
            finiteCachedAllBlocksStreamingStep,
            eraseFiniteCachedAllBlocksInPlaceRolling]
          let next := finiteCachedBlockVisitListStreamingRollingCounterStep
            machine n alpha block (blockVisits block) (hentries block)
              (advertisedBlockTwoWindowBoundaries block)
              ⟨.active cursor phase, counters⟩ supplied
          have hnext : next.listState =
              finiteCachedBlockVisitListStreamingStep machine n alpha block
                (blockVisits block) (hentries block) (.active cursor phase)
                  supplied := by
            exact finiteCachedBlockVisitListStreamingRollingCounterStep_listState
              machine n alpha block (blockVisits block) (hentries block)
                (advertisedBlockTwoWindowBoundaries block)
                ⟨.active cursor phase, counters⟩ supplied
          rw [← hnext]
          cases hstate : next.listState <;>
            have hold := hnext.symm.trans hstate <;>
            simp [hold, liftFiniteCachedAllBlocksPhase]

/-- Total starts commute with erasure, including malformed geometry. -/
@[simp]
theorem eraseFiniteCachedAllBlocksInPlaceRolling_totalStart
    (machine : DeterministicMachine) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)) :
    eraseFiniteCachedAllBlocksInPlaceRolling machine
        (finiteCachedAllBlocksInPlaceRollingTotalStart machine alpha
          blockVisits) =
      finiteCachedAllBlocksTotalStart machine alpha blockVisits := by
  by_cases hcheck : fixedAlphaAllBlockVisitEntriesInsideCheck
      alpha blockVisits = true
  · simp [finiteCachedAllBlocksInPlaceRollingTotalStart,
      finiteCachedAllBlocksTotalStart, hcheck]
  · simp [finiteCachedAllBlocksInPlaceRollingTotalStart,
      finiteCachedAllBlocksTotalStart, hcheck,
      eraseFiniteCachedAllBlocksInPlaceRolling]

/-- Total transitions commute with erasure. -/
theorem eraseFiniteCachedAllBlocksInPlaceRolling_totalStep
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (state : FiniteCachedAllBlocksInPlaceRollingState
      machine alpha blockVisits)
    (supplied : Option ReadOnlySymbol) :
    eraseFiniteCachedAllBlocksInPlaceRolling machine
        (finiteCachedAllBlocksInPlaceRollingTotalStreamingStep machine n alpha
          blockVisits state supplied) =
      finiteCachedAllBlocksTotalStreamingStep machine n alpha blockVisits
        (eraseFiniteCachedAllBlocksInPlaceRolling machine state) supplied := by
  by_cases hcheck : fixedAlphaAllBlockVisitEntriesInsideCheck
      alpha blockVisits = true
  · simp only [finiteCachedAllBlocksInPlaceRollingTotalStreamingStep,
      finiteCachedAllBlocksTotalStreamingStep, hcheck, dif_pos]
    exact eraseFiniteCachedAllBlocksInPlaceRolling_step machine n alpha
      blockVisits
        ((fixedAlphaAllBlockVisitEntriesInsideCheck_eq_true_iff
          alpha blockVisits).mp hcheck)
      state supplied
  · simp [finiteCachedAllBlocksInPlaceRollingTotalStreamingStep,
      finiteCachedAllBlocksTotalStreamingStep, hcheck,
      eraseFiniteCachedAllBlocksInPlaceRolling]

/-- Erasure commutes with the entire ordinary input-driven execution of the
total fused verifier. -/
theorem eraseFiniteCachedAllBlocksInPlaceRolling_inputDrivenCore
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (input : Fin n → Bool) (fuel : Nat)
    (state : FiniteCachedAllBlocksInPlaceRollingState
      machine alpha blockVisits) :
    let fused :=
      finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier
        machine n alpha blockVisits
    let outer := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
      machine n alpha blockVisits
    eraseFiniteCachedAllBlocksInPlaceRolling machine
        (fused.inputDrivenCore (fun bit => .bit bit)
          (finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex? machine n)
          input fuel state) =
      outer.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedAllBlocksAdaptiveQueryIndex? machine n) input fuel
          (eraseFiniteCachedAllBlocksInPlaceRolling machine state) := by
  dsimp only
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simp only [FiniteStreamingVerifier.inputDrivenCore]
      change eraseFiniteCachedAllBlocksInPlaceRolling machine
          (if finiteCachedAllBlocksInPlaceRollingHalted machine state then
            state
          else
            (finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier
              machine n alpha blockVisits).inputDrivenCore
                (fun bit => .bit bit)
                (finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex?
                  machine n)
                input fuel
                (finiteCachedAllBlocksInPlaceRollingTotalStreamingStep machine
                  n alpha blockVisits state
                  (if finiteCachedAllBlocksInPlaceRollingRequestsInput
                      machine n state then
                    (finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex?
                      machine n state).map
                        (fun index => ReadOnlySymbol.bit (input index))
                  else none))) =
        (if finiteCachedAllBlocksHalted
              (eraseFiniteCachedAllBlocksInPlaceRolling machine state) then
          eraseFiniteCachedAllBlocksInPlaceRolling machine state
        else
          (finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier machine n
            alpha blockVisits).inputDrivenCore (fun bit => .bit bit)
              (finiteCachedAllBlocksAdaptiveQueryIndex? machine n) input fuel
              (finiteCachedAllBlocksTotalStreamingStep machine n alpha
                blockVisits
                (eraseFiniteCachedAllBlocksInPlaceRolling machine state)
                (if finiteCachedAllBlocksRequestsInput machine n
                    (eraseFiniteCachedAllBlocksInPlaceRolling machine state)
                  then
                    (finiteCachedAllBlocksAdaptiveQueryIndex? machine n
                      (eraseFiniteCachedAllBlocksInPlaceRolling machine state)).map
                        (fun index => ReadOnlySymbol.bit (input index))
                  else none)))
      rw [finiteCachedAllBlocksInPlaceRollingHalted_erase]
      by_cases hhalt : finiteCachedAllBlocksHalted
          (eraseFiniteCachedAllBlocksInPlaceRolling machine state) = true
      · simp [hhalt]
      · simp only [hhalt, Bool.false_eq_true, ↓reduceIte]
        rw [finiteCachedAllBlocksInPlaceRollingRequestsInput_erase,
          finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex?_erase]
        rw [ih]
        rw [eraseFiniteCachedAllBlocksInPlaceRolling_totalStep]

/-- Adaptive compilation of the total fused verifier. -/
def compileAdaptiveFiniteCachedTimedAlphaAllBlocksInPlaceRollingTotal
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)) :
    LayeredQueryProgram n (finiteCachedAllBlocksFuel blockVisits) :=
  let verifier :=
    finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier
      machine n alpha blockVisits
  verifier.compileAdaptive (finiteCachedAllBlocksFuel blockVisits) n
    (fun bit => .bit bit) .rightEnd
    (finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex? machine n)

/-- Exact generic-compiler width equation for the total fused program. -/
@[simp]
theorem compileAdaptiveFiniteCachedTimedAlphaAllBlocksInPlaceRollingTotal_width
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)) :
    (compileAdaptiveFiniteCachedTimedAlphaAllBlocksInPlaceRollingTotal
      (n := n) machine alpha blockVisits).width =
      @Fintype.card
          (FiniteCachedAllBlocksInPlaceRollingState machine alpha blockVisits)
          (finiteCachedAllBlocksInPlaceRollingStateFintype
            machine alpha blockVisits) *
        (finiteCachedAllBlocksFuel blockVisits + 1) := by
  exact FiniteStreamingVerifier.compileAdaptive_width
    (finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier
      machine n alpha blockVisits)
    (finiteCachedAllBlocksFuel blockVisits) n
    (fun bit => .bit bit) .rightEnd
    (finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex? machine n)

/-- Bit budget for the compiled fused program: the existing homogeneous state
budget plus the ceiling-logarithmic generic fuel coordinate. -/
def finiteCachedAllBlocksInPlaceRollingCompiledBitBudget
    (machine : DeterministicMachine) {T b : Nat}
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)) : Nat :=
  fixedAlphaMultiVisitValidatorBitBudget machine T b +
    Nat.clog 2 (finiteCachedAllBlocksFuel blockVisits + 1)

/-- Quantitative public width bound obtained by composing the fused-state
embedding, the counted homogeneous carrier bound, and the generic compiler's
fuel coordinate. -/
theorem compileAdaptiveFiniteCachedTimedAlphaAllBlocksInPlaceRollingTotal_width_le_two_pow
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat} (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hlength : ∀ block, (blockVisits block).length ≤ T) :
    (compileAdaptiveFiniteCachedTimedAlphaAllBlocksInPlaceRollingTotal
      (n := n) machine alpha blockVisits).width ≤
      2 ^ finiteCachedAllBlocksInPlaceRollingCompiledBitBudget
        machine blockVisits := by
  rw [compileAdaptiveFiniteCachedTimedAlphaAllBlocksInPlaceRollingTotal_width]
  apply mul_le_two_pow_add
  · exact le_trans
      (card_finiteCachedAllBlocksInPlaceRollingState_le machine hb alpha
        blockVisits hlength)
      (card_fixedAlphaMultiVisitValidatorState_le_two_pow machine T b)
  · exact le_two_pow_clog_two
      (finiteCachedAllBlocksFuel blockVisits + 1)

/-- Valid timed schedules discharge the visit-count side condition in the
quantitative compiled-width bound. -/
theorem compileAdaptiveFiniteCachedTimedAlphaScheduleInPlaceRollingTotal_width_le_two_pow
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat} (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hschedule : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha scheduled) :
    (compileAdaptiveFiniteCachedTimedAlphaAllBlocksInPlaceRollingTotal
      (n := n) machine alpha
        (fun block => timedAlphaBlockVisits block scheduled)).width ≤
      2 ^ finiteCachedAllBlocksInPlaceRollingCompiledBitBudget machine
        (fun block => timedAlphaBlockVisits block scheduled) := by
  exact
    compileAdaptiveFiniteCachedTimedAlphaAllBlocksInPlaceRollingTotal_width_le_two_pow
      machine hb alpha (fun block => timedAlphaBlockVisits block scheduled)
        (timedAlphaSchedule_blockVisits_length_le_horizon machine alpha
          scheduled hschedule)

/-- Simultaneous accepted blank-slab certificates force the canonical fused
execution to reach a genuine completed state carrying some in-place fold.
This conclusion is obtained by erasure to the already proved outer execution;
it does not assume the desired identity of the carried fold. -/
theorem finiteCachedAllBlocksInPlaceRolling_inputDrivenCore_exists_completed_of_acceptedFromBlank
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (haccepted : ∀ block : Fin (T / b + 1),
      FixedAlphaBlockVisitListAcceptedFromBlank
        (cachedInputMachine machine) input alpha block
          (blockVisits block)) :
    let verifier :=
      finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier
        machine input.length alpha blockVisits
    ∃ fold : InPlaceTwoWindowFoldState T b,
      verifier.inputDrivenCore (fun bit => .bit bit)
          (finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex?
            machine input.length)
          (fun index => input.get index)
          (finiteCachedAllBlocksFuel blockVisits) verifier.start =
        .completed fold := by
  let fused :=
    finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier
      machine input.length alpha blockVisits
  let outer := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
    machine input.length alpha blockVisits
  let selector : fused.State → Option (Fin input.length) :=
    finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex?
      machine input.length
  let outerSelector : outer.State → Option (Fin input.length) :=
    finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length
  let inputBits : Fin input.length → Bool := fun index => input.get index
  let fuel := finiteCachedAllBlocksFuel blockVisits
  have houter :=
    finiteCachedAllBlocks_inputDrivenCore_completed_of_acceptedFromBlank
      machine input alpha blockVisits haccepted
  change outer.inputDrivenCore (fun bit => .bit bit) outerSelector inputBits
      fuel outer.start = .completed at houter
  have herase :=
    eraseFiniteCachedAllBlocksInPlaceRolling_inputDrivenCore
      machine alpha blockVisits inputBits fuel fused.start
  change eraseFiniteCachedAllBlocksInPlaceRolling machine
      (fused.inputDrivenCore (fun bit => .bit bit) selector inputBits fuel
        fused.start) =
      outer.inputDrivenCore (fun bit => .bit bit) outerSelector inputBits fuel
        (eraseFiniteCachedAllBlocksInPlaceRolling machine fused.start) at herase
  have hstart : eraseFiniteCachedAllBlocksInPlaceRolling machine fused.start =
      outer.start := by
    change eraseFiniteCachedAllBlocksInPlaceRolling machine
        (finiteCachedAllBlocksInPlaceRollingTotalStart machine alpha
          blockVisits) =
      finiteCachedAllBlocksTotalStart machine alpha blockVisits
    exact eraseFiniteCachedAllBlocksInPlaceRolling_totalStart machine alpha
      blockVisits
  rw [hstart, houter] at herase
  generalize hresult : fused.inputDrivenCore (fun bit => .bit bit) selector
    inputBits fuel fused.start = result at herase
  cases result with
  | active block state allVisits allCuts =>
      simp [eraseFiniteCachedAllBlocksInPlaceRolling] at herase
  | rejected =>
      simp [eraseFiniteCachedAllBlocksInPlaceRolling] at herase
  | completed fold =>
      exact ⟨fold, by simpa [fused, selector, inputBits, fuel] using hresult⟩

/-- Exact generic operational equation for the compiled fused program. -/
theorem compileAdaptiveFiniteCachedTimedAlphaAllBlocksInPlaceRollingTotal_eval
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (input : Fin n → Bool) :
    let verifier :=
      finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier
        machine n alpha blockVisits
    (compileAdaptiveFiniteCachedTimedAlphaAllBlocksInPlaceRollingTotal machine
      alpha blockVisits).eval input =
      verifier.accept
        (verifier.finishWithEndSymbol .rightEnd
          (verifier.runAdaptive (finiteCachedAllBlocksFuel blockVisits)
            (fun bit => .bit bit)
            (finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex?
              machine n)
            input)) := by
  dsimp only
  exact FiniteStreamingVerifier.compileAdaptive_eval
    (finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier
      machine n alpha blockVisits)
    (finiteCachedAllBlocksFuel blockVisits) n
    (fun bit => .bit bit) .rightEnd
    (finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex? machine n) input

/-- Accepted canonical input produces a completed fused fold, and the compiled
program evaluates exactly to the two flags stored in that reached fold. -/
theorem compileAdaptiveFiniteCachedTimedAlphaAllBlocksInPlaceRollingTotal_eval_of_acceptedFromBlank
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : ∀ _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (haccepted : ∀ block : Fin (T / b + 1),
      FixedAlphaBlockVisitListAcceptedFromBlank
        (cachedInputMachine machine) input alpha block
          (blockVisits block)) :
    let verifier :=
      finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier
        machine input.length alpha blockVisits
    ∃ fold : InPlaceTwoWindowFoldState T b,
      verifier.inputDrivenCore (fun bit => .bit bit)
          (finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex?
            machine input.length)
          (fun index => input.get index)
          (finiteCachedAllBlocksFuel blockVisits) verifier.start =
          .completed fold ∧
        (compileAdaptiveFiniteCachedTimedAlphaAllBlocksInPlaceRollingTotal
          (n := input.length) machine alpha blockVisits).eval
            (fun index => input.get index) =
          (fold.allBlockVisitsValid && fold.allClosedCutsValid) := by
  let verifier :=
    finiteCachedTimedAlphaAllBlocksInPlaceRollingTotalStreamingVerifier
      machine input.length alpha blockVisits
  let selector : verifier.State → Option (Fin input.length) :=
    finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex?
      machine input.length
  let inputBits : Fin input.length → Bool := fun index => input.get index
  let fuel := finiteCachedAllBlocksFuel blockVisits
  obtain ⟨fold, hcore⟩ :=
    finiteCachedAllBlocksInPlaceRolling_inputDrivenCore_exists_completed_of_acceptedFromBlank
      machine input alpha blockVisits haccepted
  change verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
      fuel verifier.start = .completed fold at hcore
  refine ⟨fold, hcore, ?_⟩
  have htotal : ∀ state, verifier.requestsInput state = true →
      ∃ index, selector state = some index := by
    intro state hrequest
    exact finiteCachedAllBlocksInPlaceRollingAdaptiveQueryIndex?_total
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
  have hrun :
      (verifier.runAdaptive fuel (fun bit => .bit bit) selector inputBits).1 =
        .completed fold := hrunPhase.trans hcore
  have hhalted : verifier.halted
      (verifier.runAdaptive fuel (fun bit => .bit bit) selector inputBits).1 =
        true := by
    rw [hrun]
    rfl
  have hfinish : verifier.finishWithEndSymbol .rightEnd
      (verifier.runAdaptive fuel (fun bit => .bit bit) selector inputBits) =
        .completed fold := by
    calc
      verifier.finishWithEndSymbol .rightEnd
          (verifier.runAdaptive fuel (fun bit => .bit bit) selector inputBits) =
        (verifier.runAdaptive fuel
          (fun bit => .bit bit) selector inputBits).1 :=
        verifier.finishWithEndSymbol_eq_of_halted .rightEnd _ hhalted
      _ = .completed fold := hrun
  change (verifier.compileAdaptive fuel input.length (fun bit => .bit bit)
      .rightEnd selector).eval inputBits = _
  rw [FiniteStreamingVerifier.compileAdaptive_eval, hfinish]
  rfl

end OneTapeMagnification
end Frontier
end Pnp4
