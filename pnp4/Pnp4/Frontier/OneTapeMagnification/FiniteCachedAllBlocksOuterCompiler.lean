import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.TimedAlphaBlockVisitInputOrder
import Pnp4.Frontier.OneTapeMagnification.ExecutableInPlaceTimedAlphaComponent
import Pnp4.Frontier.OneTapeMagnification.AdaptiveCachedBlockVisitListPrefixLiveness
import Pnp4.Frontier.OneTapeMagnification.AdaptiveCachedBlockVisitListSoundness

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# A finite outer compiler for every block of one fixed alpha

The fixed-block list compiler has a finite state but, until this module, its
block cursor was external.  Here a dependent finite outer state adds that
cursor and sequentially runs one complete list verifier for every advertised
block.  Each block starts from its own literal blank slab.  The completed slab
of one block is deliberately discarded at the outer boundary: distinct block
replays are the independent blank-slab replays used by
`timedAlphaAllBlockVisitsCheckFromBlank`.

The resulting adaptive program is executable and finite.  This file does not
claim that the whole outer program is read-once.  The established theorem in
`TimedAlphaBlockVisitInputOrder` proves read-once inside each fixed-block list;
a query-order theorem between different block lists is a separate obligation.

The final definitions combine the outer program Boolean with the existing
rolling two-window fold.  Their reflection theorem is stated against the
single exact operational premise still separating the compiled outer program
from the already proved semantic all-block Boolean.
-/

/-- Finite state of the sequential all-block verifier.  The active payload is
dependent because both slab width and list length vary with the block. -/
inductive FiniteCachedAllBlocksStreamingState
    (State : Type) (T b : Nat)
    (width : Fin (T / b + 1) -> Nat)
    (visitCount : Fin (T / b + 1) -> Nat) where
  | active (block : Fin (T / b + 1))
      (phase : FiniteCachedBlockVisitListStreamingState
        State T (width block) (visitCount block))
  | completed
  | rejected
deriving Fintype

/-- Explicit finite-state instance using the cached machine's finite control. -/
def cachedAllBlocksStreamingStateFintype
    (machine : DeterministicMachine) (T b : Nat)
    (width : Fin (T / b + 1) -> Nat)
    (visitCount : Fin (T / b + 1) -> Nat) :
    Fintype (FiniteCachedAllBlocksStreamingState
      (cachedInputMachine machine).State T b width visitCount) := by
  letI := (cachedInputMachine machine).stateFintype
  exact inferInstance

/-- Product/sum presentation exposing that the outer carrier is one dependent
sum of per-block list carriers plus two global terminal states. -/
def finiteCachedAllBlocksStreamingStateEquiv
    (State : Type) (T b : Nat)
    (width : Fin (T / b + 1) -> Nat)
    (visitCount : Fin (T / b + 1) -> Nat) :
    FiniteCachedAllBlocksStreamingState State T b width visitCount ≃
      Sum
        (Sigma fun block : Fin (T / b + 1) =>
          FiniteCachedBlockVisitListStreamingState
            State T (width block) (visitCount block))
        (Sum Unit Unit) where
  toFun
    | .active block phase => .inl ⟨block, phase⟩
    | .completed => .inr (.inl ())
    | .rejected => .inr (.inr ())
  invFun
    | .inl ⟨block, phase⟩ => .active block phase
    | .inr (.inl _) => .completed
    | .inr (.inr _) => .rejected
  left_inv state := by cases state <;> rfl
  right_inv encoded := by
    rcases encoded with fields | terminal
    · rcases fields with ⟨block, phase⟩
      rfl
    · rcases terminal with completed | rejected
      · cases completed
        rfl
      · cases rejected
        rfl

/-- Exact outer carrier size before adding the generic compiler's fuel
coordinate. -/
theorem card_finiteCachedAllBlocksStreamingState
    (State : Type) [Fintype State] (T b : Nat)
    (width : Fin (T / b + 1) -> Nat)
    (visitCount : Fin (T / b + 1) -> Nat) :
    Fintype.card
        (FiniteCachedAllBlocksStreamingState
          State T b width visitCount) =
      (∑ block : Fin (T / b + 1),
        Fintype.card (FiniteCachedBlockVisitListStreamingState
          State T (width block) (visitCount block))) + 2 := by
  rw [Fintype.card_congr
    (finiteCachedAllBlocksStreamingStateEquiv
      State T b width visitCount)]
  simp

/-- The specialized all-block carrier for one advertised fixed alpha and one
family of stable fixed-block visit lists. -/
abbrev FiniteCachedTimedAlphaAllBlocksStreamingState
    (machine : DeterministicMachine) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)) :=
  FiniteCachedAllBlocksStreamingState
    (cachedInputMachine machine).State T b
    (fun block => advertisedBlockWidth alpha.offsets block)
    (fun block => (blockVisits block).length)

/-- Proof-only entry geometry required to initialize every dependent local
list carrier. -/
def FixedAlphaAllBlockVisitEntriesInside
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit State T)) : Prop :=
  forall block, FixedAlphaBlockVisitEntriesInside
    alpha block (blockVisits block)

/-- Executable entry-geometry check for one fixed block. -/
def fixedAlphaBlockVisitEntriesInsideCheck
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (block : Fin (T / b + 1))
    (visits : List (FixedAlphaBlockVisit State T)) : Bool :=
  visits.all fun visit => decide (WorkCellInSlab
    (advertisedBlockLower alpha.offsets block)
    (advertisedBlockWidth alpha.offsets block)
    visit.entry.workHead.val)

/-- The finite per-block check reflects the proof-only entry predicate. -/
theorem fixedAlphaBlockVisitEntriesInsideCheck_eq_true_iff
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (block : Fin (T / b + 1))
    (visits : List (FixedAlphaBlockVisit State T)) :
    fixedAlphaBlockVisitEntriesInsideCheck alpha block visits = true ↔
      FixedAlphaBlockVisitEntriesInside alpha block visits := by
  simp [fixedAlphaBlockVisitEntriesInsideCheck,
    FixedAlphaBlockVisitEntriesInside]

/-- Total finite geometry check over every advertised block. -/
def fixedAlphaAllBlockVisitEntriesInsideCheck
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit State T)) : Bool :=
  decide (forall block : Fin (T / b + 1),
    fixedAlphaBlockVisitEntriesInsideCheck
      alpha block (blockVisits block) = true)

/-- Exact reflection of the total all-block geometry check. -/
theorem fixedAlphaAllBlockVisitEntriesInsideCheck_eq_true_iff
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit State T)) :
    fixedAlphaAllBlockVisitEntriesInsideCheck alpha blockVisits = true ↔
      FixedAlphaAllBlockVisitEntriesInside alpha blockVisits := by
  simp [fixedAlphaAllBlockVisitEntriesInsideCheck,
    fixedAlphaBlockVisitEntriesInsideCheck_eq_true_iff,
    FixedAlphaAllBlockVisitEntriesInside]

/-- Simultaneous semantic acceptance supplies all erased entry-geometry
evidence needed by the outer verifier. -/
theorem fixedAlphaAllBlockVisitEntriesInside_of_acceptedFromBlank
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (haccepted : forall block,
      FixedAlphaBlockVisitListAcceptedFromBlank
        (cachedInputMachine machine) input alpha block
          (blockVisits block)) :
    FixedAlphaAllBlockVisitEntriesInside alpha blockVisits := by
  intro block
  exact fixedAlphaBlockVisitEntriesInside_of_replayAccepted
    (cachedInputMachine machine) input alpha block
    (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
    (blockVisits block) (haccepted block).2

/-- Start the first advertised block from its own blank slab.  There is always
at least one advertised block because the index type has size `T / b + 1`. -/
def finiteCachedAllBlocksStart
    (machine : DeterministicMachine)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits) :
    FiniteCachedTimedAlphaAllBlocksStreamingState
      machine alpha blockVisits :=
  let first : Fin (T / b + 1) := ⟨0, Nat.zero_lt_succ _⟩
  .active first
    (finiteCachedBlockVisitListStart machine alpha first
      (blankWorkSlab (advertisedBlockWidth alpha.offsets first))
      (blockVisits first) (hentries first))

/-- Only the two global terminal states halt the outer verifier. -/
def finiteCachedAllBlocksHalted
    {State : Type} {T b : Nat}
    {width : Fin (T / b + 1) -> Nat}
    {visitCount : Fin (T / b + 1) -> Nat} :
    FiniteCachedAllBlocksStreamingState State T b width visitCount -> Bool
  | .active _ _ => false
  | .completed => true
  | .rejected => true

/-- Fresh-input requests are delegated to the currently active fixed-block
list verifier. -/
def finiteCachedAllBlocksRequestsInput
    (machine : DeterministicMachine) (n : Nat)
    {T b : Nat}
    {alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b}
    {blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)} :
    FiniteCachedTimedAlphaAllBlocksStreamingState machine alpha blockVisits ->
      Bool
  | .active _ phase =>
      finiteCachedBlockVisitListRequestsInput machine n phase
  | .completed => false
  | .rejected => false

/-- Lift one same-block list transition, collapsing its local rejection into
the unique outer rejection state. -/
def liftFiniteCachedAllBlocksPhase
    (machine : DeterministicMachine)
    {T b : Nat}
    {alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b}
    {blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)}
    (block : Fin (T / b + 1)) :
    FiniteCachedBlockVisitListStreamingState
        (cachedInputMachine machine).State T
        (advertisedBlockWidth alpha.offsets block)
        (blockVisits block).length ->
      FiniteCachedTimedAlphaAllBlocksStreamingState
        machine alpha blockVisits
  | .rejected => .rejected
  | phase => .active block phase

/-- One executable outer transition.

An active list delegates to its fixed-block transition.  Once that list has
completed, exactly one silent outer transition either starts the successor
block from a fresh blank slab or enters global completion.  Supplying a symbol
at this silent block boundary is rejected. -/
def finiteCachedAllBlocksStreamingStep
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits) :
    FiniteCachedTimedAlphaAllBlocksStreamingState machine alpha blockVisits ->
      Option ReadOnlySymbol ->
      FiniteCachedTimedAlphaAllBlocksStreamingState machine alpha blockVisits
  | .completed, _ => .completed
  | .rejected, _ => .rejected
  | .active block phase, supplied =>
      match phase with
      | .rejected => .rejected
      | .completed _ =>
          match supplied with
          | some _ => .rejected
          | none =>
              if hnext : block.val + 1 < T / b + 1 then
                let next : Fin (T / b + 1) := ⟨block.val + 1, hnext⟩
                .active next
                  (finiteCachedBlockVisitListStart machine alpha next
                    (blankWorkSlab
                      (advertisedBlockWidth alpha.offsets next))
                    (blockVisits next) (hentries next))
              else
                .completed
      | FiniteCachedBlockVisitListStreamingState.active cursor localPhase =>
          liftFiniteCachedAllBlocksPhase machine block
            (finiteCachedBlockVisitListStreamingStep machine n alpha block
              (blockVisits block) (hentries block)
              (.active cursor localPhase) supplied)

/-- Exact same-block delegation equation. -/
theorem finiteCachedAllBlocksStreamingStep_active
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (block : Fin (T / b + 1))
    (cursor : Fin (blockVisits block).length)
    (phase : FiniteCachedVisitStreamingState
      (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block))
    (supplied : Option ReadOnlySymbol) :
    finiteCachedAllBlocksStreamingStep machine n alpha blockVisits hentries
        (.active block (.active cursor phase)) supplied =
      liftFiniteCachedAllBlocksPhase machine block
        (finiteCachedBlockVisitListStreamingStep machine n alpha block
          (blockVisits block) (hentries block) (.active cursor phase)
          supplied) :=
  rfl

/-- A completed nonfinal block starts the next block from a literal blank
slab; the previous block's returned slab is not carried across blocks. -/
theorem finiteCachedAllBlocksStreamingStep_completed_next
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (block : Fin (T / b + 1))
    (slab : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (hnext : block.val + 1 < T / b + 1) :
    finiteCachedAllBlocksStreamingStep machine n alpha blockVisits hentries
        (.active block (.completed slab)) none =
      let next : Fin (T / b + 1) := ⟨block.val + 1, hnext⟩
      .active next
        (finiteCachedBlockVisitListStart machine alpha next
          (blankWorkSlab (advertisedBlockWidth alpha.offsets next))
          (blockVisits next) (hentries next)) := by
  simp [finiteCachedAllBlocksStreamingStep, hnext]

/-- A completed final block enters global completion in one silent step. -/
theorem finiteCachedAllBlocksStreamingStep_completed_last
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (block : Fin (T / b + 1))
    (slab : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (hlast : ¬ block.val + 1 < T / b + 1) :
    finiteCachedAllBlocksStreamingStep machine n alpha blockVisits hentries
        (.active block (.completed slab)) none = .completed := by
  simp [finiteCachedAllBlocksStreamingStep, hlast]

/-- Outer acceptance is exactly the unique global completion state. -/
def finiteCachedAllBlocksAccept
    {State : Type} {T b : Nat}
    {width : Fin (T / b + 1) -> Nat}
    {visitCount : Fin (T / b + 1) -> Nat} :
    FiniteCachedAllBlocksStreamingState State T b width visitCount -> Bool
  | .completed => true
  | _ => false

/-- One finite streaming verifier sequentially covering every advertised
fixed block. -/
def finiteCachedTimedAlphaAllBlocksStreamingVerifier
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits) :
    FiniteStreamingVerifier ReadOnlySymbol where
  State := FiniteCachedTimedAlphaAllBlocksStreamingState
    machine alpha blockVisits
  stateFintype := cachedAllBlocksStreamingStateFintype machine T b
    (fun block => advertisedBlockWidth alpha.offsets block)
    (fun block => (blockVisits block).length)
  start := finiteCachedAllBlocksStart machine alpha blockVisits hentries
  halted := finiteCachedAllBlocksHalted
  requestsInput := finiteCachedAllBlocksRequestsInput machine n
  step := finiteCachedAllBlocksStreamingStep machine n alpha blockVisits
    hentries
  accept := finiteCachedAllBlocksAccept

/-- The outer adaptive query is exactly the current fixed-block list query. -/
def finiteCachedAllBlocksAdaptiveQueryIndex?
    (machine : DeterministicMachine) (n : Nat)
    {T b : Nat}
    {alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b}
    {blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)} :
    FiniteCachedTimedAlphaAllBlocksStreamingState machine alpha blockVisits ->
      Option (Fin n)
  | .active _ phase =>
      finiteCachedBlockVisitListAdaptiveQueryIndex? machine n phase
  | .completed => none
  | .rejected => none

/-- The outer selector is total at every state that requests a Boolean input:
the obligation is exactly the current fixed-block list obligation. -/
theorem finiteCachedAllBlocksAdaptiveQueryIndex?_total_of_requestsInput
    (machine : DeterministicMachine) (n : Nat)
    {T b : Nat}
    {alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b}
    {blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)}
    (state : FiniteCachedTimedAlphaAllBlocksStreamingState
      machine alpha blockVisits)
    (hrequest : finiteCachedAllBlocksRequestsInput machine n state = true) :
    ∃ index,
      finiteCachedAllBlocksAdaptiveQueryIndex? machine n state = some index := by
  cases state with
  | active block phase =>
      exact finiteCachedBlockVisitListAdaptiveQueryIndex?_total_of_requestsInput
        machine n phase hrequest
  | completed =>
      simp [finiteCachedAllBlocksRequestsInput] at hrequest
  | rejected =>
      simp [finiteCachedAllBlocksRequestsInput] at hrequest

/-- Total, input-independent start state.  Advertised entry geometry is a
finite decidable property of `alpha` and the visit lists; malformed geometry
starts in rejection instead of requiring an external acceptance proof. -/
def finiteCachedAllBlocksTotalStart
    (machine : DeterministicMachine)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)) :
    FiniteCachedTimedAlphaAllBlocksStreamingState
      machine alpha blockVisits :=
  if hcheck : fixedAlphaAllBlockVisitEntriesInsideCheck
      alpha blockVisits = true then
    finiteCachedAllBlocksStart machine alpha blockVisits
      ((fixedAlphaAllBlockVisitEntriesInsideCheck_eq_true_iff
        alpha blockVisits).1 hcheck)
  else
    .rejected

/-- Total transition.  Invalid advertised geometry is absorbing rejection;
valid geometry executes the proof-indexed transition, whose proof argument is
erased from runtime data. -/
def finiteCachedAllBlocksTotalStreamingStep
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)) :
    FiniteCachedTimedAlphaAllBlocksStreamingState machine alpha blockVisits ->
      Option ReadOnlySymbol ->
      FiniteCachedTimedAlphaAllBlocksStreamingState machine alpha blockVisits :=
  if hcheck : fixedAlphaAllBlockVisitEntriesInsideCheck
      alpha blockVisits = true then
    finiteCachedAllBlocksStreamingStep machine n alpha blockVisits
      ((fixedAlphaAllBlockVisitEntriesInsideCheck_eq_true_iff
        alpha blockVisits).1 hcheck)
  else
    fun _ _ => .rejected

/-- The total outer verifier is executable for every advertised fixed alpha
and visit family, including malformed ones. -/
def finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)) :
    FiniteStreamingVerifier ReadOnlySymbol where
  State := FiniteCachedTimedAlphaAllBlocksStreamingState
    machine alpha blockVisits
  stateFintype := cachedAllBlocksStreamingStateFintype machine T b
    (fun block => advertisedBlockWidth alpha.offsets block)
    (fun block => (blockVisits block).length)
  start := finiteCachedAllBlocksTotalStart machine alpha blockVisits
  halted := finiteCachedAllBlocksHalted
  requestsInput := finiteCachedAllBlocksRequestsInput machine n
  step := finiteCachedAllBlocksTotalStreamingStep machine n alpha blockVisits
  accept := finiteCachedAllBlocksAccept

/-- On valid advertised geometry the total verifier is definitionally the
proof-indexed verifier in its start and transition fields. -/
theorem finiteCachedAllBlocksTotalStart_eq_of_entries
    (machine : DeterministicMachine)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits) :
    finiteCachedAllBlocksTotalStart machine alpha blockVisits =
      finiteCachedAllBlocksStart machine alpha blockVisits hentries := by
  have hcheck :=
    (fixedAlphaAllBlockVisitEntriesInsideCheck_eq_true_iff
      alpha blockVisits).2 hentries
  simp [finiteCachedAllBlocksTotalStart, hcheck]

/-- Invalid geometry is rejected before any input query. -/
theorem finiteCachedAllBlocksTotalStart_eq_rejected_of_not_entries
    (machine : DeterministicMachine)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : ¬ FixedAlphaAllBlockVisitEntriesInside alpha blockVisits) :
    finiteCachedAllBlocksTotalStart machine alpha blockVisits = .rejected := by
  have hcheck : fixedAlphaAllBlockVisitEntriesInsideCheck
      alpha blockVisits ≠ true := by
    intro htrue
    exact hentries
      ((fixedAlphaAllBlockVisitEntriesInsideCheck_eq_true_iff
        alpha blockVisits).1 htrue)
  simp [finiteCachedAllBlocksTotalStart, hcheck]

/-- One live fixed-block microstep is definitionally the corresponding outer
microstep, with only the dependent block injection added. -/
theorem finiteCachedAllBlocks_inputDrivenCore_one_active
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (block : Fin (T / b + 1))
    (initial : FiniteCachedBlockVisitListStreamingState
      (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block)
      (blockVisits block).length)
    (input : Fin n -> Bool)
    (hlive : finiteCachedBlockVisitListHalted initial = false) :
    let listVerifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
      machine n alpha block
      (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
      (blockVisits block) (hentries block)
    let outerVerifier := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
      machine n alpha blockVisits
    outerVerifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedAllBlocksAdaptiveQueryIndex? machine n) input 1
        (.active block initial) =
      liftFiniteCachedAllBlocksPhase machine block
        (listVerifier.inputDrivenCore (fun bit => .bit bit)
          (finiteCachedBlockVisitListAdaptiveQueryIndex? machine n)
          input 1 initial) := by
  dsimp only
  have hcheck : fixedAlphaAllBlockVisitEntriesInsideCheck
      alpha blockVisits = true :=
    (fixedAlphaAllBlockVisitEntriesInsideCheck_eq_true_iff
      alpha blockVisits).2 hentries
  cases initial with
  | completed slab =>
      simp [finiteCachedBlockVisitListHalted] at hlive
  | rejected =>
      simp [finiteCachedBlockVisitListHalted] at hlive
  | active cursor phase =>
      simp [FiniteStreamingVerifier.inputDrivenCore,
        finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier,
        finiteCachedFixedAlphaBlockVisitListStreamingVerifier,
        finiteCachedAllBlocksHalted,
        finiteCachedBlockVisitListHalted,
        finiteCachedAllBlocksRequestsInput,
        finiteCachedBlockVisitListRequestsInput,
        finiteCachedAllBlocksAdaptiveQueryIndex?,
        finiteCachedBlockVisitListAdaptiveQueryIndex?,
        finiteCachedAllBlocksTotalStreamingStep, hcheck,
        finiteCachedAllBlocksStreamingStep,
        liftFiniteCachedAllBlocksPhase]

/-- Under the exact strict-prefix liveness invariant, an arbitrary complete
fixed-block input-driven segment embeds into the outer verifier. -/
theorem finiteCachedAllBlocks_inputDrivenCore_active_eq_lift_of_live
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (block : Fin (T / b + 1))
    (initial : FiniteCachedBlockVisitListStreamingState
      (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block)
      (blockVisits block).length)
    (input : Fin n -> Bool) (fuel : Nat)
    (hlive : ∀ spent : Nat, spent < fuel + 1 ->
      finiteCachedBlockVisitListHalted
        ((finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine n
          alpha block
          (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
          (blockVisits block) (hentries block)).inputDrivenCore
            (fun bit => .bit bit)
            (finiteCachedBlockVisitListAdaptiveQueryIndex? machine n)
            input spent initial) = false) :
    let listVerifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
      machine n alpha block
      (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
      (blockVisits block) (hentries block)
    let outerVerifier := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
      machine n alpha blockVisits
    outerVerifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedAllBlocksAdaptiveQueryIndex? machine n) input (fuel + 1)
        (.active block initial) =
      liftFiniteCachedAllBlocksPhase machine block
        (listVerifier.inputDrivenCore (fun bit => .bit bit)
          (finiteCachedBlockVisitListAdaptiveQueryIndex? machine n)
          input (fuel + 1) initial) := by
  dsimp only
  let listVerifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
    machine n alpha block
    (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
    (blockVisits block) (hentries block)
  let outerVerifier := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
    machine n alpha blockVisits
  let listSelector : listVerifier.State -> Option (Fin n) :=
    finiteCachedBlockVisitListAdaptiveQueryIndex? machine n
  let outerSelector : outerVerifier.State -> Option (Fin n) :=
    finiteCachedAllBlocksAdaptiveQueryIndex? machine n
  induction fuel generalizing initial with
  | zero =>
      exact finiteCachedAllBlocks_inputDrivenCore_one_active machine alpha
        blockVisits hentries block initial input (hlive 0 (by omega))
  | succ fuel ih =>
      have hzero : finiteCachedBlockVisitListHalted initial = false := by
        simpa [listVerifier, FiniteStreamingVerifier.inputDrivenCore] using
          hlive 0 (by omega)
      let next := listVerifier.inputDrivenCore (fun bit => .bit bit)
        listSelector input 1 initial
      have hnextLive : finiteCachedBlockVisitListHalted next = false := by
        simpa [next, listVerifier] using hlive 1 (by omega)
      have hfirst := finiteCachedAllBlocks_inputDrivenCore_one_active
        machine alpha blockVisits hentries block initial input hzero
      have htailLive : ∀ spent : Nat, spent < fuel + 1 ->
          finiteCachedBlockVisitListHalted
            (listVerifier.inputDrivenCore (fun bit => .bit bit) listSelector
              input spent next) = false := by
        intro spent hspent
        have horiginal := hlive (1 + spent) (by omega)
        rw [listVerifier.inputDrivenCore_add (fun bit => .bit bit)
          listSelector input 1 spent initial] at horiginal
        simpa [next, listVerifier, listSelector] using horiginal
      have htail := ih next (by
        simpa [listVerifier, listSelector] using htailLive)
      have hfirst' : outerVerifier.inputDrivenCore (fun bit => .bit bit)
          outerSelector input 1 (.active block initial) =
          liftFiniteCachedAllBlocksPhase machine block next := by
        simpa [outerVerifier, listVerifier, outerSelector, listSelector,
          next] using hfirst
      rw [outerVerifier.inputDrivenCore_succ_front (fun bit => .bit bit)
        outerSelector input (fuel + 1) (.active block initial)]
      rw [listVerifier.inputDrivenCore_succ_front (fun bit => .bit bit)
        listSelector input (fuel + 1) initial]
      rw [hfirst']
      cases hnextState : next with
      | completed slab =>
          simp [hnextState, finiteCachedBlockVisitListHalted] at hnextLive
      | rejected =>
          simp [hnextState, finiteCachedBlockVisitListHalted] at hnextLive
      | active cursor phase =>
          simpa [outerVerifier, listVerifier, outerSelector, listSelector,
            next, hnextState, liftFiniteCachedAllBlocksPhase] using htail

/-- Strongest currently unconditional semantic-to-outer composition for one
block, modulo the exact strict-prefix liveness invariant.  Semantic replay
supplies the completed local state; liveness ensures that the nonhalting outer
machine does not cross the block boundary before the advertised local fuel is
exhausted.  The final extra microstep performs precisely that boundary. -/
theorem finiteCachedAllBlocks_inputDrivenCore_advance_of_replayAccepted_of_live
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (block : Fin (T / b + 1))
    (haccepted : FixedAlphaBlockVisitReplayAccepted
      (cachedInputMachine machine) input alpha block
      (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
      (blockVisits block))
    (hlive : FiniteCachedBlockVisitListLiveBefore machine alpha block
      (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
      (blockVisits block) (hentries block) (fun index => input.get index)
      (finiteCachedBlockVisitListFuel (blockVisits block))) :
    let listVerifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
      machine input.length alpha block
      (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
      (blockVisits block) (hentries block)
    let outerVerifier := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
      machine input.length alpha blockVisits
    outerVerifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length)
        (fun index => input.get index)
        (finiteCachedBlockVisitListFuel (blockVisits block) + 1)
        (.active block listVerifier.start) =
      if hnext : block.val + 1 < T / b + 1 then
        let next : Fin (T / b + 1) := ⟨block.val + 1, hnext⟩
        .active next
          (finiteCachedBlockVisitListStart machine alpha next
            (blankWorkSlab (advertisedBlockWidth alpha.offsets next))
            (blockVisits next) (hentries next))
      else
        .completed := by
  dsimp only
  let listVerifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
    machine input.length alpha block
    (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
    (blockVisits block) (hentries block)
  let outerVerifier := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
    machine input.length alpha blockVisits
  let listSelector : listVerifier.State -> Option (Fin input.length) :=
    finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length
  let outerSelector : outerVerifier.State -> Option (Fin input.length) :=
    finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length
  let inputBits : Fin input.length -> Bool := fun index => input.get index
  have hcertificate :=
    (finiteCachedFixedAlphaBlockVisitListStreamingCertificate_iff
      machine input alpha block
      (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
      (blockVisits block)).2 haccepted
  obtain ⟨finalSlab, hlocalCore⟩ :=
    finiteCachedBlockVisitList_inputDrivenCore_completed_of_certificate
      machine input alpha block
      (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
      (blockVisits block) (hentries block) hcertificate
  change listVerifier.inputDrivenCore (fun bit => .bit bit) listSelector
      inputBits (finiteCachedBlockVisitListFuel (blockVisits block))
      listVerifier.start = .completed finalSlab at hlocalCore
  have houterLocal : outerVerifier.inputDrivenCore (fun bit => .bit bit)
      outerSelector inputBits
      (finiteCachedBlockVisitListFuel (blockVisits block))
      (.active block listVerifier.start) =
        .active block (.completed finalSlab) := by
    cases hfuel : finiteCachedBlockVisitListFuel (blockVisits block) with
    | zero =>
        have hstart : listVerifier.start = .completed finalSlab := by
          simpa [hfuel, FiniteStreamingVerifier.inputDrivenCore] using
            hlocalCore
        simp [FiniteStreamingVerifier.inputDrivenCore, hstart]
    | succ fuel =>
        have hsim :=
          finiteCachedAllBlocks_inputDrivenCore_active_eq_lift_of_live
            machine alpha blockVisits hentries block listVerifier.start
            inputBits fuel (by
              simpa [FiniteCachedBlockVisitListLiveBefore, listVerifier,
                listSelector, hfuel] using hlive)
        have hsim' : outerVerifier.inputDrivenCore (fun bit => .bit bit)
            outerSelector inputBits (fuel + 1)
            (.active block listVerifier.start) =
              liftFiniteCachedAllBlocksPhase machine block
                (listVerifier.inputDrivenCore (fun bit => .bit bit)
                  listSelector inputBits (fuel + 1) listVerifier.start) := by
          simpa [outerVerifier, listVerifier, outerSelector, listSelector]
            using hsim
        have hlocalCore' : listVerifier.inputDrivenCore
            (fun bit => .bit bit) listSelector inputBits (fuel + 1)
            listVerifier.start = .completed finalSlab := by
          rw [← hfuel]
          exact hlocalCore
        rw [hlocalCore'] at hsim'
        simpa [liftFiniteCachedAllBlocksPhase] using hsim'
  rw [outerVerifier.inputDrivenCore_add (fun bit => .bit bit)
    outerSelector inputBits
    (finiteCachedBlockVisitListFuel (blockVisits block)) 1
    (.active block listVerifier.start)]
  rw [houterLocal]
  have hcheck : fixedAlphaAllBlockVisitEntriesInsideCheck
      alpha blockVisits = true :=
    (fixedAlphaAllBlockVisitEntriesInsideCheck_eq_true_iff
      alpha blockVisits).2 hentries
  simp [outerVerifier,
    FiniteStreamingVerifier.inputDrivenCore,
    finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier,
    finiteCachedAllBlocksHalted, finiteCachedAllBlocksRequestsInput,
    finiteCachedBlockVisitListRequestsInput,
    finiteCachedAllBlocksTotalStreamingStep, hcheck,
    finiteCachedAllBlocksStreamingStep]

/-- Semantic replay acceptance advances the executable outer verifier across
one whole block and its silent boundary step.  Strict-prefix liveness is now a
theorem of the fixed-block certificate, rather than an extra premise. -/
theorem finiteCachedAllBlocks_inputDrivenCore_advance_of_replayAccepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (block : Fin (T / b + 1))
    (haccepted : FixedAlphaBlockVisitReplayAccepted
      (cachedInputMachine machine) input alpha block
      (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
      (blockVisits block)) :
    let listVerifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
      machine input.length alpha block
      (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
      (blockVisits block) (hentries block)
    let outerVerifier := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
      machine input.length alpha blockVisits
    outerVerifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length)
        (fun index => input.get index)
        (finiteCachedBlockVisitListFuel (blockVisits block) + 1)
        (.active block listVerifier.start) =
      if hnext : block.val + 1 < T / b + 1 then
        let next : Fin (T / b + 1) := ⟨block.val + 1, hnext⟩
        .active next
          (finiteCachedBlockVisitListStart machine alpha next
            (blankWorkSlab (advertisedBlockWidth alpha.offsets next))
            (blockVisits next) (hentries next))
      else
        .completed := by
  exact finiteCachedAllBlocks_inputDrivenCore_advance_of_replayAccepted_of_live
    machine input alpha blockVisits hentries block haccepted
      (finiteCachedBlockVisitList_liveBefore_of_replayAccepted
        machine input alpha block
          (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
          (blockVisits block) (hentries block) haccepted)

/-- A semantically invalid fixed block cannot reach a completed local state
at or before its exact list budget.  Otherwise terminal absorption would make
the exact-fuel run complete, contradicting fixed-block soundness. -/
theorem finiteCachedBlockVisitList_inputDrivenCore_ne_completed_of_not_replayAccepted
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
    (hnot : ¬ FixedAlphaBlockVisitReplayAccepted
      (cachedInputMachine machine) input alpha block initialSlab visits)
    (spent : Nat) (hspent : spent ≤ finiteCachedBlockVisitListFuel visits)
    (finalSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block)) :
    let verifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
      machine input.length alpha block initialSlab visits hentries
    verifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length)
        (fun index => input.get index) spent verifier.start ≠
      .completed finalSlab := by
  let verifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
    machine input.length alpha block initialSlab visits hentries
  let selector : verifier.State -> Option (Fin input.length) :=
    finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length
  let inputBits : Fin input.length -> Bool := fun index => input.get index
  change verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
      spent verifier.start ≠ .completed finalSlab
  intro hcompleted
  have hsplit : finiteCachedBlockVisitListFuel visits =
      spent + (finiteCachedBlockVisitListFuel visits - spent) := by
    omega
  have hfull : verifier.inputDrivenCore (fun bit => .bit bit) selector
      inputBits (finiteCachedBlockVisitListFuel visits) verifier.start =
        .completed finalSlab := by
    calc
      verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
          (finiteCachedBlockVisitListFuel visits) verifier.start =
        verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
          (spent + (finiteCachedBlockVisitListFuel visits - spent))
          verifier.start :=
        congrArg (fun fuel => verifier.inputDrivenCore
          (fun bit => .bit bit) selector inputBits fuel verifier.start) hsplit
      _ = verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
          (finiteCachedBlockVisitListFuel visits - spent)
          (verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
            spent verifier.start) :=
        verifier.inputDrivenCore_add (fun bit => .bit bit) selector inputBits
          spent (finiteCachedBlockVisitListFuel visits - spent) verifier.start
      _ = verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
          (finiteCachedBlockVisitListFuel visits - spent)
          (.completed finalSlab) := by rw [hcompleted]
      _ = .completed finalSlab :=
        verifier.inputDrivenCore_eq_self_of_halted (fun bit => .bit bit)
          selector inputBits (finiteCachedBlockVisitListFuel visits - spent)
            (.completed finalSlab) rfl
  have hcertificate :=
    finiteCachedFixedAlphaBlockVisitListStreamingCertificate_of_inputDrivenCore_completed
      machine input alpha block initialSlab visits hentries finalSlab (by
        simpa [verifier, selector, inputBits] using hfull)
  exact hnot ((finiteCachedFixedAlphaBlockVisitListStreamingCertificate_iff
    machine input alpha block initialSlab visits).1 hcertificate)

/-- Until the exact local budget is exhausted, a semantically invalid block
is simulated by the outer verifier through the same dependent lift.  The only
possible local terminal is rejection, which the lift makes globally
absorbing; early completion was excluded by the preceding soundness lemma. -/
theorem finiteCachedAllBlocks_inputDrivenCore_eq_lift_of_not_replayAccepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (block : Fin (T / b + 1))
    (hnot : ¬ FixedAlphaBlockVisitReplayAccepted
      (cachedInputMachine machine) input alpha block
      (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
      (blockVisits block))
    (spent : Nat)
    (hspent : spent ≤ finiteCachedBlockVisitListFuel (blockVisits block)) :
    let listVerifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
      machine input.length alpha block
      (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
      (blockVisits block) (hentries block)
    let outerVerifier := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
      machine input.length alpha blockVisits
    outerVerifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length)
        (fun index => input.get index) spent
        (.active block listVerifier.start) =
      liftFiniteCachedAllBlocksPhase machine block
        (listVerifier.inputDrivenCore (fun bit => .bit bit)
          (finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length)
          (fun index => input.get index) spent listVerifier.start) := by
  dsimp only
  let listVerifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
    machine input.length alpha block
    (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
    (blockVisits block) (hentries block)
  let outerVerifier := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
    machine input.length alpha blockVisits
  let listSelector : listVerifier.State -> Option (Fin input.length) :=
    finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length
  let outerSelector : outerVerifier.State -> Option (Fin input.length) :=
    finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length
  let inputBits : Fin input.length -> Bool := fun index => input.get index
  change outerVerifier.inputDrivenCore (fun bit => .bit bit) outerSelector
      inputBits spent (.active block listVerifier.start) =
    liftFiniteCachedAllBlocksPhase machine block
      (listVerifier.inputDrivenCore (fun bit => .bit bit) listSelector
        inputBits spent listVerifier.start)
  revert hspent
  induction spent with
  | zero =>
      intro _
      have hstartNotRejected : listVerifier.start ≠ .rejected := by
        change finiteCachedBlockVisitListStart machine alpha block
          (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
            (blockVisits block) (hentries block) ≠ .rejected
        unfold finiteCachedBlockVisitListStart
        split <;> simp [finiteCachedBlockVisitListActiveState]
      cases hstart : listVerifier.start with
      | active cursor phase =>
          simp [FiniteStreamingVerifier.inputDrivenCore,
            liftFiniteCachedAllBlocksPhase]
      | rejected =>
          exact (hstartNotRejected hstart).elim
      | completed slab =>
          have hne :=
            finiteCachedBlockVisitList_inputDrivenCore_ne_completed_of_not_replayAccepted
              machine input alpha block
                (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
                (blockVisits block) (hentries block) hnot 0 (by omega) slab
          exfalso
          apply hne
          simpa [listVerifier, listSelector, inputBits,
            FiniteStreamingVerifier.inputDrivenCore] using hstart
  | succ spent ih =>
      intro hspent
      have hspentPrevious :
          spent ≤ finiteCachedBlockVisitListFuel (blockVisits block) := by
        omega
      have ihState := ih hspentPrevious
      let localState := listVerifier.inputDrivenCore (fun bit => .bit bit)
        listSelector inputBits spent listVerifier.start
      cases hlocal : localState with
      | active cursor phase =>
          have hone := finiteCachedAllBlocks_inputDrivenCore_one_active
            machine alpha blockVisits hentries block (.active cursor phase)
              inputBits rfl
          rw [outerVerifier.inputDrivenCore_add (fun bit => .bit bit)
            outerSelector inputBits spent 1 (.active block listVerifier.start)]
          rw [listVerifier.inputDrivenCore_add (fun bit => .bit bit)
            listSelector inputBits spent 1 listVerifier.start]
          rw [ihState]
          change listVerifier.inputDrivenCore (fun bit => .bit bit)
              listSelector inputBits spent listVerifier.start =
            .active cursor phase at hlocal
          rw [hlocal]
          simpa [outerVerifier, listVerifier, outerSelector, listSelector,
            inputBits] using hone
      | rejected =>
          rw [outerVerifier.inputDrivenCore_add (fun bit => .bit bit)
            outerSelector inputBits spent 1 (.active block listVerifier.start)]
          rw [listVerifier.inputDrivenCore_add (fun bit => .bit bit)
            listSelector inputBits spent 1 listVerifier.start]
          rw [ihState]
          change listVerifier.inputDrivenCore (fun bit => .bit bit)
              listSelector inputBits spent listVerifier.start =
            .rejected at hlocal
          rw [hlocal]
          simp only [liftFiniteCachedAllBlocksPhase]
          rw [outerVerifier.inputDrivenCore_eq_self_of_halted
            (fun bit => .bit bit) outerSelector inputBits 1 .rejected (by rfl)]
          rw [listVerifier.inputDrivenCore_eq_self_of_halted
            (fun bit => .bit bit) listSelector inputBits 1 .rejected (by rfl)]
      | completed slab =>
          have hne :=
            finiteCachedBlockVisitList_inputDrivenCore_ne_completed_of_not_replayAccepted
              machine input alpha block
                (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
                (blockVisits block) (hentries block) hnot spent
                  hspentPrevious slab
          exfalso
          apply hne
          simpa [listVerifier, listSelector, inputBits, localState] using hlocal

/-- A semantically invalid block drives the outer verifier to global
rejection within that block's exact local budget. -/
theorem finiteCachedAllBlocks_inputDrivenCore_rejected_of_not_replayAccepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (block : Fin (T / b + 1))
    (hnot : ¬ FixedAlphaBlockVisitReplayAccepted
      (cachedInputMachine machine) input alpha block
      (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
      (blockVisits block)) :
    let listVerifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
      machine input.length alpha block
      (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
      (blockVisits block) (hentries block)
    let outerVerifier := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
      machine input.length alpha blockVisits
    outerVerifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length)
        (fun index => input.get index)
        (finiteCachedBlockVisitListFuel (blockVisits block))
        (.active block listVerifier.start) = .rejected := by
  dsimp only
  let listVerifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
    machine input.length alpha block
    (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
    (blockVisits block) (hentries block)
  let listSelector : listVerifier.State -> Option (Fin input.length) :=
    finiteCachedBlockVisitListAdaptiveQueryIndex? machine input.length
  let inputBits : Fin input.length -> Bool := fun index => input.get index
  let localResult := listVerifier.inputDrivenCore (fun bit => .bit bit)
    listSelector inputBits
    (finiteCachedBlockVisitListFuel (blockVisits block)) listVerifier.start
  have hhalted : listVerifier.halted localResult = true := by
    simpa [listVerifier, listSelector, inputBits, localResult] using
      finiteCachedBlockVisitList_inputDrivenCore_halted
        machine input alpha block
          (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
          (blockVisits block) (hentries block)
  have hlocalRejected : localResult = .rejected := by
    cases hresult : localResult with
    | active cursor phase =>
        rw [hresult] at hhalted
        change finiteCachedBlockVisitListHalted (.active cursor phase) = true
          at hhalted
        simp [finiteCachedBlockVisitListHalted] at hhalted
    | rejected =>
        rfl
    | completed slab =>
        have hne :=
          finiteCachedBlockVisitList_inputDrivenCore_ne_completed_of_not_replayAccepted
            machine input alpha block
              (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
              (blockVisits block) (hentries block) hnot
                (finiteCachedBlockVisitListFuel (blockVisits block)) le_rfl slab
        exfalso
        apply hne
        simpa [listVerifier, listSelector, inputBits, localResult] using hresult
  have hsim :=
    finiteCachedAllBlocks_inputDrivenCore_eq_lift_of_not_replayAccepted
      machine input alpha blockVisits hentries block hnot
        (finiteCachedBlockVisitListFuel (blockVisits block)) le_rfl
  have hsim' :
      (finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
        machine input.length alpha blockVisits).inputDrivenCore
          (fun bit => .bit bit)
          (finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length)
          (fun index => input.get index)
          (finiteCachedBlockVisitListFuel (blockVisits block))
          (.active block listVerifier.start) =
        liftFiniteCachedAllBlocksPhase machine block localResult := by
    simpa [listVerifier, listSelector, inputBits, localResult] using hsim
  rw [hlocalRejected] at hsim'
  simpa [liftFiniteCachedAllBlocksPhase] using hsim'

/-- Total outer fuel: exact per-block list fuel plus one silent block-boundary
transition for each advertised block. -/
def finiteCachedAllBlocksFuel
    {State : Type} {T b : Nat}
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit State T)) : Nat :=
  ∑ block : Fin (T / b + 1),
    (finiteCachedBlockVisitListFuel (blockVisits block) + 1)

/-- Fuel consumed by the first `count` advertised blocks.  Writing this as a
finite sum makes the global execution induction independent of any list
encoding of `Fin`. -/
def finiteCachedAllBlocksPrefixFuel
    {State : Type} {T b : Nat}
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit State T)) (count : Nat) : Nat :=
  ∑ block : Fin (T / b + 1),
    if block.val < count then
      finiteCachedBlockVisitListFuel (blockVisits block) + 1
    else
      0

@[simp]
theorem finiteCachedAllBlocksPrefixFuel_zero
    {State : Type} {T b : Nat}
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit State T)) :
    finiteCachedAllBlocksPrefixFuel blockVisits 0 = 0 := by
  simp [finiteCachedAllBlocksPrefixFuel]

/-- Extending an in-range prefix by one block adds exactly that block's list
fuel and its silent boundary transition. -/
theorem finiteCachedAllBlocksPrefixFuel_succ
    {State : Type} {T b : Nat}
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit State T))
    (count : Nat) (hcount : count < T / b + 1) :
    finiteCachedAllBlocksPrefixFuel blockVisits (count + 1) =
      finiteCachedAllBlocksPrefixFuel blockVisits count +
        (finiteCachedBlockVisitListFuel
          (blockVisits ⟨count, hcount⟩) + 1) := by
  classical
  let current : Fin (T / b + 1) := ⟨count, hcount⟩
  let contribution := fun block : Fin (T / b + 1) =>
    finiteCachedBlockVisitListFuel (blockVisits block) + 1
  have hpoint : ∀ block : Fin (T / b + 1),
      (if block.val < count + 1 then contribution block else 0) =
        (if block = current then contribution block else 0) +
          (if block.val < count then contribution block else 0) := by
    intro block
    by_cases hlt : block.val < count
    · have hltSucc : block.val < count + 1 := by omega
      have hne : block ≠ current := by
        intro heq
        have hval := congrArg Fin.val heq
        simp [current] at hval
        omega
      simp [hlt, hltSucc, hne]
    · by_cases heq : block = current
      · subst block
        simp [current]
      · have hnotSucc : ¬ block.val < count + 1 := by
          intro hltSucc
          have hval : block.val = count := by omega
          apply heq
          apply Fin.ext
          simpa [current] using hval
        simp [hlt, hnotSucc, heq]
  unfold finiteCachedAllBlocksPrefixFuel
  calc
    (∑ block : Fin (T / b + 1),
        if block.val < count + 1 then contribution block else 0) =
      ∑ block : Fin (T / b + 1),
        ((if block = current then contribution block else 0) +
          (if block.val < count then contribution block else 0)) := by
        apply Finset.sum_congr rfl
        intro block _
        exact hpoint block
    _ = (∑ block : Fin (T / b + 1),
          if block = current then contribution block else 0) +
        ∑ block : Fin (T / b + 1),
          if block.val < count then contribution block else 0 := by
        exact Finset.sum_add_distrib
    _ = contribution current +
        ∑ block : Fin (T / b + 1),
          if block.val < count then contribution block else 0 := by
        simp
    _ = (∑ block : Fin (T / b + 1),
          if block.val < count then contribution block else 0) +
        contribution current := by omega
    _ = finiteCachedAllBlocksPrefixFuel blockVisits count +
        (finiteCachedBlockVisitListFuel
          (blockVisits ⟨count, hcount⟩) + 1) := by
        rfl

/-- The full prefix sum is the advertised global fuel. -/
theorem finiteCachedAllBlocksPrefixFuel_all
    {State : Type} {T b : Nat}
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit State T)) :
    finiteCachedAllBlocksPrefixFuel blockVisits (T / b + 1) =
      finiteCachedAllBlocksFuel blockVisits := by
  simp [finiteCachedAllBlocksPrefixFuel, finiteCachedAllBlocksFuel]

/-- Exact global prefix invariant.  If every fixed block semantically replays
from blank, consuming the first `count` block budgets places the outer machine
at the literal start of block `count`; consuming all budgets completes it. -/
theorem finiteCachedAllBlocks_inputDrivenCore_prefix_of_replayAccepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (count : Nat) (hcount : count ≤ T / b + 1)
    (haccepted : forall block : Fin (T / b + 1), block.val < count ->
      FixedAlphaBlockVisitReplayAccepted
        (cachedInputMachine machine) input alpha block
        (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
        (blockVisits block)) :
    let verifier := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
      machine input.length alpha blockVisits
    verifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length)
        (fun index => input.get index)
        (finiteCachedAllBlocksPrefixFuel blockVisits count)
        verifier.start =
      if hactive : count < T / b + 1 then
        let block : Fin (T / b + 1) := ⟨count, hactive⟩
        .active block
          (finiteCachedBlockVisitListStart machine alpha block
            (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
            (blockVisits block) (hentries block))
      else
        .completed := by
  dsimp only
  let verifier := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
    machine input.length alpha blockVisits
  let selector : verifier.State -> Option (Fin input.length) :=
    finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length
  let inputBits : Fin input.length -> Bool := fun index => input.get index
  change verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
      (finiteCachedAllBlocksPrefixFuel blockVisits count) verifier.start = _
  revert hcount haccepted
  induction count with
  | zero =>
      intro _ _
      have hcheck : fixedAlphaAllBlockVisitEntriesInsideCheck
          alpha blockVisits = true :=
        (fixedAlphaAllBlockVisitEntriesInsideCheck_eq_true_iff
          alpha blockVisits).2 hentries
      simp [verifier, selector, inputBits,
        FiniteStreamingVerifier.inputDrivenCore,
        finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier,
        finiteCachedAllBlocksTotalStart, hcheck,
        finiteCachedAllBlocksStart]
  | succ count ih =>
      intro hcount haccepted
      have hlt : count < T / b + 1 := by omega
      let block : Fin (T / b + 1) := ⟨count, hlt⟩
      have ihState : verifier.inputDrivenCore (fun bit => .bit bit)
          selector inputBits
          (finiteCachedAllBlocksPrefixFuel blockVisits count)
          verifier.start =
        .active block
          (finiteCachedBlockVisitListStart machine alpha block
            (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
            (blockVisits block) (hentries block)) := by
        have hprevious := ih (by omega) (fun previous hprevious =>
          haccepted previous (by omega))
        simpa [hlt, block] using hprevious
      have hprefix := finiteCachedAllBlocksPrefixFuel_succ
        blockVisits count hlt
      have hblock :=
        finiteCachedAllBlocks_inputDrivenCore_advance_of_replayAccepted
          machine input alpha blockVisits hentries block
            (haccepted block (by simp [block]))
      have hblock' : verifier.inputDrivenCore (fun bit => .bit bit)
          selector inputBits
          (finiteCachedBlockVisitListFuel (blockVisits block) + 1)
          (.active block
            (finiteCachedBlockVisitListStart machine alpha block
              (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
              (blockVisits block) (hentries block))) =
        if hnext : count + 1 < T / b + 1 then
          let next : Fin (T / b + 1) := ⟨count + 1, hnext⟩
          .active next
            (finiteCachedBlockVisitListStart machine alpha next
              (blankWorkSlab (advertisedBlockWidth alpha.offsets next))
              (blockVisits next) (hentries next))
        else
          .completed := by
        simpa [verifier, selector, inputBits, block] using hblock
      have hresult : verifier.inputDrivenCore (fun bit => .bit bit)
          selector inputBits
          (finiteCachedAllBlocksPrefixFuel blockVisits (count + 1))
          verifier.start =
        if hnext : count + 1 < T / b + 1 then
          let next : Fin (T / b + 1) := ⟨count + 1, hnext⟩
          .active next
            (finiteCachedBlockVisitListStart machine alpha next
              (blankWorkSlab (advertisedBlockWidth alpha.offsets next))
              (blockVisits next) (hentries next))
        else
          .completed := by
        calc
          verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
              (finiteCachedAllBlocksPrefixFuel blockVisits (count + 1))
              verifier.start =
            verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
              (finiteCachedAllBlocksPrefixFuel blockVisits count +
                (finiteCachedBlockVisitListFuel (blockVisits block) + 1))
              verifier.start :=
            congrArg (fun fuel => verifier.inputDrivenCore
              (fun bit => .bit bit) selector inputBits fuel verifier.start)
              hprefix
          _ = verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
              (finiteCachedBlockVisitListFuel (blockVisits block) + 1)
              (verifier.inputDrivenCore (fun bit => .bit bit) selector
                inputBits (finiteCachedAllBlocksPrefixFuel blockVisits count)
                verifier.start) :=
            verifier.inputDrivenCore_add (fun bit => .bit bit) selector
              inputBits (finiteCachedAllBlocksPrefixFuel blockVisits count)
                (finiteCachedBlockVisitListFuel (blockVisits block) + 1)
                  verifier.start
          _ = verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
              (finiteCachedBlockVisitListFuel (blockVisits block) + 1)
              (.active block
                (finiteCachedBlockVisitListStart machine alpha block
                  (blankWorkSlab
                    (advertisedBlockWidth alpha.offsets block))
                  (blockVisits block) (hentries block))) := by
            rw [ihState]
          _ = _ := hblock'
      simpa only [Nat.succ_eq_add_one] using hresult

/-- If some block in the first `count` positions is semantically invalid,
the exact prefix budget leaves the total outer verifier in absorbing global
rejection. -/
theorem finiteCachedAllBlocks_inputDrivenCore_prefix_rejected_of_not_replayAccepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (count : Nat) (hcount : count ≤ T / b + 1)
    (hnot : ¬ forall block : Fin (T / b + 1), block.val < count ->
      FixedAlphaBlockVisitReplayAccepted
        (cachedInputMachine machine) input alpha block
        (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
        (blockVisits block)) :
    let verifier := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
      machine input.length alpha blockVisits
    verifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length)
        (fun index => input.get index)
        (finiteCachedAllBlocksPrefixFuel blockVisits count)
        verifier.start = .rejected := by
  dsimp only
  let verifier := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
    machine input.length alpha blockVisits
  let selector : verifier.State -> Option (Fin input.length) :=
    finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length
  let inputBits : Fin input.length -> Bool := fun index => input.get index
  change verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
      (finiteCachedAllBlocksPrefixFuel blockVisits count) verifier.start =
        .rejected
  revert hcount hnot
  induction count with
  | zero =>
      intro _ hnot
      exfalso
      apply hnot
      intro block hbefore
      omega
  | succ count ih =>
      intro hcount hnot
      have hlt : count < T / b + 1 := by omega
      let block : Fin (T / b + 1) := ⟨count, hlt⟩
      have hprefix := finiteCachedAllBlocksPrefixFuel_succ
        blockVisits count hlt
      by_cases hprevious : forall previous : Fin (T / b + 1),
          previous.val < count ->
            FixedAlphaBlockVisitReplayAccepted
              (cachedInputMachine machine) input alpha previous
              (blankWorkSlab
                (advertisedBlockWidth alpha.offsets previous))
              (blockVisits previous)
      · have hcurrentNot : ¬ FixedAlphaBlockVisitReplayAccepted
            (cachedInputMachine machine) input alpha block
            (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
            (blockVisits block) := by
          intro hcurrent
          apply hnot
          intro candidate hcandidate
          by_cases heq : candidate.val = count
          · have hcandidateBlock : candidate = block := by
              apply Fin.ext
              simpa [block] using heq
            subst candidate
            exact hcurrent
          · exact hprevious candidate (by omega)
        have hbefore :=
          finiteCachedAllBlocks_inputDrivenCore_prefix_of_replayAccepted
            machine input alpha blockVisits hentries count (by omega)
              hprevious
        have hbefore' : verifier.inputDrivenCore (fun bit => .bit bit)
            selector inputBits
            (finiteCachedAllBlocksPrefixFuel blockVisits count)
            verifier.start =
          .active block
            (finiteCachedBlockVisitListStart machine alpha block
              (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
              (blockVisits block) (hentries block)) := by
          simpa [verifier, selector, inputBits, hlt, block] using hbefore
        have hreject :=
          finiteCachedAllBlocks_inputDrivenCore_rejected_of_not_replayAccepted
            machine input alpha blockVisits hentries block hcurrentNot
        let listVerifier :=
          finiteCachedFixedAlphaBlockVisitListStreamingVerifier
            machine input.length alpha block
            (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
            (blockVisits block) (hentries block)
        have hreject' : verifier.inputDrivenCore (fun bit => .bit bit)
            selector inputBits
            (finiteCachedBlockVisitListFuel (blockVisits block))
            (.active block listVerifier.start) = .rejected := by
          simpa [verifier, selector, inputBits, listVerifier] using hreject
        have hcostReject : verifier.inputDrivenCore (fun bit => .bit bit)
            selector inputBits
            (finiteCachedBlockVisitListFuel (blockVisits block) + 1)
            (.active block listVerifier.start) = .rejected := by
          rw [verifier.inputDrivenCore_add (fun bit => .bit bit) selector
            inputBits (finiteCachedBlockVisitListFuel (blockVisits block)) 1
              (.active block listVerifier.start)]
          rw [hreject']
          exact verifier.inputDrivenCore_eq_self_of_halted
            (fun bit => .bit bit) selector inputBits 1 .rejected rfl
        calc
          verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
              (finiteCachedAllBlocksPrefixFuel blockVisits (count + 1))
              verifier.start =
            verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
              (finiteCachedAllBlocksPrefixFuel blockVisits count +
                (finiteCachedBlockVisitListFuel (blockVisits block) + 1))
              verifier.start :=
            congrArg (fun fuel => verifier.inputDrivenCore
              (fun bit => .bit bit) selector inputBits fuel verifier.start)
                hprefix
          _ = verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
              (finiteCachedBlockVisitListFuel (blockVisits block) + 1)
              (verifier.inputDrivenCore (fun bit => .bit bit) selector
                inputBits (finiteCachedAllBlocksPrefixFuel blockVisits count)
                  verifier.start) :=
            verifier.inputDrivenCore_add (fun bit => .bit bit) selector
              inputBits (finiteCachedAllBlocksPrefixFuel blockVisits count)
                (finiteCachedBlockVisitListFuel (blockVisits block) + 1)
                  verifier.start
          _ = verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
              (finiteCachedBlockVisitListFuel (blockVisits block) + 1)
              (.active block listVerifier.start) := by
            rw [hbefore']
            rfl
          _ = .rejected := hcostReject
      · have hbeforeRejected := ih (by omega) hprevious
        have hbeforeRejected' : verifier.inputDrivenCore
            (fun bit => .bit bit) selector inputBits
            (finiteCachedAllBlocksPrefixFuel blockVisits count)
            verifier.start = .rejected := by
          simpa [verifier, selector, inputBits] using hbeforeRejected
        calc
          verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
              (finiteCachedAllBlocksPrefixFuel blockVisits (count + 1))
              verifier.start =
            verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
              (finiteCachedAllBlocksPrefixFuel blockVisits count +
                (finiteCachedBlockVisitListFuel (blockVisits block) + 1))
              verifier.start :=
            congrArg (fun fuel => verifier.inputDrivenCore
              (fun bit => .bit bit) selector inputBits fuel verifier.start)
                hprefix
          _ = verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
              (finiteCachedBlockVisitListFuel (blockVisits block) + 1)
              (verifier.inputDrivenCore (fun bit => .bit bit) selector
                inputBits (finiteCachedAllBlocksPrefixFuel blockVisits count)
                  verifier.start) :=
            verifier.inputDrivenCore_add (fun bit => .bit bit) selector
              inputBits (finiteCachedAllBlocksPrefixFuel blockVisits count)
                (finiteCachedBlockVisitListFuel (blockVisits block) + 1)
                  verifier.start
          _ = verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
              (finiteCachedBlockVisitListFuel (blockVisits block) + 1)
              .rejected := by rw [hbeforeRejected']
          _ = .rejected :=
            verifier.inputDrivenCore_eq_self_of_halted
              (fun bit => .bit bit) selector inputBits
                (finiteCachedBlockVisitListFuel (blockVisits block) + 1)
                  .rejected rfl

/-- Simultaneous semantic acceptance of every fixed block forces the total
outer execution to reach its unique global completion state at the advertised
sum fuel. -/
theorem finiteCachedAllBlocks_inputDrivenCore_completed_of_acceptedFromBlank
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (haccepted : forall block : Fin (T / b + 1),
      FixedAlphaBlockVisitListAcceptedFromBlank
        (cachedInputMachine machine) input alpha block
        (blockVisits block)) :
    let verifier := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
      machine input.length alpha blockVisits
    verifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length)
        (fun index => input.get index)
        (finiteCachedAllBlocksFuel blockVisits) verifier.start =
      .completed := by
  let hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits :=
    fixedAlphaAllBlockVisitEntriesInside_of_acceptedFromBlank
      machine input alpha blockVisits haccepted
  have hprefix :=
    finiteCachedAllBlocks_inputDrivenCore_prefix_of_replayAccepted
      machine input alpha blockVisits hentries (T / b + 1) le_rfl
        (fun block _ => (haccepted block).2)
  rw [finiteCachedAllBlocksPrefixFuel_all blockVisits] at hprefix
  simpa using hprefix

/-- Replay acceptance alone (without the separate chronological-list
predicate) is exactly what the outer machine executes. -/
theorem finiteCachedAllBlocks_inputDrivenCore_completed_of_replayAccepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (haccepted : forall block : Fin (T / b + 1),
      FixedAlphaBlockVisitReplayAccepted
        (cachedInputMachine machine) input alpha block
        (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
        (blockVisits block)) :
    let verifier := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
      machine input.length alpha blockVisits
    verifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length)
        (fun index => input.get index)
        (finiteCachedAllBlocksFuel blockVisits) verifier.start =
      .completed := by
  let hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits :=
    fun block => fixedAlphaBlockVisitEntriesInside_of_replayAccepted
      (cachedInputMachine machine) input alpha block
        (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
        (blockVisits block) (haccepted block)
  have hprefix :=
    finiteCachedAllBlocks_inputDrivenCore_prefix_of_replayAccepted
      machine input alpha blockVisits hentries (T / b + 1) le_rfl
        (fun block _ => haccepted block)
  rw [finiteCachedAllBlocksPrefixFuel_all blockVisits] at hprefix
  simpa using hprefix

/-- Exact operational reflection of the total outer core: global completion
at the sum fuel is equivalent to replay acceptance of every advertised fixed
block. -/
theorem finiteCachedAllBlocks_inputDrivenCore_completed_iff_replayAccepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)) :
    let verifier := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
      machine input.length alpha blockVisits
    verifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length)
        (fun index => input.get index)
        (finiteCachedAllBlocksFuel blockVisits) verifier.start =
      .completed ↔
    forall block : Fin (T / b + 1),
      FixedAlphaBlockVisitReplayAccepted
        (cachedInputMachine machine) input alpha block
        (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
        (blockVisits block) := by
  let verifier := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
    machine input.length alpha blockVisits
  let selector : verifier.State -> Option (Fin input.length) :=
    finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length
  let inputBits : Fin input.length -> Bool := fun index => input.get index
  change (verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
      (finiteCachedAllBlocksFuel blockVisits) verifier.start = .completed) ↔ _
  constructor
  · intro hcompleted
    have hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits := by
      by_contra hnotEntries
      have hstart := finiteCachedAllBlocksTotalStart_eq_rejected_of_not_entries
        machine alpha blockVisits hnotEntries
      have hstart' : verifier.start = .rejected := by
        simpa [verifier] using hstart
      have hreject : verifier.inputDrivenCore (fun bit => .bit bit)
          selector inputBits (finiteCachedAllBlocksFuel blockVisits)
          verifier.start = .rejected := by
        rw [hstart']
        exact verifier.inputDrivenCore_eq_self_of_halted
          (fun bit => .bit bit) selector inputBits
            (finiteCachedAllBlocksFuel blockVisits) .rejected rfl
      rw [hreject] at hcompleted
      contradiction
    by_contra hnotAccepted
    have hnotPrefix : ¬ forall block : Fin (T / b + 1),
        block.val < T / b + 1 ->
          FixedAlphaBlockVisitReplayAccepted
            (cachedInputMachine machine) input alpha block
            (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
            (blockVisits block) := by
      intro hall
      apply hnotAccepted
      intro block
      exact hall block block.isLt
    have hreject :=
      finiteCachedAllBlocks_inputDrivenCore_prefix_rejected_of_not_replayAccepted
        machine input alpha blockVisits hentries (T / b + 1) le_rfl
          hnotPrefix
    rw [finiteCachedAllBlocksPrefixFuel_all blockVisits] at hreject
    have hreject' : verifier.inputDrivenCore (fun bit => .bit bit) selector
        inputBits (finiteCachedAllBlocksFuel blockVisits) verifier.start =
          .rejected := by
      simpa [verifier, selector, inputBits] using hreject
    rw [hreject'] at hcompleted
    contradiction
  · intro haccepted
    exact finiteCachedAllBlocks_inputDrivenCore_completed_of_replayAccepted
      machine input alpha blockVisits haccepted

/-- Failure of simultaneous replay acceptance has the complementary exact
operational result: the total outer core is globally rejected. -/
theorem finiteCachedAllBlocks_inputDrivenCore_rejected_of_not_all_replayAccepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hnot : ¬ forall block : Fin (T / b + 1),
      FixedAlphaBlockVisitReplayAccepted
        (cachedInputMachine machine) input alpha block
        (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
        (blockVisits block)) :
    let verifier := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
      machine input.length alpha blockVisits
    verifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length)
        (fun index => input.get index)
        (finiteCachedAllBlocksFuel blockVisits) verifier.start =
      .rejected := by
  let verifier := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
    machine input.length alpha blockVisits
  let selector : verifier.State -> Option (Fin input.length) :=
    finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length
  let inputBits : Fin input.length -> Bool := fun index => input.get index
  change verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
      (finiteCachedAllBlocksFuel blockVisits) verifier.start = .rejected
  by_cases hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits
  · have hnotPrefix : ¬ forall block : Fin (T / b + 1),
        block.val < T / b + 1 ->
          FixedAlphaBlockVisitReplayAccepted
            (cachedInputMachine machine) input alpha block
            (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
            (blockVisits block) := by
      intro hall
      apply hnot
      intro block
      exact hall block block.isLt
    have hreject :=
      finiteCachedAllBlocks_inputDrivenCore_prefix_rejected_of_not_replayAccepted
        machine input alpha blockVisits hentries (T / b + 1) le_rfl
          hnotPrefix
    rw [finiteCachedAllBlocksPrefixFuel_all blockVisits] at hreject
    simpa [verifier, selector, inputBits] using hreject
  · have hstart := finiteCachedAllBlocksTotalStart_eq_rejected_of_not_entries
      machine alpha blockVisits hentries
    have hstart' : verifier.start = .rejected := by
      simpa [verifier] using hstart
    rw [hstart']
    exact verifier.inputDrivenCore_eq_self_of_halted
      (fun bit => .bit bit) selector inputBits
        (finiteCachedAllBlocksFuel blockVisits) .rejected rfl

/-- The advertised sum fuel always reaches one of the two global terminal
states, independently of semantic validity. -/
theorem finiteCachedAllBlocks_inputDrivenCore_halted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)) :
    let verifier := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
      machine input.length alpha blockVisits
    verifier.halted
      (verifier.inputDrivenCore (fun bit => .bit bit)
        (finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length)
        (fun index => input.get index)
        (finiteCachedAllBlocksFuel blockVisits) verifier.start) = true := by
  dsimp only
  by_cases haccepted : forall block : Fin (T / b + 1),
      FixedAlphaBlockVisitReplayAccepted
        (cachedInputMachine machine) input alpha block
        (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
        (blockVisits block)
  · rw [finiteCachedAllBlocks_inputDrivenCore_completed_of_replayAccepted
      machine input alpha blockVisits haccepted]
    rfl
  · rw [finiteCachedAllBlocks_inputDrivenCore_rejected_of_not_all_replayAccepted
      machine input alpha blockVisits haccepted]
    rfl

/-- Compile the finite outer verifier to one adaptive layered query program.
No global read-once claim is made here. -/
def compileAdaptiveFiniteCachedTimedAlphaAllBlocks
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits) :
    LayeredQueryProgram n (finiteCachedAllBlocksFuel blockVisits) :=
  let verifier := finiteCachedTimedAlphaAllBlocksStreamingVerifier
    machine n alpha blockVisits hentries
  verifier.compileAdaptive (finiteCachedAllBlocksFuel blockVisits) n
    (fun bit => .bit bit) .rightEnd
    (finiteCachedAllBlocksAdaptiveQueryIndex? machine n)

/-- Total adaptive outer program.  Unlike the earlier proof-indexed wrapper,
this program is defined for every advertised alpha/list family. -/
def compileAdaptiveFiniteCachedTimedAlphaAllBlocksTotal
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)) :
    LayeredQueryProgram n (finiteCachedAllBlocksFuel blockVisits) :=
  let verifier := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
    machine n alpha blockVisits
  verifier.compileAdaptive (finiteCachedAllBlocksFuel blockVisits) n
    (fun bit => .bit bit) .rightEnd
    (finiteCachedAllBlocksAdaptiveQueryIndex? machine n)

/-- Exact width of the total executable outer program. -/
@[simp]
theorem compileAdaptiveFiniteCachedTimedAlphaAllBlocksTotal_width
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)) :
    (compileAdaptiveFiniteCachedTimedAlphaAllBlocksTotal (n := n) machine
      alpha blockVisits).width =
      @Fintype.card
          (FiniteCachedTimedAlphaAllBlocksStreamingState
            machine alpha blockVisits)
          (cachedAllBlocksStreamingStateFintype machine T b
            (fun block => advertisedBlockWidth alpha.offsets block)
            (fun block => (blockVisits block).length)) *
        (finiteCachedAllBlocksFuel blockVisits + 1) := by
  exact FiniteStreamingVerifier.compileAdaptive_width
    (finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
      machine n alpha blockVisits)
    (finiteCachedAllBlocksFuel blockVisits) n
    (fun bit => .bit bit) .rightEnd
    (finiteCachedAllBlocksAdaptiveQueryIndex? machine n)

/-- Exact operational equation for the total all-block program. -/
theorem compileAdaptiveFiniteCachedTimedAlphaAllBlocksTotal_eval
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (input : Fin n -> Bool) :
    let verifier := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
      machine n alpha blockVisits
    (compileAdaptiveFiniteCachedTimedAlphaAllBlocksTotal machine alpha
      blockVisits).eval input =
      verifier.accept
        (verifier.finishWithEndSymbol .rightEnd
          (verifier.runAdaptive (finiteCachedAllBlocksFuel blockVisits)
            (fun bit => .bit bit)
            (finiteCachedAllBlocksAdaptiveQueryIndex? machine n) input)) := by
  dsimp only
  exact FiniteStreamingVerifier.compileAdaptive_eval
    (finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
      machine n alpha blockVisits)
    (finiteCachedAllBlocksFuel blockVisits) n
    (fun bit => .bit bit) .rightEnd
    (finiteCachedAllBlocksAdaptiveQueryIndex? machine n) input

/-- Accepted fixed-block replays make the total executable outer program
accept on the canonical finite view of the immutable input. -/
theorem compileAdaptiveFiniteCachedTimedAlphaAllBlocksTotal_eval_eq_true_of_acceptedFromBlank
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (haccepted : forall block : Fin (T / b + 1),
      FixedAlphaBlockVisitListAcceptedFromBlank
        (cachedInputMachine machine) input alpha block
        (blockVisits block)) :
    (compileAdaptiveFiniteCachedTimedAlphaAllBlocksTotal
      (n := input.length) machine alpha blockVisits).eval
        (fun index => input.get index) = true := by
  let verifier := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
    machine input.length alpha blockVisits
  let selector : verifier.State -> Option (Fin input.length) :=
    finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length
  let inputBits : Fin input.length -> Bool := fun index => input.get index
  have hcore :=
    finiteCachedAllBlocks_inputDrivenCore_completed_of_acceptedFromBlank
      machine input alpha blockVisits haccepted
  change verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
      (finiteCachedAllBlocksFuel blockVisits) verifier.start =
        .completed at hcore
  have htotal : ∀ state, verifier.requestsInput state = true ->
      ∃ index, selector state = some index := by
    intro state hrequest
    exact finiteCachedAllBlocksAdaptiveQueryIndex?_total_of_requestsInput
      machine input.length state hrequest
  have hrunPhase :
      (verifier.runAdaptive (finiteCachedAllBlocksFuel blockVisits)
        (fun bit => .bit bit) selector inputBits).1 =
      verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
        (finiteCachedAllBlocksFuel blockVisits) verifier.start := by
    simpa [FiniteStreamingVerifier.runAdaptive,
      FiniteStreamingVerifier.initialFueledState] using
        verifier.runAdaptiveFrom_state_eq_inputDrivenCore_of_fuel_le_layers
          (fun bit => .bit bit) selector inputBits htotal
          (verifier.initialFueledState
            (finiteCachedAllBlocksFuel blockVisits))
          (finiteCachedAllBlocksFuel blockVisits) le_rfl
  have hrun :
      (verifier.runAdaptive (finiteCachedAllBlocksFuel blockVisits)
        (fun bit => .bit bit) selector inputBits).1 = .completed :=
    hrunPhase.trans hcore
  have hhalted : verifier.halted
      (verifier.runAdaptive (finiteCachedAllBlocksFuel blockVisits)
        (fun bit => .bit bit) selector inputBits).1 = true := by
    rw [hrun]
    rfl
  have hfinish : verifier.finishWithEndSymbol .rightEnd
      (verifier.runAdaptive (finiteCachedAllBlocksFuel blockVisits)
        (fun bit => .bit bit) selector inputBits) = .completed := by
    calc
      verifier.finishWithEndSymbol .rightEnd
          (verifier.runAdaptive (finiteCachedAllBlocksFuel blockVisits)
            (fun bit => .bit bit) selector inputBits) =
        (verifier.runAdaptive (finiteCachedAllBlocksFuel blockVisits)
          (fun bit => .bit bit) selector inputBits).1 :=
        verifier.finishWithEndSymbol_eq_of_halted .rightEnd _ hhalted
      _ = .completed := hrun
  change (verifier.compileAdaptive (finiteCachedAllBlocksFuel blockVisits)
      input.length (fun bit => .bit bit) .rightEnd selector).eval
        inputBits = true
  rw [FiniteStreamingVerifier.compileAdaptive_eval]
  change finiteCachedAllBlocksAccept
      (verifier.finishWithEndSymbol .rightEnd
        (verifier.runAdaptive (finiteCachedAllBlocksFuel blockVisits)
          (fun bit => .bit bit) selector inputBits)) = true
  rw [hfinish]
  rfl

/-- Full executable reflection of the total finite outer compiler on the
canonical immutable-input view.  The outer program checks exactly simultaneous
fixed-block replay acceptance; chronological ordering remains the schedule
layer's separate responsibility. -/
theorem compileAdaptiveFiniteCachedTimedAlphaAllBlocksTotal_eval_eq_true_iff_replayAccepted
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T)) :
    (compileAdaptiveFiniteCachedTimedAlphaAllBlocksTotal
      (n := input.length) machine alpha blockVisits).eval
        (fun index => input.get index) = true ↔
      forall block : Fin (T / b + 1),
        FixedAlphaBlockVisitReplayAccepted
          (cachedInputMachine machine) input alpha block
          (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
          (blockVisits block) := by
  let verifier := finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier
    machine input.length alpha blockVisits
  let selector : verifier.State -> Option (Fin input.length) :=
    finiteCachedAllBlocksAdaptiveQueryIndex? machine input.length
  let inputBits : Fin input.length -> Bool := fun index => input.get index
  let fuel := finiteCachedAllBlocksFuel blockVisits
  have htotal : ∀ state, verifier.requestsInput state = true ->
      ∃ index, selector state = some index := by
    intro state hrequest
    exact finiteCachedAllBlocksAdaptiveQueryIndex?_total_of_requestsInput
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
      finiteCachedAllBlocks_inputDrivenCore_halted
        machine input alpha blockVisits
  have hrunHalted : verifier.halted
      (verifier.runAdaptive fuel (fun bit => .bit bit) selector inputBits).1 =
        true := by
    rw [hrunPhase]
    exact hcoreHalted
  have hfinish : verifier.finishWithEndSymbol .rightEnd
      (verifier.runAdaptive fuel (fun bit => .bit bit) selector inputBits) =
      (verifier.runAdaptive fuel (fun bit => .bit bit) selector inputBits).1 :=
    verifier.finishWithEndSymbol_eq_of_halted .rightEnd _ hrunHalted
  have hcoreIff :=
    finiteCachedAllBlocks_inputDrivenCore_completed_iff_replayAccepted
      machine input alpha blockVisits
  change (verifier.inputDrivenCore (fun bit => .bit bit) selector inputBits
      fuel verifier.start = .completed ↔ _) at hcoreIff
  change (verifier.compileAdaptive fuel input.length (fun bit => .bit bit)
      .rightEnd selector).eval inputBits = true ↔ _
  rw [FiniteStreamingVerifier.compileAdaptive_eval, hfinish, hrunPhase]
  constructor
  · intro heval
    cases hstate : verifier.inputDrivenCore (fun bit => .bit bit) selector
        inputBits fuel verifier.start with
    | active block phase =>
        rw [hstate] at heval
        simp [verifier,
          finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier,
          finiteCachedAllBlocksAccept] at heval
    | rejected =>
        rw [hstate] at heval
        simp [verifier,
          finiteCachedTimedAlphaAllBlocksTotalStreamingVerifier,
          finiteCachedAllBlocksAccept] at heval
    | completed =>
        exact hcoreIff.1 hstate
  · intro haccepted
    have hcompleted := hcoreIff.2 haccepted
    rw [hcompleted]
    rfl

/-- Exact generic-compiler width equation for the all-block program. -/
@[simp]
theorem compileAdaptiveFiniteCachedTimedAlphaAllBlocks_width
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits) :
    (compileAdaptiveFiniteCachedTimedAlphaAllBlocks (n := n) machine alpha
      blockVisits hentries).width =
      @Fintype.card
          (FiniteCachedTimedAlphaAllBlocksStreamingState
            machine alpha blockVisits)
          (cachedAllBlocksStreamingStateFintype machine T b
            (fun block => advertisedBlockWidth alpha.offsets block)
            (fun block => (blockVisits block).length)) *
        (finiteCachedAllBlocksFuel blockVisits + 1) := by
  exact FiniteStreamingVerifier.compileAdaptive_width
    (finiteCachedTimedAlphaAllBlocksStreamingVerifier
      machine n alpha blockVisits hentries)
    (finiteCachedAllBlocksFuel blockVisits) n
    (fun bit => .bit bit) .rightEnd
    (finiteCachedAllBlocksAdaptiveQueryIndex? machine n)

/-- Exact operational equation for the compiled all-block program. -/
theorem compileAdaptiveFiniteCachedTimedAlphaAllBlocks_eval
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit (cachedInputMachine machine).State T))
    (hentries : FixedAlphaAllBlockVisitEntriesInside alpha blockVisits)
    (input : Fin n -> Bool) :
    let verifier := finiteCachedTimedAlphaAllBlocksStreamingVerifier
      machine n alpha blockVisits hentries
    (compileAdaptiveFiniteCachedTimedAlphaAllBlocks machine alpha blockVisits
      hentries).eval input =
      verifier.accept
        (verifier.finishWithEndSymbol .rightEnd
          (verifier.runAdaptive (finiteCachedAllBlocksFuel blockVisits)
            (fun bit => .bit bit)
            (finiteCachedAllBlocksAdaptiveQueryIndex? machine n) input)) := by
  dsimp only
  exact FiniteStreamingVerifier.compileAdaptive_eval
    (finiteCachedTimedAlphaAllBlocksStreamingVerifier
      machine n alpha blockVisits hentries)
    (finiteCachedAllBlocksFuel blockVisits) n
    (fun bit => .bit bit) .rightEnd
    (finiteCachedAllBlocksAdaptiveQueryIndex? machine n) input

/-- Schedule specialization of the executable outer all-block program. -/
def compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b)) :
    LayeredQueryProgram n
      (finiteCachedAllBlocksFuel
        (fun block => timedAlphaBlockVisits block scheduled)) :=
  compileAdaptiveFiniteCachedTimedAlphaAllBlocksTotal machine alpha
    (fun block => timedAlphaBlockVisits block scheduled)

/-- On a valid schedule, the finite outer compiler exactly reflects the
existing all-block Boolean on the canonical immutable-input view.  Validity
supplies the chronological half omitted by the replay-only outer machine. -/
theorem compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks_eval_eq_allBlockVisitsCheck_of_valid
    (machine : DeterministicMachine) [DecidableEq machine.State]
    [DecidableEq (cachedInputMachine machine).State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hvalid : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha scheduled) :
    (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks
      (n := input.length) machine alpha scheduled).eval
        (fun index => input.get index) =
      timedAlphaAllBlockVisitsCheckFromBlank
        (cachedInputMachine machine) input alpha scheduled := by
  apply Bool.eq_iff_iff.mpr
  unfold compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks
  rw [compileAdaptiveFiniteCachedTimedAlphaAllBlocksTotal_eval_eq_true_iff_replayAccepted]
  rw [timedAlphaAllBlockVisitsCheckFromBlank_eq_true_iff]
  constructor
  · intro hreplay block
    exact ⟨hvalid.blockVisitsChronological
      (cachedInputMachine machine) block, hreplay block⟩
  · intro haccepted block
    exact (haccepted block).2

/-- The one exact reflection premise connecting the new outer program to the
existing executable all-block Boolean.  It intentionally says nothing about
read-once query order between blocks. -/
def FiniteCachedTimedAlphaScheduleAllBlocksReflects
    (machine : DeterministicMachine) [DecidableEq machine.State]
    [DecidableEq (cachedInputMachine machine).State]
    (semanticInput : List Bool) {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (input : Fin n -> Bool) : Prop :=
  (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks machine alpha
      scheduled).eval input =
    timedAlphaAllBlockVisitsCheckFromBlank
      (cachedInputMachine machine) semanticInput alpha scheduled

/-- The formerly external reflection premise is derivable for every valid
schedule on the canonical view of the same immutable input. -/
theorem finiteCachedTimedAlphaScheduleAllBlocksReflects_canonical_of_valid
    (machine : DeterministicMachine) [DecidableEq machine.State]
    [DecidableEq (cachedInputMachine machine).State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hvalid : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha scheduled) :
    FiniteCachedTimedAlphaScheduleAllBlocksReflects machine input alpha
      scheduled (fun index => input.get index) := by
  simpa only [FiniteCachedTimedAlphaScheduleAllBlocksReflects] using
    compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks_eval_eq_allBlockVisitsCheck_of_valid
      machine input alpha scheduled hvalid

/-- Schedule-level executable composition: syntax/schedule check, the finite
outer all-block program, and the rolling two-window flags. -/
def timedAlphaVisitScheduleFiniteOuterInPlaceCheck
    (machine : DeterministicMachine) [DecidableEq machine.State]
    [DecidableEq (cachedInputMachine machine).State]
    (semanticInput : List Bool) {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (input : Fin n -> Bool) : Bool :=
    (timedAlphaVisitScheduleCheck
      (cachedInputMachine machine) alpha scheduled &&
    (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks machine alpha
      scheduled).eval input) &&
    timedAlphaInPlaceTwoWindowFoldCheck
      (cachedInputMachine machine) semanticInput alpha scheduled

/-- Once the outer operational reflection is supplied, the new finite-outer
plus rolling-fold check is extensionally identical to the established
in-place schedule checkpoint. -/
theorem timedAlphaVisitScheduleFiniteOuterInPlaceCheck_eq_existing
    (machine : DeterministicMachine) [DecidableEq machine.State]
    [DecidableEq (cachedInputMachine machine).State]
    (semanticInput : List Bool) {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (input : Fin n -> Bool)
    (hreflect : FiniteCachedTimedAlphaScheduleAllBlocksReflects machine
      semanticInput alpha scheduled input) :
    timedAlphaVisitScheduleFiniteOuterInPlaceCheck machine semanticInput
        alpha scheduled input =
      timedAlphaVisitScheduleInPlaceCanonicalCutCheck
        (cachedInputMachine machine) semanticInput alpha scheduled := by
  have hreflect' :
      (compileAdaptiveFiniteCachedTimedAlphaScheduleAllBlocks machine alpha
          scheduled).eval input =
        timedAlphaAllBlockVisitsCheckFromBlank
          (cachedInputMachine machine) semanticInput alpha scheduled := by
    simpa only [FiniteCachedTimedAlphaScheduleAllBlocksReflects] using hreflect
  unfold timedAlphaVisitScheduleFiniteOuterInPlaceCheck
    timedAlphaVisitScheduleInPlaceCanonicalCutCheck
    timedAlphaVisitScheduleAllBlockVisitsCheck
  rw [hreflect']

/-- On the canonical input view, the finite-outer checkpoint needs no external
reflection premise.  If the schedule is valid, reflection is the theorem
above; if it is invalid, both composite checks reject at their common schedule
gate. -/
theorem timedAlphaVisitScheduleFiniteOuterInPlaceCheck_canonical_eq_existing
    (machine : DeterministicMachine) [DecidableEq machine.State]
    [DecidableEq (cachedInputMachine machine).State]
    (semanticInput : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b)) :
    timedAlphaVisitScheduleFiniteOuterInPlaceCheck machine semanticInput
        alpha scheduled (fun index => semanticInput.get index) =
      timedAlphaVisitScheduleInPlaceCanonicalCutCheck
        (cachedInputMachine machine) semanticInput alpha scheduled := by
  by_cases hscheduleCheck : timedAlphaVisitScheduleCheck
      (cachedInputMachine machine) alpha scheduled = true
  · have hvalid : TimedAlphaVisitScheduleValid
        (cachedInputMachine machine) alpha scheduled :=
      (timedAlphaVisitScheduleCheck_eq_true_iff
        (cachedInputMachine machine) alpha scheduled).1 hscheduleCheck
    exact timedAlphaVisitScheduleFiniteOuterInPlaceCheck_eq_existing
      machine semanticInput alpha scheduled
        (fun index => semanticInput.get index)
        (finiteCachedTimedAlphaScheduleAllBlocksReflects_canonical_of_valid
          machine semanticInput alpha scheduled hvalid)
  · unfold timedAlphaVisitScheduleFiniteOuterInPlaceCheck
      timedAlphaVisitScheduleInPlaceCanonicalCutCheck
      timedAlphaVisitScheduleAllBlockVisitsCheck
    simp [hscheduleCheck]

/-- Consequently the finite-outer composition has the exact canonical-cut
semantics already proved for the rolling checkpoint. -/
theorem timedAlphaVisitScheduleFiniteOuterInPlaceCheck_eq_true_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    [DecidableEq (cachedInputMachine machine).State]
    (semanticInput : List Bool) {n T b : Nat} (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (input : Fin n -> Bool)
    (hreflect : FiniteCachedTimedAlphaScheduleAllBlocksReflects machine
      semanticInput alpha scheduled input) :
    timedAlphaVisitScheduleFiniteOuterInPlaceCheck machine semanticInput
        alpha scheduled input = true ↔
      timedAlphaVisitScheduleAllBlockVisitsCheck
          (cachedInputMachine machine) semanticInput alpha scheduled = true ∧
        alpha.offsets = canonicalCutOffsets
          (cachedInputMachine machine) semanticInput T b hb := by
  rw [timedAlphaVisitScheduleFiniteOuterInPlaceCheck_eq_existing
    machine semanticInput alpha scheduled input hreflect]
  exact timedAlphaVisitScheduleInPlaceCanonicalCutCheck_eq_true_iff
    (cachedInputMachine machine) semanticInput T b hb alpha scheduled

/-- Unconditional canonical-input semantics of the executable finite-outer
plus rolling-fold checkpoint. -/
theorem timedAlphaVisitScheduleFiniteOuterInPlaceCheck_canonical_eq_true_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    [DecidableEq (cachedInputMachine machine).State]
    (semanticInput : List Bool) {T b : Nat} (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b)) :
    timedAlphaVisitScheduleFiniteOuterInPlaceCheck machine semanticInput
        alpha scheduled (fun index => semanticInput.get index) = true ↔
      timedAlphaVisitScheduleAllBlockVisitsCheck
          (cachedInputMachine machine) semanticInput alpha scheduled = true ∧
        alpha.offsets = canonicalCutOffsets
          (cachedInputMachine machine) semanticInput T b hb := by
  rw [timedAlphaVisitScheduleFiniteOuterInPlaceCheck_canonical_eq_existing]
  exact timedAlphaVisitScheduleInPlaceCanonicalCutCheck_eq_true_iff
    (cachedInputMachine machine) semanticInput T b hb alpha scheduled

end OneTapeMagnification
end Frontier
end Pnp4
