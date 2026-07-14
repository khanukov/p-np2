import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.AdaptiveCachedVisitReadOnce
import Pnp4.Frontier.OneTapeMagnification.OnePassFixedAlphaBlockList

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# One finite cached verifier for a fixed-block visit list

The one-visit streaming verifier already keeps only a finite cached control,
bounded heads, and one local work slab.  This file threads that same slab
through an advertised list of visits of one fixed block.  A finite cursor
selects the current visit.  When its local phase completes, one silent
transition checks the advertised endpoint and either installs the completed
slab in the next visit or returns it as the list result.

The executable verifier and its adaptive `LayeredQueryProgram` contain no
actual run.  The later certificate theorem is deliberately separate: it
uses the semantic unread trace only to prove that recursively threading the
finite completed slab is exactly the established visit-list replay relation.
This module does not yet prove read-once for the whole list; that requires a
cross-visit monotonicity invariant for the advertised input endpoints.
-/

/-- Every advertised entry head in a supplied fixed-block list lies in the
block slab.  This is proof-only data used to initialize each finite phase. -/
def FixedAlphaBlockVisitEntriesInside
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (block : Fin (T / b + 1))
    (visits : List (FixedAlphaBlockVisit State T)) : Prop :=
  ∀ visit, visit ∈ visits ->
    WorkCellInSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      visit.entry.workHead.val

/-- Semantic list replay supplies every entry-inside proof required by the
finite list verifier. -/
theorem fixedAlphaBlockVisitEntriesInside_of_replayAccepted
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit machine.State T))
    (haccepted : FixedAlphaBlockVisitReplayAccepted
      machine input alpha block initialSlab visits) :
    FixedAlphaBlockVisitEntriesInside alpha block visits := by
  induction visits generalizing initialSlab with
  | nil =>
      intro visit hmem
      simp at hmem
  | cons visit0 rest ih =>
      rcases haccepted with ⟨hfirst, hrest⟩
      intro visit hmem
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · have hzero := hfirst.1
          ⟨0, FixedAlphaBlockVisit.steps_pos visit⟩
        simpa [fixedAlphaBlockVisitEntryConfiguration] using hzero
      · exact ih
          (fixedAlphaBlockVisitOutputSlab
            machine input alpha block visit0 initialSlab)
          hrest visit hmem

/-- Finite state of the whole fixed-block list verifier.  `active` retains a
finite cursor and exactly one one-visit phase. -/
inductive FiniteCachedBlockVisitListStreamingState
    (State : Type) (H w k : Nat) where
  | active (cursor : Fin k)
      (phase : FiniteCachedVisitStreamingState State H w)
  | completed (slab : WorkSlab w)
  | rejected
deriving Fintype

/-- Explicit Fintype for cached control, avoiding a global instance for the
machine's internal state type. -/
def cachedBlockVisitListStreamingStateFintype
    (machine : DeterministicMachine) (H w k : Nat) :
    Fintype (FiniteCachedBlockVisitListStreamingState
      (cachedInputMachine machine).State H w k) := by
  letI := (cachedInputMachine machine).stateFintype
  exact inferInstance

/-- Product/sum presentation used to expose the exact finite state count. -/
def finiteCachedBlockVisitListStreamingStateEquiv
    (State : Type) (H w k : Nat) :
    FiniteCachedBlockVisitListStreamingState State H w k ≃
      Sum (Fin k × FiniteCachedVisitStreamingState State H w)
        (Sum (WorkSlab w) Unit) where
  toFun
    | .active cursor phase => .inl (cursor, phase)
    | .completed slab => .inr (.inl slab)
    | .rejected => .inr (.inr ())
  invFun
    | .inl fields => .active fields.1 fields.2
    | .inr (.inl slab) => .completed slab
    | .inr (.inr _) => .rejected
  left_inv state := by cases state <;> rfl
  right_inv encoded := by
    rcases encoded with fields | slabOrFailure
    · rfl
    · rcases slabOrFailure with slab | failure
      · rfl
      · cases failure
        rfl

/-- Exact carrier size: one one-visit phase for each finite cursor, one
completed slab, and one global rejection state. -/
theorem card_finiteCachedBlockVisitListStreamingState
    (State : Type) [Fintype State] (H w k : Nat) :
    Fintype.card
        (FiniteCachedBlockVisitListStreamingState State H w k) =
      k * Fintype.card (FiniteCachedVisitStreamingState State H w) +
        2 ^ w + 1 := by
  rw [Fintype.card_congr
    (finiteCachedBlockVisitListStreamingStateEquiv State H w k)]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_unit]
  ring

/-- Initialize one cursor-selected visit from the currently carried slab. -/
def finiteCachedBlockVisitListActiveState
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
    FiniteCachedBlockVisitListStreamingState
      (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block) visits.length :=
  let visit := visits.get cursor
  .active cursor
    (.running (fixedAlphaVisitRemaining visit)
      (finiteCachedStateOfVisitEntry machine alpha block visit carried
        (hentries visit (List.get_mem visits cursor))))

/-- Empty lists return the initial slab.  Nonempty lists start the first
finite cached phase. -/
def finiteCachedBlockVisitListStart
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
    FiniteCachedBlockVisitListStreamingState
      (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block) visits.length :=
  if hnonempty : 0 < visits.length then
    finiteCachedBlockVisitListActiveState machine alpha block visits hentries
      ⟨0, hnonempty⟩ initialSlab
  else
    .completed initialSlab

/-- Only a global completion or rejection halts the list verifier.  A locally
completed visit still needs one silent carry/endpoint transition. -/
def finiteCachedBlockVisitListHalted
    {State : Type} {H w k : Nat} :
    FiniteCachedBlockVisitListStreamingState State H w k -> Bool
  | .active _ _ => false
  | .completed _ => true
  | .rejected => true

/-- Fresh-input requests are delegated exactly to the active one-visit
phase. -/
def finiteCachedBlockVisitListRequestsInput
    (machine : DeterministicMachine) (n : Nat)
    {T w k : Nat} :
    FiniteCachedBlockVisitListStreamingState
        (cachedInputMachine machine).State T w k -> Bool
  | .active _ phase =>
      finiteCachedVisitPhaseRequestsInput machine n phase
  | .completed _ => false
  | .rejected => false

/-- Lift a one-visit transition back under the same list cursor, collapsing
its explicit local failure to the list failure state. -/
def liftFiniteCachedBlockVisitPhase
    {State : Type} {H w k : Nat} (cursor : Fin k) :
    FiniteCachedVisitStreamingState State H w ->
      FiniteCachedBlockVisitListStreamingState State H w k
  | .rejected _ => .rejected
  | phase => .active cursor phase

/-- One executable transition of the fixed-block visit-list verifier.

Running phases delegate to the one-visit transition.  A completed phase
accepts only on exact advertised endpoint equality; its slab is then carried
to the next advertised visit, or returned when the cursor is last. -/
def finiteCachedBlockVisitListStreamingStep
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits) :
    FiniteCachedBlockVisitListStreamingState
        (cachedInputMachine machine).State T
        (advertisedBlockWidth alpha.offsets block) visits.length ->
      Option ReadOnlySymbol ->
      FiniteCachedBlockVisitListStreamingState
        (cachedInputMachine machine).State T
        (advertisedBlockWidth alpha.offsets block) visits.length
  | .completed slab, _ => .completed slab
  | .rejected, _ => .rejected
  | .active _ (.rejected _), _ => .rejected
  | .active cursor phase@(.running _ _), supplied =>
      liftFiniteCachedBlockVisitPhase cursor
        (finiteCachedVisitStreamingStep machine n T
          (advertisedBlockWidth alpha.offsets block)
          (advertisedBlockLower alpha.offsets block)
          (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
          phase supplied)
  | .active cursor phase@(.completed final), supplied =>
      if @finiteCachedVisitPhaseAccept
          (cachedInputMachine machine).State
          (cachedInputStateDecidableEq machine) T
          (advertisedBlockWidth alpha.offsets block)
          (visits.get cursor).exit phase then
        match supplied with
        | some _ => .rejected
        | none =>
            if hnext : cursor.val + 1 < visits.length then
              finiteCachedBlockVisitListActiveState machine alpha block
                visits hentries ⟨cursor.val + 1, hnext⟩ final.workSlab
            else
              .completed final.workSlab
      else
        .rejected

/-- A running list phase delegates definitionally to exactly one one-visit
streaming transition under the same cursor. -/
theorem finiteCachedBlockVisitListStreamingStep_active_running
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (cursor : Fin visits.length)
    (remaining : Fin (T + 1))
    (live : LocalReplayState (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block))
    (supplied : Option ReadOnlySymbol) :
    finiteCachedBlockVisitListStreamingStep machine n alpha block visits
        hentries (.active cursor (.running remaining live)) supplied =
      liftFiniteCachedBlockVisitPhase cursor
        (finiteCachedVisitStreamingStep machine n T
          (advertisedBlockWidth alpha.offsets block)
          (advertisedBlockLower alpha.offsets block)
          (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
          (.running remaining live) supplied) :=
  rfl

/-- Exact successful carry boundary: after endpoint equality, one silent step
installs the completed slab in the next advertised visit. -/
theorem finiteCachedBlockVisitListStreamingStep_completed_next
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (cursor : Fin visits.length)
    (final : FiniteLocalFinalState (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block))
    (haccept : @finiteCachedVisitPhaseAccept
      (cachedInputMachine machine).State
      (cachedInputStateDecidableEq machine) T
      (advertisedBlockWidth alpha.offsets block)
      (visits.get cursor).exit (.completed final) = true)
    (hnext : cursor.val + 1 < visits.length) :
    finiteCachedBlockVisitListStreamingStep machine n alpha block visits
        hentries (.active cursor (.completed final)) none =
      finiteCachedBlockVisitListActiveState machine alpha block visits
        hentries ⟨cursor.val + 1, hnext⟩ final.workSlab := by
  have haccept' : @finiteCachedVisitPhaseAccept
      (cachedInputMachine machine).State
      (cachedInputStateDecidableEq machine) T
      (advertisedBlockWidth alpha.offsets block)
      visits[cursor.val].exit (.completed final) = true := by
    simpa [List.get_eq_getElem] using haccept
  simp [finiteCachedBlockVisitListStreamingStep, haccept', hnext]

/-- Exact final boundary: after the last endpoint check, one silent step
returns the finite carried slab as the global list result. -/
theorem finiteCachedBlockVisitListStreamingStep_completed_last
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (cursor : Fin visits.length)
    (final : FiniteLocalFinalState (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block))
    (haccept : @finiteCachedVisitPhaseAccept
      (cachedInputMachine machine).State
      (cachedInputStateDecidableEq machine) T
      (advertisedBlockWidth alpha.offsets block)
      (visits.get cursor).exit (.completed final) = true)
    (hlast : ¬ cursor.val + 1 < visits.length) :
    finiteCachedBlockVisitListStreamingStep machine n alpha block visits
        hentries (.active cursor (.completed final)) none =
      .completed final.workSlab := by
  have haccept' : @finiteCachedVisitPhaseAccept
      (cachedInputMachine machine).State
      (cachedInputStateDecidableEq machine) T
      (advertisedBlockWidth alpha.offsets block)
      visits[cursor.val].exit (.completed final) = true := by
    simpa [List.get_eq_getElem] using haccept
  simp [finiteCachedBlockVisitListStreamingStep, haccept', hlast]

/-- A supplied symbol at an already completed local phase is always rejected;
carry transitions are necessarily silent. -/
theorem finiteCachedBlockVisitListStreamingStep_completed_some
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits)
    (cursor : Fin visits.length)
    (final : FiniteLocalFinalState (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block))
    (symbol : ReadOnlySymbol) :
    finiteCachedBlockVisitListStreamingStep machine n alpha block visits
        hentries (.active cursor (.completed final)) (some symbol) =
      .rejected := by
  simp [finiteCachedBlockVisitListStreamingStep]

/-- A list accepts exactly in its global completed state.  Endpoint matching
has already been checked by the silent carry transitions. -/
def finiteCachedBlockVisitListAccept
    {State : Type} {H w k : Nat} :
    FiniteCachedBlockVisitListStreamingState State H w k -> Bool
  | .completed _ => true
  | _ => false

/-- One finite streaming verifier for every visit of one advertised block. -/
def finiteCachedFixedAlphaBlockVisitListStreamingVerifier
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits) :
    FiniteStreamingVerifier ReadOnlySymbol where
  State := FiniteCachedBlockVisitListStreamingState
    (cachedInputMachine machine).State T
    (advertisedBlockWidth alpha.offsets block) visits.length
  stateFintype := cachedBlockVisitListStreamingStateFintype machine T
    (advertisedBlockWidth alpha.offsets block) visits.length
  start := finiteCachedBlockVisitListStart machine alpha block initialSlab
    visits hentries
  halted := finiteCachedBlockVisitListHalted
  requestsInput := finiteCachedBlockVisitListRequestsInput machine n
  step := finiteCachedBlockVisitListStreamingStep machine n alpha block visits
    hentries
  accept := finiteCachedBlockVisitListAccept

/-- State-dependent input coordinate exposed by the active cached phase. -/
def finiteCachedBlockVisitListAdaptiveQueryIndex?
    (machine : DeterministicMachine) (n : Nat)
    {T w k : Nat} :
    FiniteCachedBlockVisitListStreamingState
        (cachedInputMachine machine).State T w k -> Option (Fin n)
  | .active _ phase =>
      finiteCachedVisitAdaptiveQueryIndex? machine n phase
  | .completed _ => none
  | .rejected => none

/-- Exact transition fuel: one unit for every advertised machine transition
and one silent endpoint/carry transition for every visit. -/
def finiteCachedBlockVisitListFuel
    {State : Type} {T : Nat}
    (visits : List (FixedAlphaBlockVisit State T)) : Nat :=
  fixedAlphaBlockVisitsTotalSteps visits + visits.length

/-- Positive visit durations bound the number of phase boundaries by the
number of advertised machine transitions. -/
theorem fixedAlphaBlockVisits_length_le_totalSteps
    {State : Type} {T : Nat}
    (visits : List (FixedAlphaBlockVisit State T)) :
    visits.length ≤ fixedAlphaBlockVisitsTotalSteps visits := by
  induction visits with
  | nil => simp [fixedAlphaBlockVisitsTotalSteps]
  | cons visit rest ih =>
      simp only [List.length_cons, fixedAlphaBlockVisitsTotalSteps]
      have hpositive := FixedAlphaBlockVisit.steps_pos visit
      omega

/-- A chronological list therefore needs at most `2*T` total verifier fuel,
including every endpoint/carry transition. -/
theorem finiteCachedBlockVisitListFuel_le_two_mul_horizon
    {State : Type} {T : Nat}
    (visits : List (FixedAlphaBlockVisit State T))
    (hchronological : FixedAlphaBlockVisitsChronological visits) :
    finiteCachedBlockVisitListFuel visits ≤ 2 * T := by
  have hsteps := fixedAlphaBlockVisitsTotalSteps_le_horizon
    visits hchronological
  have hlength := fixedAlphaBlockVisits_length_le_totalSteps visits
  unfold finiteCachedBlockVisitListFuel
  omega

/-- Valid timed schedules give the same `2*T` fuel bound for every stable
fixed-block sublist. -/
theorem TimedAlphaVisitScheduleValid.blockVisitListFuel_le_two_mul_horizon
    (machine : DeterministicMachine)
    {T b : Nat}
    {alpha : AmbientTimedCanonicalAlpha machine.State T b}
    {scheduled : List (TimedAlphaScheduledVisit machine.State T b)}
    (hvalid : TimedAlphaVisitScheduleValid machine alpha scheduled)
    (block : Fin (T / b + 1)) :
    finiteCachedBlockVisitListFuel
        (timedAlphaBlockVisits block scheduled) ≤ 2 * T := by
  exact finiteCachedBlockVisitListFuel_le_two_mul_horizon
    (timedAlphaBlockVisits block scheduled)
    (hvalid.blockVisitsChronological machine block)

/-- Compile the single list verifier to one adaptive layered query program.
The remaining read-once obligation is cross-visit query monotonicity. -/
def compileAdaptiveFiniteCachedFixedAlphaBlockVisitList
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits) :
    LayeredQueryProgram n (finiteCachedBlockVisitListFuel visits) :=
  let verifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
    machine n alpha block initialSlab visits hentries
  verifier.compileAdaptive (finiteCachedBlockVisitListFuel visits) n
    (fun bit => .bit bit) .rightEnd
    (finiteCachedBlockVisitListAdaptiveQueryIndex? machine n)

/-- Exact width equation for the executable multi-visit program. -/
@[simp]
theorem compileAdaptiveFiniteCachedFixedAlphaBlockVisitList_width
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits) :
    (compileAdaptiveFiniteCachedFixedAlphaBlockVisitList (n := n) machine
      alpha block initialSlab visits hentries).width =
      @Fintype.card
          (FiniteCachedBlockVisitListStreamingState
            (cachedInputMachine machine).State T
            (advertisedBlockWidth alpha.offsets block) visits.length)
          (cachedBlockVisitListStreamingStateFintype machine T
            (advertisedBlockWidth alpha.offsets block) visits.length) *
        (finiteCachedBlockVisitListFuel visits + 1) := by
  exact FiniteStreamingVerifier.compileAdaptive_width
    (finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine n alpha
      block initialSlab visits hentries)
    (finiteCachedBlockVisitListFuel visits) n
    (fun bit => .bit bit) .rightEnd
    (finiteCachedBlockVisitListAdaptiveQueryIndex? machine n)

/-- Closed form of the multi-visit program width.  Relative to the one-visit
carrier, list composition costs exactly a cursor factor plus one retained
slab and one rejecting state. -/
theorem compileAdaptiveFiniteCachedFixedAlphaBlockVisitList_width_eq
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T))
    (hentries : FixedAlphaBlockVisitEntriesInside alpha block visits) :
    (compileAdaptiveFiniteCachedFixedAlphaBlockVisitList (n := n) machine
      alpha block initialSlab visits hentries).width =
      (visits.length *
          @Fintype.card
            (FiniteCachedVisitStreamingState
              (cachedInputMachine machine).State T
              (advertisedBlockWidth alpha.offsets block))
            (cachedFiniteVisitStreamingStateFintype machine T
              (advertisedBlockWidth alpha.offsets block)) +
        2 ^ advertisedBlockWidth alpha.offsets block + 1) *
          (finiteCachedBlockVisitListFuel visits + 1) := by
  rw [compileAdaptiveFiniteCachedFixedAlphaBlockVisitList_width]
  rw [@card_finiteCachedBlockVisitListStreamingState
    (cachedInputMachine machine).State
    (cachedInputMachine machine).stateFintype T
    (advertisedBlockWidth alpha.offsets block) visits.length]

/-- Exact operational equation for the compiled list program.  The right
side is one adaptive execution of the finite list verifier followed by its
end-marker closure. -/
theorem compileAdaptiveFiniteCachedFixedAlphaBlockVisitList_eval
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
    (input : Fin n -> Bool) :
    let verifier := finiteCachedFixedAlphaBlockVisitListStreamingVerifier
      machine n alpha block initialSlab visits hentries
    (compileAdaptiveFiniteCachedFixedAlphaBlockVisitList machine alpha block
      initialSlab visits hentries).eval input =
      verifier.accept
        (verifier.finishWithEndSymbol .rightEnd
          (verifier.runAdaptive (finiteCachedBlockVisitListFuel visits)
            (fun bit => .bit bit)
            (finiteCachedBlockVisitListAdaptiveQueryIndex? machine n)
            input)) := by
  dsimp only
  exact FiniteStreamingVerifier.compileAdaptive_eval
    (finiteCachedFixedAlphaBlockVisitListStreamingVerifier machine n alpha
      block initialSlab visits hentries)
    (finiteCachedBlockVisitListFuel visits) n
    (fun bit => .bit bit) .rightEnd
    (finiteCachedBlockVisitListAdaptiveQueryIndex? machine n) input

/-- The precise remaining query-order premise for the multi-visit program.
Once cross-visit freshness proves strict increase, the generic adaptive
compiler immediately yields read-once. -/
theorem compileAdaptiveFiniteCachedFixedAlphaBlockVisitList_isReadOnce_of_fresh
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
    (hfresh : FiniteStreamingVerifier.FreshQueriesStrictlyIncrease
      (compileAdaptiveFiniteCachedFixedAlphaBlockVisitList (n := n) machine
        alpha block initialSlab visits hentries)) :
    (compileAdaptiveFiniteCachedFixedAlphaBlockVisitList (n := n) machine
      alpha block initialSlab visits hentries).IsReadOnce := by
  exact FiniteStreamingVerifier.isReadOnce_of_freshQueriesStrictlyIncrease
    _ hfresh

/-- A finite completed streaming phase exposes the exact slab carried by the
old semantic visit replay.  This is the key carry lemma needed at a list
boundary. -/
theorem finiteCachedFixedAlphaVisitStreaming_completed_outputSlab
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat}
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
    (hagree : FiniteCachedVisitSymbolsAgree machine input T
      (advertisedBlockWidth alpha.offsets block)
      (advertisedBlockLower alpha.offsets block)
      (cachedRunUnreadSymbols machine input
        (fixedAlphaBlockVisitEntryConfiguration
          alpha block visit carried) visit.steps)
      (finiteCachedStateOfVisitEntry machine alpha block visit carried
        hentry))
    (hstream : runFiniteCachedVisitStreamingWithUnreads machine input.length T
      (advertisedBlockWidth alpha.offsets block)
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
      (cachedRunUnreadSymbols machine input
        (fixedAlphaBlockVisitEntryConfiguration
          alpha block visit carried) visit.steps)
      (.running (fixedAlphaVisitRemaining visit)
        (finiteCachedStateOfVisitEntry machine alpha block visit carried
          hentry)) = .completed final)
    (hendpoint : visit.exit.state = final.control ∧
      visit.exit.inputHead = final.inputHead ∧
      visit.exit.workHead = final.workHead) :
    final.workSlab = fixedAlphaBlockVisitOutputSlab
      (cachedInputMachine machine) input alpha block visit carried := by
  let base := advertisedBlockLower alpha.offsets block
  let width := advertisedBlockWidth alpha.offsets block
  let unreads := cachedRunUnreadSymbols machine input
    (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
    visit.steps
  let initial := finiteCachedStateOfVisitEntry
    machine alpha block visit carried hentry
  have hrespect : FiniteCachedVisitUnreadsRespectEnd machine input.length
      T width base unreads initial := by
    exact finiteCachedVisitSymbolsAgree_implies_respectEnd
      machine input unreads initial (by
        simpa [base, width, unreads, initial] using hagree)
  have hlength : (fixedAlphaVisitRemaining visit).val = unreads.length := by
    simp [fixedAlphaVisitRemaining, unreads]
  have hrun := runFiniteCachedVisitStreamingWithUnreads_eq_replay
    machine input.length
    (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
    unreads (fixedAlphaVisitRemaining visit) initial
    (by
      apply List.ne_nil_of_length_pos
      simp [unreads, FixedAlphaBlockVisit.steps_pos])
    hlength hrespect
  have hmapped : streamingStateOfFiniteReplayResult
      (finiteCachedVisitReplay machine T width base
        (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
        unreads initial) = .completed final := by
    exact hrun.symm.trans (by
      simpa [base, width, unreads, initial] using hstream)
  have hreplay : finiteCachedVisitReplay machine T width base
      (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
      unreads initial = .completed final := by
    cases hresult : finiteCachedVisitReplay machine T width base
        (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
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
  have hreplayFixed : finiteCachedFixedAlphaBlockVisitReplay machine alpha
      block visit carried hentry unreads = .completed final := by
    simpa [finiteCachedFixedAlphaBlockVisitReplay, base, width, initial]
      using hreplay
  exact (finiteCachedFixedAlphaBlockVisitReplay_completed_sound
    machine input alpha block visit carried hentry unreads final
    (by simp [unreads])
    (by simpa [base, width, unreads, initial] using hagree)
    hreplayFixed hendpoint).2

/-- One completed finite phase certificate with its final slab kept explicit,
so a recursive list certificate can install that slab in the next visit. -/
def FiniteCachedFixedAlphaVisitStreamingStepCertificate
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (final : FiniteLocalFinalState (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block)) : Prop :=
  ∃ hentry : WorkCellInSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      visit.entry.workHead.val,
    FiniteCachedVisitSymbolsAgree machine input T
        (advertisedBlockWidth alpha.offsets block)
        (advertisedBlockLower alpha.offsets block)
        (cachedRunUnreadSymbols machine input
          (fixedAlphaBlockVisitEntryConfiguration
            alpha block visit carried) visit.steps)
        (finiteCachedStateOfVisitEntry machine alpha block visit carried
          hentry) ∧
      runFiniteCachedVisitStreamingWithUnreads machine input.length T
          (advertisedBlockWidth alpha.offsets block)
          (advertisedBlockLower alpha.offsets block)
          (advertisedBlockLower_add_width_le_horizon alpha.offsets block)
          (cachedRunUnreadSymbols machine input
            (fixedAlphaBlockVisitEntryConfiguration
              alpha block visit carried) visit.steps)
          (.running (fixedAlphaVisitRemaining visit)
            (finiteCachedStateOfVisitEntry machine alpha block visit carried
              hentry)) = .completed final ∧
        visit.exit.state = final.control ∧
          visit.exit.inputHead = final.inputHead ∧
          visit.exit.workHead = final.workHead

/-- Existentially hiding the final finite slab recovers exactly the existing
one-visit semantic validity relation. -/
theorem exists_finiteCachedFixedAlphaVisitStreamingStepCertificate_iff
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block)) :
    (∃ final, FiniteCachedFixedAlphaVisitStreamingStepCertificate
        machine input alpha block visit carried final) ↔
      FixedAlphaBlockVisitValid (cachedInputMachine machine) input alpha block
        visit carried := by
  rw [← finiteCachedFixedAlphaVisitStreamingCertificate_iff
    machine input alpha block visit carried]
  constructor
  · rintro ⟨final, hentry, hagree, hstream,
      hstate, hinput, hwork⟩
    exact ⟨hentry, final, hagree, hstream, hstate, hinput, hwork⟩
  · rintro ⟨hentry, final, hagree, hstream,
      hstate, hinput, hwork⟩
    exact ⟨final, hentry, hagree, hstream, hstate, hinput, hwork⟩

/-- The final slab named by a step certificate is the exact semantic output
slab, not merely an arbitrary carry witness. -/
theorem FiniteCachedFixedAlphaVisitStreamingStepCertificate.outputSlab_eq
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (final : FiniteLocalFinalState (cachedInputMachine machine).State T
      (advertisedBlockWidth alpha.offsets block))
    (hcertificate : FiniteCachedFixedAlphaVisitStreamingStepCertificate
      machine input alpha block visit carried final) :
    final.workSlab = fixedAlphaBlockVisitOutputSlab
      (cachedInputMachine machine) input alpha block visit carried := by
  rcases hcertificate with
    ⟨hentry, hagree, hstream, hstate, hinput, hwork⟩
  exact finiteCachedFixedAlphaVisitStreaming_completed_outputSlab
    machine input alpha block visit carried hentry final hagree hstream
    ⟨hstate, hinput, hwork⟩

/-- Recursive finite streaming certificate for the whole fixed-block list.
The only tail carry is the completed finite slab returned by the previous
phase. -/
def FiniteCachedFixedAlphaBlockVisitListStreamingCertificate
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1)) :
    WorkSlab (advertisedBlockWidth alpha.offsets block) ->
      List (FixedAlphaBlockVisit
        (cachedInputMachine machine).State T) -> Prop
  | _, [] => True
  | carried, visit :: rest =>
      ∃ final,
        FiniteCachedFixedAlphaVisitStreamingStepCertificate
            machine input alpha block visit carried final ∧
          FiniteCachedFixedAlphaBlockVisitListStreamingCertificate
            machine input alpha block final.workSlab rest

/-- Exact list-level carry theorem: recursively composing the finite cached
streaming phases is equivalent to the established slab-threaded semantic
replay for every supplied visit list. -/
theorem finiteCachedFixedAlphaBlockVisitListStreamingCertificate_iff
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)) :
    FiniteCachedFixedAlphaBlockVisitListStreamingCertificate
        machine input alpha block initialSlab visits ↔
      FixedAlphaBlockVisitReplayAccepted
        (cachedInputMachine machine) input alpha block initialSlab visits := by
  induction visits generalizing initialSlab with
  | nil =>
      simp [FiniteCachedFixedAlphaBlockVisitListStreamingCertificate,
        FixedAlphaBlockVisitReplayAccepted]
  | cons visit rest ih =>
      rw [FiniteCachedFixedAlphaBlockVisitListStreamingCertificate,
        FixedAlphaBlockVisitReplayAccepted]
      constructor
      · rintro ⟨final, hstep, htail⟩
        have hvalid :=
          (exists_finiteCachedFixedAlphaVisitStreamingStepCertificate_iff
            machine input alpha block visit initialSlab).mp
            ⟨final, hstep⟩
        have hslab := hstep.outputSlab_eq
          machine input alpha block visit initialSlab final
        refine ⟨hvalid, ?_⟩
        rw [← hslab]
        exact (ih final.workSlab).mp htail
      · rintro ⟨hvalid, htail⟩
        obtain ⟨final, hstep⟩ :=
          (exists_finiteCachedFixedAlphaVisitStreamingStepCertificate_iff
            machine input alpha block visit initialSlab).mpr hvalid
        refine ⟨final, hstep, ?_⟩
        apply (ih final.workSlab).mpr
        rw [hstep.outputSlab_eq
          machine input alpha block visit initialSlab final]
        exact htail

/-- Public list certificate: chronological separation plus the recursively
slab-threaded finite streaming phases. -/
def FiniteCachedFixedAlphaBlockVisitListStreamingAcceptedCertificate
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)) : Prop :=
  FixedAlphaBlockVisitsChronological visits ∧
    FiniteCachedFixedAlphaBlockVisitListStreamingCertificate
      machine input alpha block initialSlab visits

/-- Exact correspondence with the established public fixed-block list
acceptance predicate. -/
theorem finiteCachedFixedAlphaBlockVisitListStreamingAcceptedCertificate_iff
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)) :
    FiniteCachedFixedAlphaBlockVisitListStreamingAcceptedCertificate
        machine input alpha block initialSlab visits ↔
      FixedAlphaBlockVisitListAccepted
        (cachedInputMachine machine) input alpha block initialSlab visits := by
  unfold FiniteCachedFixedAlphaBlockVisitListStreamingAcceptedCertificate
    FixedAlphaBlockVisitListAccepted
  rw [finiteCachedFixedAlphaBlockVisitListStreamingCertificate_iff]

/-- Blank-slab specialization used by the timed-alpha component checker. -/
theorem finiteCachedFixedAlphaBlockVisitListStreamingFromBlank_iff
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (block : Fin (T / b + 1))
    (visits : List (FixedAlphaBlockVisit
      (cachedInputMachine machine).State T)) :
    FiniteCachedFixedAlphaBlockVisitListStreamingAcceptedCertificate
        machine input alpha block
        (blankWorkSlab (advertisedBlockWidth alpha.offsets block)) visits ↔
      FixedAlphaBlockVisitListAcceptedFromBlank
        (cachedInputMachine machine) input alpha block visits := by
  exact finiteCachedFixedAlphaBlockVisitListStreamingAcceptedCertificate_iff
    machine input alpha block
      (blankWorkSlab (advertisedBlockWidth alpha.offsets block)) visits

end OneTapeMagnification
end Frontier
end Pnp4
