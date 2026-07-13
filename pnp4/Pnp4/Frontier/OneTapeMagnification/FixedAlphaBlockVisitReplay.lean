import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.AdvertisedCutBlockSlabs
import Pnp4.Frontier.OneTapeMagnification.TimedCanonicalAlpha

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Replay of one advertised block's visits for a fixed timed alpha

An ambient timed alpha fixes advertised cut offsets, hence the finite slab of
each advertised block.  This file supplies the next validator-side layer.  A
visit carries a strict advertised time interval and bounded entry/exit
metadata.  At its entry, one finite slab valuation is materialized as a full
configuration by putting `false` outside the slab.  The deterministic machine
is then run for the advertised duration.

A visit is locally valid exactly when every pre-transition work head of this
materialized run remains in the advertised slab and the final control state
and both heads equal the advertised exit metadata.  The resulting slab
restriction is the sole value carried to the next advertised visit of the
same block.  The recursive checker therefore uses one `WorkSlab`, not a full
work tape, across an arbitrary fixed list of visits.

The main replay theorem is independent of an actual-run group decomposition:
every concrete entry configuration agreeing with the advertised entry on the
visible local interface has an exit agreeing with the validator's advertised
exit and carried slab.  Blank initialization is explicit.

This module deliberately does **not** derive the visit list from the padded
timed word, prove that the word is prefix-shaped or chronologically coherent,
check crossing directions/payloads, check cut minimality, or construct the
global composition across different blocks.  Those remain validator
obligations; arbitrary ambient alpha values may still be rejected.
-/

/-- A finite slab filled entirely with the blank work-tape symbol. -/
def blankWorkSlab (width : Nat) : WorkSlab width :=
  fun _ => false

/-- Slab membership is an arithmetic, hence decidable, predicate. -/
instance instDecidableWorkCellInSlab (base width cell : Nat) :
    Decidable (WorkCellInSlab base width cell) := by
  unfold WorkCellInSlab
  infer_instance

/-- Extend one finite slab to a complete work tape, using blank cells outside
the advertised half-open interval. -/
def workTapeOfWorkSlab (base : Nat) {width : Nat}
    (slab : WorkSlab width) : WorkTape :=
  fun cell =>
    if hcell : WorkCellInSlab base width cell then
      slab (workCellIndex hcell)
    else false

/-- Restricting the blank work tape gives the blank finite slab. -/
@[simp]
theorem restrictWorkSlab_blank (base width : Nat) :
    restrictWorkSlab base width WorkTape.blank = blankWorkSlab width := by
  rfl

/-- Extending a blank finite slab with blank cells is the globally blank work
tape, independently of the slab position. -/
@[simp]
theorem workTapeOfWorkSlab_blank (base width : Nat) :
    workTapeOfWorkSlab base (blankWorkSlab width) = WorkTape.blank := by
  funext cell
  by_cases hcell : WorkCellInSlab base width cell
  · simp [workTapeOfWorkSlab, hcell, blankWorkSlab, WorkTape.blank]
  · simp [workTapeOfWorkSlab, hcell, WorkTape.blank]

/-- Materialization is a right inverse to slab restriction. -/
@[simp]
theorem restrictWorkSlab_workTapeOfWorkSlab
    (base : Nat) {width : Nat} (slab : WorkSlab width) :
    restrictWorkSlab base width (workTapeOfWorkSlab base slab) = slab := by
  funext i
  have hcell : WorkCellInSlab base width (workSlabCell base i) := by
    unfold WorkCellInSlab workSlabCell
    constructor <;> omega
  simp only [restrictWorkSlab, workTapeOfWorkSlab]
  rw [dif_pos hcell]
  congr 1
  apply Fin.ext
  simp only [workCellIndex, workSlabCell]
  omega

/-- The bounded state-and-head interface advertised at a visit endpoint.

This reuses the finite shape already counted by `TimedCanonicalAlpha`; despite
the original name, the same three fields are also suitable at intermediate
visit endpoints. -/
abbrev FixedAlphaVisitEndpoint (State : Type) (T : Nat) :=
  BoundedTerminalEndpoint State T

/-- The blank-start endpoint advertised at time zero. -/
def initialFixedAlphaVisitEndpoint
    (machine : DeterministicMachine) (T : Nat) :
    FixedAlphaVisitEndpoint machine.State T :=
  { state := machine.startState
    inputHead := ⟨0, by omega⟩
    workHead := ⟨0, by omega⟩ }

/-- Materialize bounded endpoint metadata together with one finite slab.  No
information about the work tape outside that slab is retained. -/
def configurationOfFixedAlphaEndpoint
    {State : Type} {T : Nat} (base : Nat) {width : Nat}
    (endpoint : FixedAlphaVisitEndpoint State T)
    (slab : WorkSlab width) : Configuration State :=
  { state := endpoint.state
    inputHead := endpoint.inputHead.val
    workHead := endpoint.workHead.val
    workTape := workTapeOfWorkSlab base slab }

@[simp]
theorem configurationOfFixedAlphaEndpoint_state
    {State : Type} {T : Nat} (base : Nat) {width : Nat}
    (endpoint : FixedAlphaVisitEndpoint State T)
    (slab : WorkSlab width) :
    (configurationOfFixedAlphaEndpoint base endpoint slab).state =
      endpoint.state :=
  rfl

@[simp]
theorem configurationOfFixedAlphaEndpoint_inputHead
    {State : Type} {T : Nat} (base : Nat) {width : Nat}
    (endpoint : FixedAlphaVisitEndpoint State T)
    (slab : WorkSlab width) :
    (configurationOfFixedAlphaEndpoint base endpoint slab).inputHead =
      endpoint.inputHead.val :=
  rfl

@[simp]
theorem configurationOfFixedAlphaEndpoint_workHead
    {State : Type} {T : Nat} (base : Nat) {width : Nat}
    (endpoint : FixedAlphaVisitEndpoint State T)
    (slab : WorkSlab width) :
    (configurationOfFixedAlphaEndpoint base endpoint slab).workHead =
      endpoint.workHead.val :=
  rfl

@[simp]
theorem configurationOfFixedAlphaEndpoint_restrictWorkSlab
    {State : Type} {T : Nat} (base : Nat) {width : Nat}
    (endpoint : FixedAlphaVisitEndpoint State T)
    (slab : WorkSlab width) :
    restrictWorkSlab base width
        (configurationOfFixedAlphaEndpoint base endpoint slab).workTape =
      slab := by
  exact restrictWorkSlab_workTapeOfWorkSlab base slab

/-- Blank materialization of the blank-start endpoint is exactly the ordinary
initial configuration. -/
@[simp]
theorem configurationOfFixedAlphaEndpoint_initial_blank
    (machine : DeterministicMachine) (T base width : Nat) :
    configurationOfFixedAlphaEndpoint base
        (initialFixedAlphaVisitEndpoint machine T) (blankWorkSlab width) =
      initialConfiguration machine := by
  unfold configurationOfFixedAlphaEndpoint
    initialFixedAlphaVisitEndpoint initialConfiguration
  rw [workTapeOfWorkSlab_blank]

/-- A configuration realizes advertised endpoint metadata when its control
state and both head positions are exactly the advertised fields. -/
def ConfigurationMatchesFixedAlphaEndpoint
    {State : Type} {T : Nat}
    (endpoint : FixedAlphaVisitEndpoint State T)
    (config : Configuration State) : Prop :=
  endpoint.state = config.state ∧
    endpoint.inputHead.val = config.inputHead ∧
    endpoint.workHead.val = config.workHead

/-- One nonempty advertised visit of a fixed block.  Absolute times are kept
so a later layer can connect the visit to the timed crossing word; the local
replay uses their exact difference. -/
structure FixedAlphaBlockVisit (State : Type) (T : Nat) where
  entryTime : Fin (T + 1)
  exitTime : Fin (T + 1)
  entryTime_lt_exitTime : entryTime < exitTime
  entry : FixedAlphaVisitEndpoint State T
  exit : FixedAlphaVisitEndpoint State T

/-- Number of transitions advertised for one visit. -/
def FixedAlphaBlockVisit.steps
    {State : Type} {T : Nat} (visit : FixedAlphaBlockVisit State T) : Nat :=
  visit.exitTime.val - visit.entryTime.val

theorem FixedAlphaBlockVisit.steps_pos
    {State : Type} {T : Nat} (visit : FixedAlphaBlockVisit State T) :
    0 < visit.steps := by
  have htime : visit.entryTime.val < visit.exitTime.val := by
    exact visit.entryTime_lt_exitTime
  unfold FixedAlphaBlockVisit.steps
  omega

theorem FixedAlphaBlockVisit.entryTime_add_steps
    {State : Type} {T : Nat} (visit : FixedAlphaBlockVisit State T) :
    visit.entryTime.val + visit.steps = visit.exitTime.val := by
  have htime : visit.entryTime.val < visit.exitTime.val := by
    exact visit.entryTime_lt_exitTime
  unfold FixedAlphaBlockVisit.steps
  omega

/-- A fixed list of distinct maximal visits to one block is chronologically
separated.  The strict gap rejects an artificial split of one visit into two
adjacent visits; intervening times represent visits to other blocks. -/
def FixedAlphaBlockVisitsChronological
    {State : Type} {T : Nat}
  (visits : List (FixedAlphaBlockVisit State T)) : Prop :=
  visits.Pairwise fun earlier later =>
    earlier.exitTime.val < later.entryTime.val

/-- Materialize the advertised entry of one visit using exactly the carried
slab selected by the fixed alpha's cut offsets. -/
def fixedAlphaBlockVisitEntryConfiguration
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit State T)
    (carried : WorkSlab
      (advertisedBlockWidth alpha.offsets block)) : Configuration State :=
  configurationOfFixedAlphaEndpoint
    (advertisedBlockLower alpha.offsets block) visit.entry carried

/-- Deterministically replay the advertised visit from its materialized local
entry. -/
def fixedAlphaBlockVisitRun
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit machine.State T)
    (carried : WorkSlab
      (advertisedBlockWidth alpha.offsets block)) :
    Configuration machine.State :=
  runFrom machine input
    (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
    visit.steps

/-- The sole state transferred to the next advertised visit of this block:
the updated restriction of the same alpha-determined slab. -/
def fixedAlphaBlockVisitOutputSlab
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit machine.State T)
    (carried : WorkSlab
      (advertisedBlockWidth alpha.offsets block)) :
    WorkSlab (advertisedBlockWidth alpha.offsets block) :=
  restrictWorkSlab
    (advertisedBlockLower alpha.offsets block)
    (advertisedBlockWidth alpha.offsets block)
    (fixedAlphaBlockVisitRun machine input alpha block visit carried).workTape

/-- Materialize the advertised exit metadata together with the uniquely
computed output slab. -/
def fixedAlphaBlockVisitExitConfiguration
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit machine.State T)
    (carried : WorkSlab
      (advertisedBlockWidth alpha.offsets block)) :
    Configuration machine.State :=
  configurationOfFixedAlphaEndpoint
    (advertisedBlockLower alpha.offsets block) visit.exit
    (fixedAlphaBlockVisitOutputSlab
      machine input alpha block visit carried)

/-- Exact local validity of one advertised visit.

The bounded quantifier ranges over every pre-transition time.  The final work
head may leave the slab.  The exit clause checks the state and both heads but
does not demand any full-tape equality outside the carried slab. -/
def FixedAlphaBlockVisitValid
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit machine.State T)
    (carried : WorkSlab
      (advertisedBlockWidth alpha.offsets block)) : Prop :=
  (∀ time : Fin visit.steps,
    WorkCellInSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      (runFrom machine input
        (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
        time.val).workHead) ∧
  ConfigurationMatchesFixedAlphaEndpoint visit.exit
    (fixedAlphaBlockVisitRun machine input alpha block visit carried)

/-- A genuine Boolean interface for the one-visit local validity predicate.
The state equality procedure is explicit because a later circuit realization
must choose an encoding of control states. -/
def fixedAlphaBlockVisitCheck
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit machine.State T)
    (carried : WorkSlab
      (advertisedBlockWidth alpha.offsets block)) : Bool :=
  decide (∀ time : Fin visit.steps,
      WorkCellInSlab
        (advertisedBlockLower alpha.offsets block)
        (advertisedBlockWidth alpha.offsets block)
        (runFrom machine input
          (fixedAlphaBlockVisitEntryConfiguration
            alpha block visit carried) time.val).workHead) &&
    (decide (visit.exit.state =
        (fixedAlphaBlockVisitRun
          machine input alpha block visit carried).state) &&
      (decide (visit.exit.inputHead.val =
          (fixedAlphaBlockVisitRun
            machine input alpha block visit carried).inputHead) &&
        decide (visit.exit.workHead.val =
          (fixedAlphaBlockVisitRun
            machine input alpha block visit carried).workHead)))

theorem fixedAlphaBlockVisitCheck_eq_true_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit machine.State T)
    (carried : WorkSlab
      (advertisedBlockWidth alpha.offsets block)) :
    fixedAlphaBlockVisitCheck machine input alpha block visit carried = true ↔
      FixedAlphaBlockVisitValid machine input alpha block visit carried := by
  simp [fixedAlphaBlockVisitCheck, FixedAlphaBlockVisitValid,
    ConfigurationMatchesFixedAlphaEndpoint]

/-- A valid advertised visit replays from every concrete configuration that
has the same state, heads, and carried slab at entry.

The conclusion is the complete local interface at exit: the concrete run
agrees with the advertised exit state and heads and with the validator's
uniquely computed output slab.  No actual-run grouping occurs in the
statement. -/
theorem fixedAlphaBlockVisitValid_replays_matching_entry
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit machine.State T)
    (carried : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (hvalid : FixedAlphaBlockVisitValid
      machine input alpha block visit carried)
    (concreteEntry : Configuration machine.State)
    (hentry : SameOnWorkSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
      concreteEntry) :
    SameOnWorkSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      (fixedAlphaBlockVisitExitConfiguration
        machine input alpha block visit carried)
      (runFrom machine input concreteEntry visit.steps) := by
  let base := advertisedBlockLower alpha.offsets block
  let width := advertisedBlockWidth alpha.offsets block
  let advertisedEntry :=
    fixedAlphaBlockVisitEntryConfiguration alpha block visit carried
  let validatorExit :=
    fixedAlphaBlockVisitRun machine input alpha block visit carried
  let advertisedExit :=
    fixedAlphaBlockVisitExitConfiguration
      machine input alpha block visit carried
  have hinside : ∀ time, time < visit.steps →
      WorkCellInSlab base width
        (runFrom machine input advertisedEntry time).workHead := by
    intro time htime
    exact hvalid.1 ⟨time, htime⟩
  have hreplay : SameOnWorkSlab base width validatorExit
      (runFrom machine input concreteEntry visit.steps) := by
    exact runFrom_sameOnWorkSlab_same_input machine input hentry hinside
  have hexit : SameOnWorkSlab base width advertisedExit validatorExit := by
    rcases hvalid.2 with ⟨hstate, hinputHead, hworkHead⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [advertisedExit, validatorExit,
        fixedAlphaBlockVisitExitConfiguration] using hstate
    · simpa [advertisedExit, validatorExit,
        fixedAlphaBlockVisitExitConfiguration] using hinputHead
    · simpa [advertisedExit, validatorExit,
        fixedAlphaBlockVisitExitConfiguration] using hworkHead
    · calc
        restrictWorkSlab base width advertisedExit.workTape =
            fixedAlphaBlockVisitOutputSlab
              machine input alpha block visit carried := by
          simp [advertisedExit, base, width,
            fixedAlphaBlockVisitExitConfiguration]
        _ = restrictWorkSlab base width validatorExit.workTape := by
          rfl
  exact hexit.trans hreplay

/-- Readable projection of the preceding local-interface theorem: a matching
concrete entry reaches the advertised exit metadata and the exact carried
output slab. -/
theorem fixedAlphaBlockVisitValid_concrete_exit_interface
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit machine.State T)
    (carried : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (hvalid : FixedAlphaBlockVisitValid
      machine input alpha block visit carried)
    (concreteEntry : Configuration machine.State)
    (hentry : SameOnWorkSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
      concreteEntry) :
    ConfigurationMatchesFixedAlphaEndpoint visit.exit
        (runFrom machine input concreteEntry visit.steps) ∧
      restrictWorkSlab
          (advertisedBlockLower alpha.offsets block)
          (advertisedBlockWidth alpha.offsets block)
          (runFrom machine input concreteEntry visit.steps).workTape =
        fixedAlphaBlockVisitOutputSlab
          machine input alpha block visit carried := by
  have hsame := fixedAlphaBlockVisitValid_replays_matching_entry
    machine input alpha block visit carried hvalid concreteEntry hentry
  rcases hsame with ⟨hstate, hinputHead, hworkHead, htape⟩
  constructor
  · exact ⟨by simpa [fixedAlphaBlockVisitExitConfiguration] using hstate,
      by simpa [fixedAlphaBlockVisitExitConfiguration] using hinputHead,
      by simpa [fixedAlphaBlockVisitExitConfiguration] using hworkHead⟩
  · simpa [fixedAlphaBlockVisitExitConfiguration] using htape.symm

/-- Converse completeness interface for one visit.  If an arbitrary concrete
entry agrees with the materialized advertised entry, its own pre-transition
heads stay inside the advertised slab, and its exit realizes the advertised
metadata, then the deterministic local validator accepts the visit.

This is still a statement about an arbitrary supplied configuration, not an
actual-run segment decomposition. -/
theorem fixedAlphaBlockVisitValid_of_matching_concrete_replay
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit machine.State T)
    (carried : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (concreteEntry : Configuration machine.State)
    (hentry : SameOnWorkSlab
      (advertisedBlockLower alpha.offsets block)
      (advertisedBlockWidth alpha.offsets block)
      (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
      concreteEntry)
    (hinsideConcrete : ∀ time, time < visit.steps →
      WorkCellInSlab
        (advertisedBlockLower alpha.offsets block)
        (advertisedBlockWidth alpha.offsets block)
        (runFrom machine input concreteEntry time).workHead)
    (hexitConcrete : ConfigurationMatchesFixedAlphaEndpoint visit.exit
      (runFrom machine input concreteEntry visit.steps)) :
    FixedAlphaBlockVisitValid
      machine input alpha block visit carried := by
  let base := advertisedBlockLower alpha.offsets block
  let width := advertisedBlockWidth alpha.offsets block
  let advertisedEntry :=
    fixedAlphaBlockVisitEntryConfiguration alpha block visit carried
  constructor
  · intro time
    have hsameAt : SameOnWorkSlab base width
        (runFrom machine input concreteEntry time.val)
        (runFrom machine input advertisedEntry time.val) := by
      apply runFrom_sameOnWorkSlab_same_input machine input hentry.symm
      intro earlier hearlier
      exact hinsideConcrete earlier (by
        have htime := time.isLt
        omega)
    have hinside := hinsideConcrete time.val time.isLt
    rw [← hsameAt.2.2.1]
    exact hinside
  · have hsameExit : SameOnWorkSlab base width
        (runFrom machine input concreteEntry visit.steps)
        (runFrom machine input advertisedEntry visit.steps) := by
      exact runFrom_sameOnWorkSlab_same_input machine input hentry.symm
        hinsideConcrete
    rcases hexitConcrete with ⟨hstate, hinputHead, hworkHead⟩
    exact ⟨hstate.trans hsameExit.1,
      hinputHead.trans hsameExit.2.1,
      hworkHead.trans hsameExit.2.2.1⟩

/-- Deterministic fold of one carried slab through a fixed visit list.  This
function computes an output even for invalid advertisements; acceptance below
is what certifies every intermediate replay. -/
def replayFixedAlphaBlockVisits
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1)) :
    WorkSlab (advertisedBlockWidth alpha.offsets block) →
      List (FixedAlphaBlockVisit machine.State T) →
        WorkSlab (advertisedBlockWidth alpha.offsets block)
  | carried, [] => carried
  | carried, visit :: rest =>
      replayFixedAlphaBlockVisits machine input alpha block
        (fixedAlphaBlockVisitOutputSlab
          machine input alpha block visit carried) rest

/-- Recursive validator relation.  At each visit the only transferred tape
information is the output slab computed by the preceding visit. -/
def FixedAlphaBlockVisitReplayAccepted
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1)) :
    WorkSlab (advertisedBlockWidth alpha.offsets block) →
      List (FixedAlphaBlockVisit machine.State T) → Prop
  | _, [] => True
  | carried, visit :: rest =>
      FixedAlphaBlockVisitValid machine input alpha block visit carried ∧
        FixedAlphaBlockVisitReplayAccepted machine input alpha block
          (fixedAlphaBlockVisitOutputSlab
            machine input alpha block visit carried) rest

/-- Executable recursive checker corresponding exactly to
`FixedAlphaBlockVisitReplayAccepted`. -/
def fixedAlphaBlockVisitReplayCheck
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1)) :
    WorkSlab (advertisedBlockWidth alpha.offsets block) →
      List (FixedAlphaBlockVisit machine.State T) → Bool
  | _, [] => true
  | carried, visit :: rest =>
      fixedAlphaBlockVisitCheck machine input alpha block visit carried &&
        fixedAlphaBlockVisitReplayCheck machine input alpha block
          (fixedAlphaBlockVisitOutputSlab
            machine input alpha block visit carried) rest

theorem fixedAlphaBlockVisitReplayCheck_eq_true_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (carried : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit machine.State T)) :
    fixedAlphaBlockVisitReplayCheck
        machine input alpha block carried visits = true ↔
      FixedAlphaBlockVisitReplayAccepted
        machine input alpha block carried visits := by
  induction visits generalizing carried with
  | nil => simp [fixedAlphaBlockVisitReplayCheck,
      FixedAlphaBlockVisitReplayAccepted]
  | cons visit rest ih =>
      simp [fixedAlphaBlockVisitReplayCheck,
        FixedAlphaBlockVisitReplayAccepted,
        fixedAlphaBlockVisitCheck_eq_true_iff, ih]

/-- Public fixed-list acceptance predicate: chronological nonoverlap plus the
sequential one-slab replay checks. -/
def FixedAlphaBlockVisitListAccepted
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit machine.State T)) : Prop :=
  FixedAlphaBlockVisitsChronological visits ∧
    FixedAlphaBlockVisitReplayAccepted
      machine input alpha block initialSlab visits

/-- Boolean checker for strict chronological separation together with every
state-threaded local replay check. -/
def fixedAlphaBlockVisitListCheck
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
  (visits : List (FixedAlphaBlockVisit machine.State T)) : Bool :=
  decide (visits.Pairwise fun earlier later =>
      earlier.exitTime.val < later.entryTime.val) &&
    fixedAlphaBlockVisitReplayCheck
      machine input alpha block initialSlab visits

theorem fixedAlphaBlockVisitListCheck_eq_true_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit machine.State T)) :
    fixedAlphaBlockVisitListCheck
        machine input alpha block initialSlab visits = true ↔
      FixedAlphaBlockVisitListAccepted
        machine input alpha block initialSlab visits := by
  simp [fixedAlphaBlockVisitListCheck,
    FixedAlphaBlockVisitListAccepted,
    FixedAlphaBlockVisitsChronological,
    fixedAlphaBlockVisitReplayCheck_eq_true_iff]

/-- Every block validator starts from the one blank slab valuation.  Showing
that this matches a concrete block's first actual entry requires the separate
cross-block persistence argument; it is not assumed silently here. -/
def FixedAlphaBlockVisitListAcceptedFromBlank
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (visits : List (FixedAlphaBlockVisit machine.State T)) : Prop :=
  FixedAlphaBlockVisitListAccepted machine input alpha block
    (blankWorkSlab (advertisedBlockWidth alpha.offsets block)) visits

/-- Empty advertised visit lists are accepted from the blank slab.  In
particular this is the only possible list at `T = 0`, since every visit stores
a strict pair of times in `Fin (T + 1)`. -/
theorem fixedAlphaBlockVisitListAcceptedFromBlank_nil
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1)) :
    FixedAlphaBlockVisitListAcceptedFromBlank
      machine input alpha block [] := by
  simp [FixedAlphaBlockVisitListAcceptedFromBlank,
    FixedAlphaBlockVisitListAccepted,
    FixedAlphaBlockVisitsChronological,
    FixedAlphaBlockVisitReplayAccepted]

/-- There is no advertised nonempty visit when the time horizon is zero. -/
theorem fixedAlphaBlockVisit_zero_time_elim
    {State : Type} (visit : FixedAlphaBlockVisit State 0) : False := by
  have hEntry : visit.entryTime.val = 0 := by omega
  have hExit : visit.exitTime.val = 0 := by omega
  have hStrict := visit.entryTime_lt_exitTime
  omega

/-- Hence every advertised visit list at zero horizon is empty. -/
theorem fixedAlphaBlockVisits_zero_time_eq_nil
    {State : Type} (visits : List (FixedAlphaBlockVisit State 0)) :
    visits = [] := by
  cases visits with
  | nil => rfl
  | cons visit rest =>
      exact False.elim (fixedAlphaBlockVisit_zero_time_elim visit)

end OneTapeMagnification
end Frontier
end Pnp4
