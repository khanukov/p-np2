import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.OnePassAdvertisedBlockCutCheck

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Left-to-right in-place two-window block fold

This module implements the rolling `2b` counter carrier suggested by the
advertised-block geometry.  Before block `j`, the first `b` coordinates hold
the contribution made by block `j - 1` to bucket `j - 1`, and the second
`b` coordinates are zero.  Replaying block `j` updates both windows.  The
first window is then the sum of the only two source-block contributions to
bucket `j - 1`; that bucket is checked once, the second window is moved into
the first, and the second is cleared.

The bounded counter API previously exposed only a conservative
`initial + steps <= H` exactness theorem.  The first theorem below proves the
sharp nonsaturation criterion `initial + actual crossings <= H`.  This is
what permits the rolling carrier to keep horizon `H = T`, rather than `2T`.
-/

/-- Sharp bounded-vector exactness: saturation is unreachable whenever the
final value of each coordinate fits, irrespective of how many noncrossing
steps occur. -/
theorem onePassBoundedCrossingCounterVectorFrom_apply_val_of_final_le
    (machine : DeterministicMachine) (input : List Bool) {H m : Nat}
    (boundaries : Fin m -> Nat) (config : Configuration machine.State)
    (steps : Nat) (initial : BoundedCrossingCounterVector H m)
    (hfinal : forall i,
      (initial i).val +
          streamingWorkBoundaryCrossingCountFrom machine input config steps
            (boundaries i) <= H)
    (i : Fin m) :
    (onePassBoundedCrossingCounterVectorFrom machine input boundaries
        config steps initial i).val =
      (initial i).val +
        streamingWorkBoundaryCrossingCountFrom machine input config steps
          (boundaries i) := by
  induction steps generalizing config initial with
  | zero =>
      simp [onePassBoundedCrossingCounterVectorFrom,
        streamingWorkBoundaryCrossingCountFrom]
  | succ steps ih =>
      let next := step machine input config
      let bumped := bumpBoundedCrossingCounterVector boundaries
        config.workHead next.workHead initial
      have hdecomp : forall j,
          streamingWorkBoundaryCrossingCountFrom machine input config
              (steps + 1) (boundaries j) =
            (if CrossesWorkBoundary (boundaries j)
                config.workHead next.workHead then 1 else 0) +
              streamingWorkBoundaryCrossingCountFrom machine input next steps
                (boundaries j) := by
        intro j
        simp [streamingWorkBoundaryCrossingCountFrom, next]
      have hbumpVal : forall j,
          (bumped j).val = (initial j).val +
            if CrossesWorkBoundary (boundaries j)
                config.workHead next.workHead then 1 else 0 := by
        intro j
        have hle : (initial j).val +
            (if CrossesWorkBoundary (boundaries j)
                config.workHead next.workHead then 1 else 0) <= H := by
          have hall := hfinal j
          rw [hdecomp j] at hall
          omega
        simp [bumped, bumpBoundedCrossingCounterVector,
          min_eq_left hle]
      have htail : forall j,
          (bumped j).val +
              streamingWorkBoundaryCrossingCountFrom machine input next steps
                (boundaries j) <= H := by
        intro j
        rw [hbumpVal]
        have hall := hfinal j
        rw [hdecomp j] at hall
        omega
      change
        (onePassBoundedCrossingCounterVectorFrom machine input boundaries
          next steps bumped i).val = _
      rw [ih next bumped htail, hbumpVal]
      simp only [streamingWorkBoundaryCrossingCountFrom]
      dsimp [next]
      omega

/-- Sharp exactness for one fixed-alpha visit started from arbitrary bounded
counters. -/
theorem onePassFixedAlphaBlockVisitFromCounters_counter_val_of_final_le
    (machine : DeterministicMachine) (input : List Bool)
    {T b H m : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit machine.State T)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (boundaries : Fin m -> Nat)
    (initial : BoundedCrossingCounterVector H m)
    (hfinal : forall i,
      (initial i).val +
          streamingWorkBoundaryCrossingCountFrom machine input
            (fixedAlphaBlockVisitEntryConfiguration
              alpha block visit carried) visit.steps (boundaries i) <= H)
    (i : Fin m) :
    ((onePassFixedAlphaBlockVisitFromCounters machine input alpha block visit
        carried boundaries initial).counters i).val =
      (initial i).val +
        streamingWorkBoundaryCrossingCountFrom machine input
          (fixedAlphaBlockVisitEntryConfiguration
            alpha block visit carried) visit.steps (boundaries i) := by
  unfold onePassFixedAlphaBlockVisitFromCounters
  rw [onePassFixedAlphaVisitFrom_counters]
  exact onePassBoundedCrossingCounterVectorFrom_apply_val_of_final_le
    machine input boundaries
    (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
    visit.steps initial hfinal i

/-- Sharp exactness for the entire visit list of one block. -/
theorem onePassFixedAlphaBlockListFrom_counter_val_of_final_le
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool)
    {T b H m : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1)) (boundaries : Fin m -> Nat)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (initial : BoundedCrossingCounterVector H m)
    (visits : List (FixedAlphaBlockVisit machine.State T))
    (hfinal : forall i,
      (initial i).val +
          fixedAlphaBlockVisitListStreamingCrossingCount machine input alpha
            block (boundaries i) carried visits <= H)
    (i : Fin m) :
    ((onePassFixedAlphaBlockListFrom machine input alpha block boundaries
        carried initial visits).counters i).val =
      (initial i).val +
        fixedAlphaBlockVisitListStreamingCrossingCount machine input alpha
          block (boundaries i) carried visits := by
  induction visits generalizing carried initial with
  | nil =>
      simp [onePassFixedAlphaBlockListFrom,
        fixedAlphaBlockVisitListStreamingCrossingCount]
  | cons visit rest ih =>
      let current := onePassFixedAlphaBlockVisitFromCounters
        machine input alpha block visit carried boundaries initial
      let nextSlab := onePassFixedAlphaBlockVisitResultOutputSlab
        alpha block current
      have hfirst : forall j,
          (initial j).val +
              streamingWorkBoundaryCrossingCountFrom machine input
                (fixedAlphaBlockVisitEntryConfiguration
                  alpha block visit carried) visit.steps (boundaries j) <= H := by
        intro j
        have hall := hfinal j
        simp only [fixedAlphaBlockVisitListStreamingCrossingCount] at hall
        omega
      have hcurrent : forall j,
          (current.counters j).val =
            (initial j).val +
              streamingWorkBoundaryCrossingCountFrom machine input
                (fixedAlphaBlockVisitEntryConfiguration
                  alpha block visit carried) visit.steps (boundaries j) := by
        intro j
        exact
          onePassFixedAlphaBlockVisitFromCounters_counter_val_of_final_le
            machine input alpha block visit carried boundaries initial
            hfirst j
      have htail : forall j,
          (current.counters j).val +
              fixedAlphaBlockVisitListStreamingCrossingCount machine input
                alpha block (boundaries j) nextSlab rest <= H := by
        intro j
        rw [hcurrent j]
        have hall := hfinal j
        simp only [fixedAlphaBlockVisitListStreamingCrossingCount] at hall
        dsimp [nextSlab, current]
        rw [onePassFixedAlphaBlockVisitResultOutputSlab_fromCounters_eq]
        simpa only [Nat.add_assoc] using hall
      simp only [onePassFixedAlphaBlockListFrom]
      rw [ih nextSlab current.counters htail, hcurrent i]
      dsimp [nextSlab, current]
      rw [onePassFixedAlphaBlockVisitResultOutputSlab_fromCounters_eq]
      simp only [fixedAlphaBlockVisitListStreamingCrossingCount]
      omega

/-- Move the right `b`-window into the left `b`-window and clear the right
window in place. -/
def shiftRightWindowAndClear {H b : Nat}
    (counters : BoundedCrossingCounterVector H (b + b)) :
    BoundedCrossingCounterVector H (b + b) :=
  Fin.addCases
    (fun candidate => counters (Fin.natAdd b candidate))
    (fun _ => ⟨0, by omega⟩)

@[simp]
theorem shiftRightWindowAndClear_left {H b : Nat}
    (counters : BoundedCrossingCounterVector H (b + b))
    (candidate : Fin b) :
    shiftRightWindowAndClear counters (Fin.castAdd b candidate) =
      counters (Fin.natAdd b candidate) := by
  exact Fin.addCases_left candidate

@[simp]
theorem shiftRightWindowAndClear_right {H b : Nat}
    (counters : BoundedCrossingCounterVector H (b + b))
    (candidate : Fin b) :
    (shiftRightWindowAndClear counters
      (Fin.natAdd b candidate)).val = 0 := by
  change ((Fin.addCases _ _ (Fin.natAdd b candidate)) : Fin (H + 1)).val = 0
  rw [Fin.addCases_right]

/-- The local crossing contribution made by one source block to one named
boundary. -/
def fixedAlphaSourceBlockCrossingContribution
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (initialSlabs : forall block : Fin (T / b + 1),
      WorkSlab (advertisedBlockWidth alpha.offsets block))
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit machine.State T))
    (block : Fin (T / b + 1)) (boundary : Fin T) : Nat :=
  fixedAlphaBlockVisitListStreamingCrossingCount machine input alpha block
    boundary.val (initialSlabs block) (blockVisits block)

/-- The two source blocks adjacent to a full bucket. -/
def leftSourceBlockOfBucket {T b : Nat}
    (bucket : Fin (T / b)) : Fin (T / b + 1) :=
  ⟨bucket.val, by omega⟩

def rightSourceBlockOfBucket {T b : Nat}
    (bucket : Fin (T / b)) : Fin (T / b + 1) :=
  ⟨bucket.val + 1, by omega⟩

/-- Sum of the two adjacent source-block contributions to one bucket
candidate.  This is the profile materialized when the right source block is
processed by the rolling fold. -/
def adjacentSourceBucketCrossingProfile
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (initialSlabs : forall block : Fin (T / b + 1),
      WorkSlab (advertisedBlockWidth alpha.offsets block))
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit machine.State T))
    (bucket : Fin (T / b)) (candidate : Fin b) : Nat :=
  fixedAlphaSourceBlockCrossingContribution machine input alpha initialSlabs
      blockVisits (leftSourceBlockOfBucket bucket)
      (fullBucketBoundary bucket candidate) +
    fixedAlphaSourceBlockCrossingContribution machine input alpha initialSlabs
      blockVisits (rightSourceBlockOfBucket bucket)
      (fullBucketBoundary bucket candidate)

theorem adjacentSourceBucketCrossingProfile_decomposition
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (initialSlabs : forall block : Fin (T / b + 1),
      WorkSlab (advertisedBlockWidth alpha.offsets block))
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit machine.State T))
    (bucket : Fin (T / b)) (candidate : Fin b) :
    adjacentSourceBucketCrossingProfile machine input alpha initialSlabs
        blockVisits bucket candidate =
      fixedAlphaSourceBlockCrossingContribution machine input alpha
          initialSlabs blockVisits (leftSourceBlockOfBucket bucket)
          (fullBucketBoundary bucket candidate) +
      fixedAlphaSourceBlockCrossingContribution machine input alpha
          initialSlabs blockVisits (rightSourceBlockOfBucket bucket)
          (fullBucketBoundary bucket candidate) := by
  rfl

/-- Sum of all block-local contributions.  This is the honest block-ordered
candidate for the global profile; identifying it with the actual run is a
separate schedule/locality theorem. -/
def sourceBlockSummedCrossingProfile
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (initialSlabs : forall block : Fin (T / b + 1),
      WorkSlab (advertisedBlockWidth alpha.offsets block))
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit machine.State T))
    (boundary : Fin T) : Nat :=
  ∑ block : Fin (T / b + 1),
    fixedAlphaSourceBlockCrossingContribution machine input alpha initialSlabs
      blockVisits block boundary

/-- If nonadjacent source blocks contribute zero at a bucket candidate, the
all-block sum decomposes into exactly the two adjacent contributions used by
the rolling carrier. -/
theorem sourceBlockSummedCrossingProfile_eq_adjacent_of_nonadjacent_zero
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (initialSlabs : forall block : Fin (T / b + 1),
      WorkSlab (advertisedBlockWidth alpha.offsets block))
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit machine.State T))
    (bucket : Fin (T / b)) (candidate : Fin b)
    (hnonadjacent : forall block : Fin (T / b + 1),
      block ≠ leftSourceBlockOfBucket bucket ->
      block ≠ rightSourceBlockOfBucket bucket ->
      fixedAlphaSourceBlockCrossingContribution machine input alpha
        initialSlabs blockVisits block
          (fullBucketBoundary bucket candidate) = 0) :
    sourceBlockSummedCrossingProfile machine input alpha initialSlabs
        blockVisits (fullBucketBoundary bucket candidate) =
      adjacentSourceBucketCrossingProfile machine input alpha initialSlabs
        blockVisits bucket candidate := by
  let left := leftSourceBlockOfBucket bucket
  let right := rightSourceBlockOfBucket bucket
  let contribution := fun block : Fin (T / b + 1) =>
    fixedAlphaSourceBlockCrossingContribution machine input alpha initialSlabs
      blockVisits block (fullBucketBoundary bucket candidate)
  have hne : left ≠ right := by
    intro heq
    have hval := congrArg Fin.val heq
    simp [left, right, leftSourceBlockOfBucket,
      rightSourceBlockOfBucket] at hval
  have hrightMem : right ∈ (Finset.univ.erase left) := by
    exact Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ right⟩
  have hrest : ∑ block ∈ Finset.univ.erase left, contribution block =
      contribution right := by
    apply Finset.sum_eq_single right
    · intro block hmem hneRight
      have hneLeft : block ≠ left := (Finset.mem_erase.mp hmem).1
      exact hnonadjacent block hneLeft hneRight
    · intro hnot
      exact (hnot hrightMem).elim
  unfold sourceBlockSummedCrossingProfile
  rw [<- Finset.sum_erase_add Finset.univ contribution
    (Finset.mem_univ left)]
  rw [hrest]
  unfold adjacentSourceBucketCrossingProfile
  simp only [contribution, left, right]
  omega

/-- A block-local contribution has at most one increment per advertised
transition. -/
theorem fixedAlphaBlockVisitListStreamingCrossingCount_le_totalSteps
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1)) (boundary : Nat)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit machine.State T)) :
    fixedAlphaBlockVisitListStreamingCrossingCount machine input alpha block
        boundary carried visits <=
      fixedAlphaBlockVisitsTotalSteps visits := by
  induction visits generalizing carried with
  | nil =>
      simp [fixedAlphaBlockVisitListStreamingCrossingCount,
        fixedAlphaBlockVisitsTotalSteps]
  | cons visit rest ih =>
      simp only [fixedAlphaBlockVisitListStreamingCrossingCount,
        fixedAlphaBlockVisitsTotalSteps]
      have hone := streamingWorkBoundaryCrossingCountFrom_le_steps
        machine input
        (fixedAlphaBlockVisitEntryConfiguration alpha block visit carried)
        visit.steps boundary
      have hrest := ih
        (fixedAlphaBlockVisitOutputSlab
          machine input alpha block visit carried)
      omega

/-- Close the bucket immediately to the left of the current block, using the
now-complete first window.  The initial block closes nothing. -/
def closeLeftBucketFromFirstWindowCheck
    {T b H : Nat} (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1))
    (counters : BoundedCrossingCounterVector H (b + b)) : Bool :=
  if hleft : 0 < block.val then
    let bucket : Fin (T / b) := ⟨block.val - 1, by omega⟩
    oneSidedLeftmostMinimumCheck
      (counters (Fin.castAdd b (offsets bucket))).val
      (offsets bucket)
      (fun candidate => (counters (Fin.castAdd b candidate)).val)
  else true

/-- Exact reflection of a completed first window against any supplied
global crossing profile. -/
theorem closeLeftBucketFromFirstWindowCheck_eq_true_iff_of_exact
    {T b H : Nat} (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1))
    (counters : BoundedCrossingCounterVector H (b + b))
    (crossings : Fin T -> Nat)
    (hexact : forall (hleft : 0 < block.val) (candidate : Fin b),
      (counters (Fin.castAdd b candidate)).val =
        crossings (fullBucketBoundary
          (show Fin (T / b) from ⟨block.val - 1, by omega⟩)
          candidate)) :
    closeLeftBucketFromFirstWindowCheck offsets block counters = true <->
      forall hleft : 0 < block.val,
        AdvertisedCutOffsetIsLeftmostMinimum crossings
          (show Fin (T / b) from ⟨block.val - 1, by omega⟩)
          (offsets
            (show Fin (T / b) from ⟨block.val - 1, by omega⟩)) := by
  unfold closeLeftBucketFromFirstWindowCheck
  by_cases hleft : 0 < block.val
  · rw [dif_pos hleft]
    let bucket : Fin (T / b) := ⟨block.val - 1, by omega⟩
    have hvalues :
        (fun candidate : Fin b =>
          (counters (Fin.castAdd b candidate)).val) =
        (fun candidate : Fin b =>
          crossings (fullBucketBoundary bucket candidate)) := by
      funext candidate
      exact hexact hleft candidate
    have hselected :
        (counters (Fin.castAdd b (offsets bucket))).val =
          crossings (fullBucketBoundary bucket (offsets bucket)) := by
      exact hexact hleft (offsets bucket)
    have hcheck :
        oneSidedLeftmostMinimumCheck
            (counters (Fin.castAdd b (offsets bucket))).val
            (offsets bucket)
            (fun candidate =>
              (counters (Fin.castAdd b candidate)).val) = true <->
          AdvertisedCutOffsetIsLeftmostMinimum crossings bucket
            (offsets bucket) := by
      rw [hvalues, hselected,
        oneSidedLeftmostMinimumCheck_eq_true_iff,
        oneSidedLeftmostMinimum_bucket_iff]
    constructor
    · intro hfull _
      exact hcheck.1 (by simpa only [bucket] using hfull)
    · intro hfull
      have := hcheck.2 (hfull hleft)
      simpa only [bucket] using this
  · rw [dif_neg hleft]
    constructor
    · intro _ hproof
      exact (hleft hproof).elim
    · intro _
      rfl

/-- Mutable state of the global left-to-right fold.  Its finite data is two
`b`-windows plus two accumulated Boolean flags. -/
structure InPlaceTwoWindowFoldState (H b : Nat) where
  allBlockVisitsValid : Bool
  allClosedCutsValid : Bool
  counters : BoundedCrossingCounterVector H (b + b)

def initialInPlaceTwoWindowFoldState (H b : Nat) :
    InPlaceTwoWindowFoldState H b :=
  { allBlockVisitsValid := true
    allClosedCutsValid := true
    counters := zeroBoundedCrossingCounterVector H (b + b) }

/-- Replay one block into the current rolling carrier without resetting its
first window. -/
def replayBlockIntoRollingTwoWindows
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (initialSlabs : forall block : Fin (T / b + 1),
      WorkSlab (advertisedBlockWidth alpha.offsets block))
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit machine.State T))
    (block : Fin (T / b + 1))
    (initial : BoundedCrossingCounterVector T (b + b)) :
    OnePassFixedAlphaBlockListResult T (b + b)
      (advertisedBlockWidth alpha.offsets block) :=
  onePassFixedAlphaBlockListFrom machine input alpha block
    (advertisedBlockTwoWindowBoundaries block) (initialSlabs block) initial
    (blockVisits block)

/-- One in-place fold step: replay, close the completed left bucket, then
move the right window left and clear the right window. -/
def inPlaceTwoWindowBlockStep
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (initialSlabs : forall block : Fin (T / b + 1),
      WorkSlab (advertisedBlockWidth alpha.offsets block))
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit machine.State T))
    (state : InPlaceTwoWindowFoldState T b)
    (block : Fin (T / b + 1)) : InPlaceTwoWindowFoldState T b :=
  let replay := replayBlockIntoRollingTwoWindows machine input alpha
    initialSlabs blockVisits block state.counters
  { allBlockVisitsValid :=
      state.allBlockVisitsValid && replay.allVisitsValid
    allClosedCutsValid :=
      state.allClosedCutsValid &&
        closeLeftBucketFromFirstWindowCheck alpha.offsets block replay.counters
    counters := shiftRightWindowAndClear replay.counters }

/-- Fuelled implementation of the increasing block traversal. -/
def inPlaceTwoWindowBlockFoldFrom
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (initialSlabs : forall block : Fin (T / b + 1),
      WorkSlab (advertisedBlockWidth alpha.offsets block))
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit machine.State T)) :
    Nat -> Nat -> InPlaceTwoWindowFoldState T b ->
      InPlaceTwoWindowFoldState T b
  | _, 0, state => state
  | next, fuel + 1, state =>
      if hblock : next < T / b + 1 then
        inPlaceTwoWindowBlockFoldFrom machine input alpha initialSlabs
          blockVisits (next + 1) fuel
          (inPlaceTwoWindowBlockStep machine input alpha initialSlabs
            blockVisits state ⟨next, hblock⟩)
      else state

/-- The actual global fold processes advertised blocks in increasing order. -/
def inPlaceTwoWindowBlockFold
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (initialSlabs : forall block : Fin (T / b + 1),
      WorkSlab (advertisedBlockWidth alpha.offsets block))
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit machine.State T)) :
    InPlaceTwoWindowFoldState T b :=
  inPlaceTwoWindowBlockFoldFrom machine input alpha initialSlabs blockVisits
    0 (T / b + 1) (initialInPlaceTwoWindowFoldState T b)

/-- Bucket closed by one block, if any. -/
def closedBucketOfAdvertisedBlock? {T b : Nat}
    (block : Fin (T / b + 1)) : Option (Fin (T / b)) :=
  if hleft : 0 < block.val then
    some ⟨block.val - 1, by omega⟩
  else none

/-- Static trace of buckets closed by the increasing block traversal. -/
def inPlaceTwoWindowClosedBucketTrace (T b : Nat) : List (Fin (T / b)) :=
  (List.finRange (T / b + 1)).filterMap closedBucketOfAdvertisedBlock?

/-- Every full bucket is closed exactly once and in increasing order. -/
theorem inPlaceTwoWindowClosedBucketTrace_eq_finRange (T b : Nat) :
    inPlaceTwoWindowClosedBucketTrace T b = List.finRange (T / b) := by
  unfold inPlaceTwoWindowClosedBucketTrace
  rw [List.finRange_succ_eq_map]
  simp [closedBucketOfAdvertisedBlock?, Function.comp_def]

/-- Carrier invariant immediately before processing `block`. -/
def RollingTwoWindowCarrierBeforeBlock
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (initialSlabs : forall block : Fin (T / b + 1),
      WorkSlab (advertisedBlockWidth alpha.offsets block))
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit machine.State T))
    (block : Fin (T / b + 1))
    (counters : BoundedCrossingCounterVector T (b + b)) : Prop :=
  (forall (hleft : 0 < block.val) (candidate : Fin b),
      (counters (Fin.castAdd b candidate)).val =
        fixedAlphaSourceBlockCrossingContribution machine input alpha
          initialSlabs blockVisits
          (leftSourceBlockOfBucket
            (show Fin (T / b) from ⟨block.val - 1, by omega⟩))
          (fullBucketBoundary
            (show Fin (T / b) from ⟨block.val - 1, by omega⟩)
            candidate)) /\
    ((¬ 0 < block.val) -> forall candidate : Fin b,
      (counters (Fin.castAdd b candidate)).val = 0) /\
    forall candidate : Fin b,
      (counters (Fin.natAdd b candidate)).val = 0

/-- The zero carrier satisfies the invariant before the initial block. -/
theorem zeroCarrier_before_initialBlock
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (initialSlabs : forall block : Fin (T / b + 1),
      WorkSlab (advertisedBlockWidth alpha.offsets block))
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit machine.State T))
    (block : Fin (T / b + 1)) (hzero : block.val = 0) :
    RollingTwoWindowCarrierBeforeBlock machine input alpha initialSlabs
      blockVisits block (zeroBoundedCrossingCounterVector T (b + b)) := by
  unfold RollingTwoWindowCarrierBeforeBlock
  constructor
  · intro hleft
    omega
  · constructor <;> simp [zeroBoundedCrossingCounterVector]

/-- Exact room needed by the sharp bounded replay follows from the rolling
invariant, a per-block `T`-step bound, and the fact that each completed
two-source bucket profile is at most `T`. -/
theorem rollingTwoWindow_finalFits
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (initialSlabs : forall block : Fin (T / b + 1),
      WorkSlab (advertisedBlockWidth alpha.offsets block))
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit machine.State T))
    (block : Fin (T / b + 1))
    (initial : BoundedCrossingCounterVector T (b + b))
    (hinvariant : RollingTwoWindowCarrierBeforeBlock machine input alpha
      initialSlabs blockVisits block initial)
    (hsteps : fixedAlphaBlockVisitsTotalSteps (blockVisits block) <= T)
    (hadjacentLe : forall (bucket : Fin (T / b)) (candidate : Fin b),
      adjacentSourceBucketCrossingProfile machine input alpha initialSlabs
        blockVisits bucket candidate <= T) :
    forall i,
      (initial i).val +
          fixedAlphaBlockVisitListStreamingCrossingCount machine input alpha
            block (advertisedBlockTwoWindowBoundaries block i)
            (initialSlabs block) (blockVisits block) <= T := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro candidate
    by_cases hleft : 0 < block.val
    · let bucket : Fin (T / b) := ⟨block.val - 1, by omega⟩
      have hinitial := hinvariant.1 hleft candidate
      have hfull := hadjacentLe bucket candidate
      rw [advertisedBlockTwoWindowBoundaries_left block hleft candidate]
      rw [hinitial]
      unfold adjacentSourceBucketCrossingProfile at hfull
      have hright : rightSourceBlockOfBucket bucket = block := by
        apply Fin.ext
        simp [bucket, rightSourceBlockOfBucket]
        omega
      rw [hright] at hfull
      exact hfull
    · rw [hinvariant.2.1 hleft candidate]
      have hlocal :=
        fixedAlphaBlockVisitListStreamingCrossingCount_le_totalSteps
          machine input alpha block
          (advertisedBlockTwoWindowBoundaries block
            (Fin.castAdd b candidate))
          (initialSlabs block) (blockVisits block)
      omega
  · intro candidate
    rw [hinvariant.2.2 candidate]
    have hlocal :=
      fixedAlphaBlockVisitListStreamingCrossingCount_le_totalSteps
        machine input alpha block
        (advertisedBlockTwoWindowBoundaries block
          (Fin.natAdd b candidate))
        (initialSlabs block) (blockVisits block)
    omega

/-- After replaying the current block, the first window is the full sum of
the two adjacent source blocks for the bucket being closed. -/
theorem replayBlockIntoRollingTwoWindows_left_eq_adjacent
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (initialSlabs : forall block : Fin (T / b + 1),
      WorkSlab (advertisedBlockWidth alpha.offsets block))
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit machine.State T))
    (block : Fin (T / b + 1))
    (initial : BoundedCrossingCounterVector T (b + b))
    (hinvariant : RollingTwoWindowCarrierBeforeBlock machine input alpha
      initialSlabs blockVisits block initial)
    (hfit : forall i,
      (initial i).val +
          fixedAlphaBlockVisitListStreamingCrossingCount machine input alpha
            block (advertisedBlockTwoWindowBoundaries block i)
            (initialSlabs block) (blockVisits block) <= T)
    (hleft : 0 < block.val) (candidate : Fin b) :
    ((replayBlockIntoRollingTwoWindows machine input alpha initialSlabs
        blockVisits block initial).counters
      (Fin.castAdd b candidate)).val =
      adjacentSourceBucketCrossingProfile machine input alpha initialSlabs
        blockVisits
        (show Fin (T / b) from ⟨block.val - 1, by omega⟩) candidate := by
  unfold replayBlockIntoRollingTwoWindows
  rw [onePassFixedAlphaBlockListFrom_counter_val_of_final_le
    machine input alpha block (advertisedBlockTwoWindowBoundaries block)
    (initialSlabs block) initial (blockVisits block) hfit
    (Fin.castAdd b candidate)]
  rw [advertisedBlockTwoWindowBoundaries_left block hleft candidate]
  rw [hinvariant.1 hleft candidate]
  unfold adjacentSourceBucketCrossingProfile
  have hright :
      rightSourceBlockOfBucket
          (show Fin (T / b) from ⟨block.val - 1, by omega⟩) = block := by
    apply Fin.ext
    simp [rightSourceBlockOfBucket]
    omega
  rw [hright]
  rfl

/-- The shifted first window is exactly the current block's contribution to
its right bucket, ready to be completed by the next block. -/
theorem replayBlockIntoRollingTwoWindows_shifted_left_eq_current
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (initialSlabs : forall block : Fin (T / b + 1),
      WorkSlab (advertisedBlockWidth alpha.offsets block))
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit machine.State T))
    (block : Fin (T / b + 1))
    (initial : BoundedCrossingCounterVector T (b + b))
    (hinvariant : RollingTwoWindowCarrierBeforeBlock machine input alpha
      initialSlabs blockVisits block initial)
    (hfit : forall i,
      (initial i).val +
          fixedAlphaBlockVisitListStreamingCrossingCount machine input alpha
            block (advertisedBlockTwoWindowBoundaries block i)
            (initialSlabs block) (blockVisits block) <= T)
    (hright : block.val < T / b) (candidate : Fin b) :
    (shiftRightWindowAndClear
        (replayBlockIntoRollingTwoWindows machine input alpha initialSlabs
          blockVisits block initial).counters
      (Fin.castAdd b candidate)).val =
      fixedAlphaSourceBlockCrossingContribution machine input alpha
        initialSlabs blockVisits block
        (fullBucketBoundary
          (show Fin (T / b) from ⟨block.val, hright⟩) candidate) := by
  rw [shiftRightWindowAndClear_left]
  unfold replayBlockIntoRollingTwoWindows
  rw [onePassFixedAlphaBlockListFrom_counter_val_of_final_le
    machine input alpha block (advertisedBlockTwoWindowBoundaries block)
    (initialSlabs block) initial (blockVisits block) hfit
    (Fin.natAdd b candidate)]
  rw [advertisedBlockTwoWindowBoundaries_right block hright candidate]
  rw [hinvariant.2.2 candidate]
  simp [fixedAlphaSourceBlockCrossingContribution]

/-- The transfer always clears the second window. -/
theorem replayBlockIntoRollingTwoWindows_shifted_right_zero
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (initialSlabs : forall block : Fin (T / b + 1),
      WorkSlab (advertisedBlockWidth alpha.offsets block))
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit machine.State T))
    (block : Fin (T / b + 1))
    (initial : BoundedCrossingCounterVector T (b + b))
    (candidate : Fin b) :
    (shiftRightWindowAndClear
        (replayBlockIntoRollingTwoWindows machine input alpha initialSlabs
          blockVisits block initial).counters
      (Fin.natAdd b candidate)).val = 0 := by
  exact shiftRightWindowAndClear_right _ candidate

/-- The shifted carrier is exactly the before-block invariant for the next
block.  This is the inductive heart of the left-to-right fold. -/
theorem shiftedCarrier_before_successorBlock
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (initialSlabs : forall block : Fin (T / b + 1),
      WorkSlab (advertisedBlockWidth alpha.offsets block))
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit machine.State T))
    (block : Fin (T / b + 1))
    (initial : BoundedCrossingCounterVector T (b + b))
    (hinvariant : RollingTwoWindowCarrierBeforeBlock machine input alpha
      initialSlabs blockVisits block initial)
    (hfit : forall i,
      (initial i).val +
          fixedAlphaBlockVisitListStreamingCrossingCount machine input alpha
            block (advertisedBlockTwoWindowBoundaries block i)
            (initialSlabs block) (blockVisits block) <= T)
    (hright : block.val < T / b) :
    RollingTwoWindowCarrierBeforeBlock machine input alpha initialSlabs
      blockVisits
      (show Fin (T / b + 1) from ⟨block.val + 1, by omega⟩)
      (shiftRightWindowAndClear
        (replayBlockIntoRollingTwoWindows machine input alpha initialSlabs
          blockVisits block initial).counters) := by
  unfold RollingTwoWindowCarrierBeforeBlock
  constructor
  · intro _ candidate
    have hshift :=
      replayBlockIntoRollingTwoWindows_shifted_left_eq_current
        machine input alpha initialSlabs blockVisits block initial hinvariant
        hfit hright candidate
    simpa [leftSourceBlockOfBucket] using hshift
  · constructor
    · intro hnot
      exfalso
      apply hnot
      simp
    · intro candidate
      exact replayBlockIntoRollingTwoWindows_shifted_right_zero
        machine input alpha initialSlabs blockVisits block initial candidate

/-- With exact two-source decomposition into a global profile, the bucket
closed by this replay passes exactly when its advertised offset is the
leftmost minimum of that global profile. -/
theorem closeReplayedLeftBucketCheck_eq_true_iff_global
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (initialSlabs : forall block : Fin (T / b + 1),
      WorkSlab (advertisedBlockWidth alpha.offsets block))
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit machine.State T))
    (block : Fin (T / b + 1))
    (initial : BoundedCrossingCounterVector T (b + b))
    (hinvariant : RollingTwoWindowCarrierBeforeBlock machine input alpha
      initialSlabs blockVisits block initial)
    (hfit : forall i,
      (initial i).val +
          fixedAlphaBlockVisitListStreamingCrossingCount machine input alpha
            block (advertisedBlockTwoWindowBoundaries block i)
            (initialSlabs block) (blockVisits block) <= T)
    (globalCrossings : Fin T -> Nat)
    (hdecomposition : forall (bucket : Fin (T / b)) (candidate : Fin b),
      adjacentSourceBucketCrossingProfile machine input alpha initialSlabs
          blockVisits bucket candidate =
        globalCrossings (fullBucketBoundary bucket candidate)) :
    closeLeftBucketFromFirstWindowCheck alpha.offsets block
        (replayBlockIntoRollingTwoWindows machine input alpha initialSlabs
          blockVisits block initial).counters = true <->
      forall hleft : 0 < block.val,
        AdvertisedCutOffsetIsLeftmostMinimum globalCrossings
          (show Fin (T / b) from ⟨block.val - 1, by omega⟩)
          (alpha.offsets
            (show Fin (T / b) from ⟨block.val - 1, by omega⟩)) := by
  apply closeLeftBucketFromFirstWindowCheck_eq_true_iff_of_exact
  intro hleft candidate
  rw [replayBlockIntoRollingTwoWindows_left_eq_adjacent machine input alpha
    initialSlabs blockVisits block initial hinvariant hfit hleft candidate]
  exact hdecomposition _ candidate

/-- Blank slab family used by the block-ordered specialization of a timed
schedule. -/
def timedScheduleBlankBlockSlabs
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b) :
    forall block : Fin (T / b + 1),
      WorkSlab (advertisedBlockWidth alpha.offsets block) :=
  fun block => blankWorkSlab (advertisedBlockWidth alpha.offsets block)

/-- Per-block visit family obtained by stable filtering of one timed
schedule. -/
def timedScheduleBlockVisitFamily
    {State : Type} {T b : Nat}
    (scheduled : List (TimedAlphaScheduledVisit State T b)) :
    Fin (T / b + 1) -> List (FixedAlphaBlockVisit State T) :=
  fun block => timedAlphaBlockVisits block scheduled

/-- The precise remaining locality/permutation statement for the schedule
layer: the two adjacent block-ordered contributions equal the actual global
crossing count at every full-bucket candidate. -/
def TimedScheduleAdjacentSourceDecomposesActual
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b)) : Prop :=
  forall (bucket : Fin (T / b)) (candidate : Fin b),
    adjacentSourceBucketCrossingProfile machine input alpha
        (timedScheduleBlankBlockSlabs alpha)
        (timedScheduleBlockVisitFamily scheduled) bucket candidate =
      actualWorkBoundaryCrossingProfile machine input T
        (fullBucketBoundary bucket candidate)

/-- The remaining schedule decomposition follows from two independently
checkable facts: block grouping preserves the total profile, and source
blocks not adjacent to a candidate contribute zero. -/
theorem timedScheduleAdjacentSourceDecomposesActual_of_sum_and_locality
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hsum : forall boundary : Fin T,
      sourceBlockSummedCrossingProfile machine input alpha
          (timedScheduleBlankBlockSlabs alpha)
          (timedScheduleBlockVisitFamily scheduled) boundary =
        actualWorkBoundaryCrossingProfile machine input T boundary)
    (hlocality : forall (bucket : Fin (T / b)) (candidate : Fin b)
      (block : Fin (T / b + 1)),
      block ≠ leftSourceBlockOfBucket bucket ->
      block ≠ rightSourceBlockOfBucket bucket ->
      fixedAlphaSourceBlockCrossingContribution machine input alpha
        (timedScheduleBlankBlockSlabs alpha)
        (timedScheduleBlockVisitFamily scheduled) block
          (fullBucketBoundary bucket candidate) = 0) :
    TimedScheduleAdjacentSourceDecomposesActual
      machine input alpha scheduled := by
  intro bucket candidate
  rw [<- sourceBlockSummedCrossingProfile_eq_adjacent_of_nonadjacent_zero
    machine input alpha (timedScheduleBlankBlockSlabs alpha)
    (timedScheduleBlockVisitFamily scheduled) bucket candidate
    (hlocality bucket candidate)]
  exact hsum _

/-- Every individual boundary is crossed at most once per transition. -/
theorem actualWorkBoundaryCrossingProfile_le_horizon
    (machine : DeterministicMachine) (input : List Bool)
    (T : Nat) (boundary : Fin T) :
    actualWorkBoundaryCrossingProfile machine input T boundary <= T := by
  unfold actualWorkBoundaryCrossingProfile workBoundaryCrossingCount
  rw [<- streamingWorkBoundaryCrossingCountFrom_eq]
  exact streamingWorkBoundaryCrossingCountFrom_le_steps machine input
    (initialConfiguration machine) T boundary.val

/-- The decomposition premise immediately supplies the `T` bound required
by the sharp rolling carrier. -/
theorem timedSchedule_adjacentSourceProfile_le_horizon
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hdecomposition : TimedScheduleAdjacentSourceDecomposesActual
      machine input alpha scheduled)
    (bucket : Fin (T / b)) (candidate : Fin b) :
    adjacentSourceBucketCrossingProfile machine input alpha
        (timedScheduleBlankBlockSlabs alpha)
        (timedScheduleBlockVisitFamily scheduled) bucket candidate <= T := by
  rw [hdecomposition bucket candidate]
  exact actualWorkBoundaryCrossingProfile_le_horizon machine input T _

/-- Schedule validity supplies every per-block duration bound needed by the
rolling fold. -/
theorem timedScheduleBlockVisitFamily_totalSteps_le_horizon
    (machine : DeterministicMachine)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha scheduled)
    (block : Fin (T / b + 1)) :
    fixedAlphaBlockVisitsTotalSteps
        (timedScheduleBlockVisitFamily scheduled block) <= T := by
  exact hschedule.blockVisitsTotalSteps_le_horizon machine block

/-- Under schedule validity and the exact decomposition premise, every
rolling block replay fits in the `Fin (T+1)` counters. -/
theorem timedSchedule_rollingTwoWindow_finalFits
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha scheduled)
    (hdecomposition : TimedScheduleAdjacentSourceDecomposesActual
      machine input alpha scheduled)
    (block : Fin (T / b + 1))
    (initial : BoundedCrossingCounterVector T (b + b))
    (hinvariant : RollingTwoWindowCarrierBeforeBlock machine input alpha
      (timedScheduleBlankBlockSlabs alpha)
      (timedScheduleBlockVisitFamily scheduled) block initial) :
    forall i,
      (initial i).val +
          fixedAlphaBlockVisitListStreamingCrossingCount machine input alpha
            block (advertisedBlockTwoWindowBoundaries block i)
            (timedScheduleBlankBlockSlabs alpha block)
            (timedScheduleBlockVisitFamily scheduled block) <= T := by
  exact rollingTwoWindow_finalFits machine input alpha
    (timedScheduleBlankBlockSlabs alpha)
    (timedScheduleBlockVisitFamily scheduled) block initial hinvariant
    (timedScheduleBlockVisitFamily_totalSteps_le_horizon machine alpha
      scheduled hschedule block)
    (timedSchedule_adjacentSourceProfile_le_horizon machine input alpha
      scheduled hdecomposition)

/-- All-block replay validity makes each block replay Boolean accept,
independently of the carried counter contents. -/
theorem timedSchedule_replayBlock_allVisitsValid
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha scheduled)
    (block : Fin (T / b + 1))
    (initial : BoundedCrossingCounterVector T (b + b)) :
    (replayBlockIntoRollingTwoWindows machine input alpha
      (timedScheduleBlankBlockSlabs alpha)
      (timedScheduleBlockVisitFamily scheduled) block initial).allVisitsValid =
        true := by
  unfold replayBlockIntoRollingTwoWindows
  apply (onePassFixedAlphaBlockListFrom_allVisitsValid_eq_true_iff
    machine input alpha block (advertisedBlockTwoWindowBoundaries block)
    (timedScheduleBlankBlockSlabs alpha block) initial
    (timedScheduleBlockVisitFamily scheduled block)).2
  exact (haccepted block).2

/-- Schedule-level one-step reflection against the actual run.  Everything
except `TimedScheduleAdjacentSourceDecomposesActual` is discharged by the
existing schedule and all-block validity APIs. -/
theorem timedSchedule_closeReplayedLeftBucketCheck_eq_true_iff_actual
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha scheduled)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha scheduled)
    (hdecomposition : TimedScheduleAdjacentSourceDecomposesActual
      machine input alpha scheduled)
    (block : Fin (T / b + 1))
    (initial : BoundedCrossingCounterVector T (b + b))
    (hinvariant : RollingTwoWindowCarrierBeforeBlock machine input alpha
      (timedScheduleBlankBlockSlabs alpha)
      (timedScheduleBlockVisitFamily scheduled) block initial) :
    ((replayBlockIntoRollingTwoWindows machine input alpha
        (timedScheduleBlankBlockSlabs alpha)
        (timedScheduleBlockVisitFamily scheduled) block initial).allVisitsValid &&
      closeLeftBucketFromFirstWindowCheck alpha.offsets block
        (replayBlockIntoRollingTwoWindows machine input alpha
          (timedScheduleBlankBlockSlabs alpha)
          (timedScheduleBlockVisitFamily scheduled) block initial).counters) =
        true <->
      forall hleft : 0 < block.val,
        AdvertisedCutOffsetIsLeftmostMinimum
          (actualWorkBoundaryCrossingProfile machine input T)
          (show Fin (T / b) from ⟨block.val - 1, by omega⟩)
          (alpha.offsets
            (show Fin (T / b) from ⟨block.val - 1, by omega⟩)) := by
  have hfit := timedSchedule_rollingTwoWindow_finalFits machine input alpha
    scheduled hschedule hdecomposition block initial hinvariant
  have hvisit := timedSchedule_replayBlock_allVisitsValid machine input alpha
    scheduled haccepted block initial
  have hclose := closeReplayedLeftBucketCheck_eq_true_iff_global machine input alpha
    (timedScheduleBlankBlockSlabs alpha)
    (timedScheduleBlockVisitFamily scheduled) block initial hinvariant hfit
    (actualWorkBoundaryCrossingProfile machine input T) hdecomposition
  simpa only [Bool.and_eq_true, hvisit, true_and] using hclose

/-- Recursive semantic specification mirroring the visit-validity flag of
the fuelled fold. -/
def rollingBlockVisitSpecFrom
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (initialSlabs : forall block : Fin (T / b + 1),
      WorkSlab (advertisedBlockWidth alpha.offsets block))
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit machine.State T)) : Nat -> Nat -> Prop
  | _, 0 => True
  | next, fuel + 1 =>
      if hblock : next < T / b + 1 then
        FixedAlphaBlockVisitReplayAccepted machine input alpha
            ⟨next, hblock⟩ (initialSlabs ⟨next, hblock⟩)
            (blockVisits ⟨next, hblock⟩) /\
          rollingBlockVisitSpecFrom machine input alpha initialSlabs
            blockVisits (next + 1) fuel
      else True

/-- Recursive semantic specification mirroring the cut-validity flag of the
fuelled fold. -/
def rollingClosedCutSpecFrom
    {T b : Nat} (offsets : CanonicalCutOffsets T b)
    (crossings : Fin T -> Nat) : Nat -> Nat -> Prop
  | _, 0 => True
  | next, fuel + 1 =>
      if hblock : next < T / b + 1 then
        (forall hleft : 0 < next,
            AdvertisedCutOffsetIsLeftmostMinimum crossings
              (show Fin (T / b) from ⟨next - 1, by omega⟩)
              (offsets
                (show Fin (T / b) from ⟨next - 1, by omega⟩))) /\
          rollingClosedCutSpecFrom offsets crossings (next + 1) fuel
      else True

/-- Exact recursive reflection for both Boolean flags of the global fold.
The proof simultaneously propagates the rolling carrier invariant. -/
theorem inPlaceTwoWindowBlockFoldFrom_flags_reflect
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (initialSlabs : forall block : Fin (T / b + 1),
      WorkSlab (advertisedBlockWidth alpha.offsets block))
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit machine.State T))
    (globalCrossings : Fin T -> Nat)
    (hsteps : forall block : Fin (T / b + 1),
      fixedAlphaBlockVisitsTotalSteps (blockVisits block) <= T)
    (hadjacentLe : forall (bucket : Fin (T / b)) (candidate : Fin b),
      adjacentSourceBucketCrossingProfile machine input alpha initialSlabs
        blockVisits bucket candidate <= T)
    (hdecomposition : forall (bucket : Fin (T / b)) (candidate : Fin b),
      adjacentSourceBucketCrossingProfile machine input alpha initialSlabs
          blockVisits bucket candidate =
        globalCrossings (fullBucketBoundary bucket candidate))
    (next fuel : Nat) (state : InPlaceTwoWindowFoldState T b)
    (hinvariant : forall hblock : next < T / b + 1,
      RollingTwoWindowCarrierBeforeBlock machine input alpha initialSlabs
        blockVisits ⟨next, hblock⟩ state.counters) :
    ((inPlaceTwoWindowBlockFoldFrom machine input alpha initialSlabs
          blockVisits next fuel state).allBlockVisitsValid = true <->
        state.allBlockVisitsValid = true /\
          rollingBlockVisitSpecFrom machine input alpha initialSlabs
            blockVisits next fuel) /\
      ((inPlaceTwoWindowBlockFoldFrom machine input alpha initialSlabs
          blockVisits next fuel state).allClosedCutsValid = true <->
        state.allClosedCutsValid = true /\
          rollingClosedCutSpecFrom alpha.offsets globalCrossings next fuel) := by
  induction fuel generalizing next state with
  | zero =>
      simp [inPlaceTwoWindowBlockFoldFrom, rollingBlockVisitSpecFrom,
        rollingClosedCutSpecFrom]
  | succ fuel ih =>
      by_cases hblock : next < T / b + 1
      · let block : Fin (T / b + 1) := ⟨next, hblock⟩
        let replay := replayBlockIntoRollingTwoWindows machine input alpha
          initialSlabs blockVisits block state.counters
        let nextState := inPlaceTwoWindowBlockStep machine input alpha
          initialSlabs blockVisits state block
        have hcurrentInvariant := hinvariant hblock
        have hfit := rollingTwoWindow_finalFits machine input alpha initialSlabs
          blockVisits block state.counters hcurrentInvariant (hsteps block)
          hadjacentLe
        have hvisit : replay.allVisitsValid = true <->
            FixedAlphaBlockVisitReplayAccepted machine input alpha block
              (initialSlabs block) (blockVisits block) := by
          unfold replay replayBlockIntoRollingTwoWindows
          exact onePassFixedAlphaBlockListFrom_allVisitsValid_eq_true_iff
            machine input alpha block (advertisedBlockTwoWindowBoundaries block)
            (initialSlabs block) state.counters (blockVisits block)
        have hclose :
            closeLeftBucketFromFirstWindowCheck alpha.offsets block
                replay.counters = true <->
              forall hleft : 0 < block.val,
                AdvertisedCutOffsetIsLeftmostMinimum globalCrossings
                  (show Fin (T / b) from
                    ⟨block.val - 1, by omega⟩)
                  (alpha.offsets (show Fin (T / b) from
                    ⟨block.val - 1, by omega⟩)) := by
          exact closeReplayedLeftBucketCheck_eq_true_iff_global machine input
            alpha initialSlabs blockVisits block state.counters
            hcurrentInvariant hfit globalCrossings hdecomposition
        have hnextInvariant : forall hnext : next + 1 < T / b + 1,
            RollingTwoWindowCarrierBeforeBlock machine input alpha
              initialSlabs blockVisits ⟨next + 1, hnext⟩
              nextState.counters := by
          intro hnext
          have hright : block.val < T / b := by
            simp only [block]
            omega
          have hshift := shiftedCarrier_before_successorBlock machine input
            alpha initialSlabs blockVisits block state.counters
            hcurrentInvariant hfit hright
          simpa only [nextState, inPlaceTwoWindowBlockStep, replay, block] using
            hshift
        have hrec := ih (next + 1) nextState hnextInvariant
        have hfold :
            inPlaceTwoWindowBlockFoldFrom machine input alpha initialSlabs
                blockVisits next (fuel + 1) state =
              inPlaceTwoWindowBlockFoldFrom machine input alpha initialSlabs
                blockVisits (next + 1) fuel nextState := by
          simp [inPlaceTwoWindowBlockFoldFrom, hblock, nextState, block]
        have hvisitSpec :
            rollingBlockVisitSpecFrom machine input alpha initialSlabs
                blockVisits next (fuel + 1) <->
              FixedAlphaBlockVisitReplayAccepted machine input alpha block
                  (initialSlabs block) (blockVisits block) /\
                rollingBlockVisitSpecFrom machine input alpha initialSlabs
                  blockVisits (next + 1) fuel := by
          simp [rollingBlockVisitSpecFrom, hblock, block]
        have hcutSpec :
            rollingClosedCutSpecFrom alpha.offsets globalCrossings next
                (fuel + 1) <->
              (forall hleft : 0 < block.val,
                  AdvertisedCutOffsetIsLeftmostMinimum globalCrossings
                    (show Fin (T / b) from
                      ⟨block.val - 1, by omega⟩)
                    (alpha.offsets (show Fin (T / b) from
                      ⟨block.val - 1, by omega⟩))) /\
                rollingClosedCutSpecFrom alpha.offsets globalCrossings
                  (next + 1) fuel := by
          simp [rollingClosedCutSpecFrom, hblock, block]
        rw [hfold]
        constructor
        · constructor
          · intro hfinal
            have hparts := hrec.1.1 hfinal
            have hstep : state.allBlockVisitsValid = true /\
                replay.allVisitsValid = true := by
              simpa only [nextState, inPlaceTwoWindowBlockStep, replay,
                Bool.and_eq_true] using hparts.1
            refine ⟨hstep.1, hvisitSpec.2 ⟨hvisit.1 hstep.2, hparts.2⟩⟩
          · rintro ⟨hstate, hspec⟩
            rcases hvisitSpec.1 hspec with ⟨hcurrent, htail⟩
            apply hrec.1.2
            constructor
            · simpa only [nextState, inPlaceTwoWindowBlockStep, replay,
                Bool.and_eq_true] using ⟨hstate, hvisit.2 hcurrent⟩
            · exact htail
        · constructor
          · intro hfinal
            have hparts := hrec.2.1 hfinal
            have hstep : state.allClosedCutsValid = true /\
                closeLeftBucketFromFirstWindowCheck alpha.offsets block
                  replay.counters = true := by
              simpa only [nextState, inPlaceTwoWindowBlockStep, replay,
                Bool.and_eq_true] using hparts.1
            refine ⟨hstep.1, hcutSpec.2 ⟨hclose.1 hstep.2, hparts.2⟩⟩
          · rintro ⟨hstate, hspec⟩
            rcases hcutSpec.1 hspec with ⟨hcurrent, htail⟩
            apply hrec.2.2
            constructor
            · simpa only [nextState, inPlaceTwoWindowBlockStep, replay,
                Bool.and_eq_true] using ⟨hstate, hclose.2 hcurrent⟩
            · exact htail
      · simp [inPlaceTwoWindowBlockFoldFrom, rollingBlockVisitSpecFrom,
          rollingClosedCutSpecFrom, hblock]

/-- Range characterization of the recursive cut specification. -/
theorem rollingClosedCutSpecFrom_iff_range
    {T b : Nat} (offsets : CanonicalCutOffsets T b)
    (crossings : Fin T -> Nat) (next fuel : Nat)
    (hspan : next + fuel <= T / b + 1) :
    rollingClosedCutSpecFrom offsets crossings next fuel <->
      forall bucket : Fin (T / b),
        next <= bucket.val + 1 -> bucket.val + 1 < next + fuel ->
          AdvertisedCutOffsetIsLeftmostMinimum crossings bucket
            (offsets bucket) := by
  induction fuel generalizing next with
  | zero =>
      constructor
      · intro _ bucket hlower hupper
        omega
      · intro _
        trivial
  | succ fuel ih =>
      have hblock : next < T / b + 1 := by omega
      rw [rollingClosedCutSpecFrom, dif_pos hblock,
        ih (next + 1) (by omega)]
      constructor
      · rintro ⟨hcurrent, htail⟩ bucket hlower hupper
        by_cases heq : bucket.val + 1 = next
        · have hpos : 0 < next := by omega
          have hbucket :
              bucket =
                (show Fin (T / b) from ⟨next - 1, by omega⟩) := by
            apply Fin.ext
            change bucket.val = next - 1
            omega
          simpa only [hbucket] using hcurrent hpos
        · exact htail bucket (by omega) (by omega)
      · intro hall
        constructor
        · intro hpos
          let bucket : Fin (T / b) := ⟨next - 1, by omega⟩
          have hcut := hall bucket (by simp [bucket]; omega)
            (by simp [bucket]; omega)
          simpa only [bucket] using hcut
        · intro bucket hlower hupper
          exact hall bucket (by omega) (by omega)

/-- The full traversal cut specification is the ordinary universal
leftmost-minimum condition over all full buckets. -/
theorem rollingClosedCutSpecFrom_full_iff_allBuckets
    {T b : Nat} (offsets : CanonicalCutOffsets T b)
    (crossings : Fin T -> Nat) :
    rollingClosedCutSpecFrom offsets crossings 0 (T / b + 1) <->
      forall bucket : Fin (T / b),
        AdvertisedCutOffsetIsLeftmostMinimum crossings bucket
          (offsets bucket) := by
  rw [rollingClosedCutSpecFrom_iff_range offsets crossings 0 (T / b + 1)
    (by omega)]
  constructor
  · intro hall bucket
    exact hall bucket (by omega) (by omega)
  · intro hall bucket _ _
    exact hall bucket

/-- Range characterization of the recursive block-visit specification. -/
theorem rollingBlockVisitSpecFrom_iff_range
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (initialSlabs : forall block : Fin (T / b + 1),
      WorkSlab (advertisedBlockWidth alpha.offsets block))
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit machine.State T))
    (next fuel : Nat) (hspan : next + fuel <= T / b + 1) :
    rollingBlockVisitSpecFrom machine input alpha initialSlabs blockVisits
        next fuel <->
      forall block : Fin (T / b + 1),
        next <= block.val -> block.val < next + fuel ->
          FixedAlphaBlockVisitReplayAccepted machine input alpha block
            (initialSlabs block) (blockVisits block) := by
  induction fuel generalizing next with
  | zero =>
      constructor
      · intro _ block hlower hupper
        omega
      · intro _
        trivial
  | succ fuel ih =>
      have hblock : next < T / b + 1 := by omega
      rw [rollingBlockVisitSpecFrom, dif_pos hblock,
        ih (next + 1) (by omega)]
      constructor
      · rintro ⟨hcurrent, htail⟩ block hlower hupper
        by_cases heq : block.val = next
        · have hblockEq : block =
              (show Fin (T / b + 1) from ⟨next, hblock⟩) := by
            apply Fin.ext
            exact heq
          cases hblockEq
          exact hcurrent
        · exact htail block (by omega) (by omega)
      · intro hall
        constructor
        · apply hall ⟨next, hblock⟩
          · rfl
          · simp
        · intro block hlower hupper
          exact hall block (by omega) (by omega)

/-- The full traversal visit specification is universal per-block replay
acceptance. -/
theorem rollingBlockVisitSpecFrom_full_iff_allBlocks
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (initialSlabs : forall block : Fin (T / b + 1),
      WorkSlab (advertisedBlockWidth alpha.offsets block))
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit machine.State T)) :
    rollingBlockVisitSpecFrom machine input alpha initialSlabs blockVisits
        0 (T / b + 1) <->
      forall block : Fin (T / b + 1),
        FixedAlphaBlockVisitReplayAccepted machine input alpha block
          (initialSlabs block) (blockVisits block) := by
  rw [rollingBlockVisitSpecFrom_iff_range machine input alpha initialSlabs
    blockVisits 0 (T / b + 1) (by omega)]
  constructor
  · intro hall block
    exact hall block (by omega) (by omega)
  · intro hall block _ _
    exact hall block

/-- Global reflection of the actual increasing fold. -/
theorem inPlaceTwoWindowBlockFold_flags_reflect
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (initialSlabs : forall block : Fin (T / b + 1),
      WorkSlab (advertisedBlockWidth alpha.offsets block))
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit machine.State T))
    (globalCrossings : Fin T -> Nat)
    (hsteps : forall block : Fin (T / b + 1),
      fixedAlphaBlockVisitsTotalSteps (blockVisits block) <= T)
    (hadjacentLe : forall (bucket : Fin (T / b)) (candidate : Fin b),
      adjacentSourceBucketCrossingProfile machine input alpha initialSlabs
        blockVisits bucket candidate <= T)
    (hdecomposition : forall (bucket : Fin (T / b)) (candidate : Fin b),
      adjacentSourceBucketCrossingProfile machine input alpha initialSlabs
          blockVisits bucket candidate =
        globalCrossings (fullBucketBoundary bucket candidate)) :
    ((inPlaceTwoWindowBlockFold machine input alpha initialSlabs
          blockVisits).allBlockVisitsValid = true <->
        forall block : Fin (T / b + 1),
          FixedAlphaBlockVisitReplayAccepted machine input alpha block
            (initialSlabs block) (blockVisits block)) /\
      ((inPlaceTwoWindowBlockFold machine input alpha initialSlabs
          blockVisits).allClosedCutsValid = true <->
        forall bucket : Fin (T / b),
          AdvertisedCutOffsetIsLeftmostMinimum globalCrossings bucket
            (alpha.offsets bucket)) := by
  have hinitial : forall hblock : 0 < T / b + 1,
      RollingTwoWindowCarrierBeforeBlock machine input alpha initialSlabs
        blockVisits ⟨0, hblock⟩
        (initialInPlaceTwoWindowFoldState T b).counters := by
    intro hblock
    exact zeroCarrier_before_initialBlock machine input alpha initialSlabs
      blockVisits ⟨0, hblock⟩ rfl
  have hreflect := inPlaceTwoWindowBlockFoldFrom_flags_reflect machine input
    alpha initialSlabs blockVisits globalCrossings hsteps hadjacentLe
    hdecomposition 0 (T / b + 1)
    (initialInPlaceTwoWindowFoldState T b) hinitial
  constructor
  · unfold inPlaceTwoWindowBlockFold
    rw [hreflect.1,
      rollingBlockVisitSpecFrom_full_iff_allBlocks machine input alpha
        initialSlabs blockVisits]
    simp [initialInPlaceTwoWindowFoldState]
  · unfold inPlaceTwoWindowBlockFold
    rw [hreflect.2,
      rollingClosedCutSpecFrom_full_iff_allBuckets alpha.offsets
        globalCrossings]
    simp [initialInPlaceTwoWindowFoldState]

/-- Schedule-level global reflection against the actual run.  The only new
premise not supplied by schedule/all-block validity is the explicit
block-order decomposition statement. -/
theorem timedSchedule_inPlaceTwoWindowBlockFold_flags_reflect_actual
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha scheduled)
    (hdecomposition : TimedScheduleAdjacentSourceDecomposesActual
      machine input alpha scheduled) :
    ((inPlaceTwoWindowBlockFold machine input alpha
          (timedScheduleBlankBlockSlabs alpha)
          (timedScheduleBlockVisitFamily scheduled)).allBlockVisitsValid =
        true <->
      forall block : Fin (T / b + 1),
        FixedAlphaBlockVisitReplayAccepted machine input alpha block
          (timedScheduleBlankBlockSlabs alpha block)
          (timedScheduleBlockVisitFamily scheduled block)) /\
    ((inPlaceTwoWindowBlockFold machine input alpha
          (timedScheduleBlankBlockSlabs alpha)
          (timedScheduleBlockVisitFamily scheduled)).allClosedCutsValid =
        true <->
      forall bucket : Fin (T / b),
        AdvertisedCutOffsetIsLeftmostMinimum
          (actualWorkBoundaryCrossingProfile machine input T) bucket
          (alpha.offsets bucket)) := by
  exact inPlaceTwoWindowBlockFold_flags_reflect machine input alpha
    (timedScheduleBlankBlockSlabs alpha)
    (timedScheduleBlockVisitFamily scheduled)
    (actualWorkBoundaryCrossingProfile machine input T)
    (timedScheduleBlockVisitFamily_totalSteps_le_horizon machine alpha
      scheduled hschedule)
    (timedSchedule_adjacentSourceProfile_le_horizon machine input alpha
      scheduled hdecomposition)
    hdecomposition

/-- Under all-block validity, the combined global fold accepts exactly when
every advertised cut is the actual-run leftmost minimum. -/
theorem timedSchedule_inPlaceTwoWindowBlockFold_combined_eq_true_iff_actualCuts
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha scheduled)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha scheduled)
    (hdecomposition : TimedScheduleAdjacentSourceDecomposesActual
      machine input alpha scheduled) :
    (((inPlaceTwoWindowBlockFold machine input alpha
          (timedScheduleBlankBlockSlabs alpha)
          (timedScheduleBlockVisitFamily scheduled)).allBlockVisitsValid &&
      (inPlaceTwoWindowBlockFold machine input alpha
          (timedScheduleBlankBlockSlabs alpha)
          (timedScheduleBlockVisitFamily scheduled)).allClosedCutsValid) =
        true <->
      forall bucket : Fin (T / b),
        AdvertisedCutOffsetIsLeftmostMinimum
          (actualWorkBoundaryCrossingProfile machine input T) bucket
          (alpha.offsets bucket)) := by
  have hreflect :=
    timedSchedule_inPlaceTwoWindowBlockFold_flags_reflect_actual machine input
      alpha scheduled hschedule hdecomposition
  have hvisits : forall block : Fin (T / b + 1),
      FixedAlphaBlockVisitReplayAccepted machine input alpha block
        (timedScheduleBlankBlockSlabs alpha block)
        (timedScheduleBlockVisitFamily scheduled block) := by
    intro block
    exact (haccepted block).2
  have hvisitsCheck := hreflect.1.2 hvisits
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨_, hcuts⟩
    exact hreflect.2.1 hcuts
  · intro hcuts
    exact ⟨hvisitsCheck, hreflect.2.2 hcuts⟩

/-- With no full buckets, the unique edge block closes no cut and the global
cut flag is unconditionally true. -/
theorem inPlaceTwoWindowBlockFold_noFullBuckets_cutsValid
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (initialSlabs : forall block : Fin (T / b + 1),
      WorkSlab (advertisedBlockWidth alpha.offsets block))
    (blockVisits : forall _block : Fin (T / b + 1),
      List (FixedAlphaBlockVisit machine.State T))
    (hnoBuckets : T / b = 0) :
    (inPlaceTwoWindowBlockFold machine input alpha initialSlabs
      blockVisits).allClosedCutsValid = true := by
  unfold inPlaceTwoWindowBlockFold
  simp only [hnoBuckets, Nat.zero_add]
  simp [inPlaceTwoWindowBlockFoldFrom, inPlaceTwoWindowBlockStep,
    initialInPlaceTwoWindowFoldState, closeLeftBucketFromFirstWindowCheck]

end OneTapeMagnification
end Frontier
end Pnp4
