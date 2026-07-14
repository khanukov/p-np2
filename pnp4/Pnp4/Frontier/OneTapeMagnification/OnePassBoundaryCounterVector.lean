import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FixedAlphaCutCounterReplay

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# One-pass vector of work-boundary crossing counters

The earlier executable cut checker obtains one coordinate of the crossing
profile by replaying a trajectory for that named boundary.  Calling it for
many candidates would reread the same input.  Here all named boundaries are
updated together during one recursive pass through the trajectory.

The first implementation uses natural counters and is proved coordinatewise
equal to `streamingWorkBoundaryCrossingCountFrom`.  The second implementation
stores every coordinate in `Fin (H + 1)` and uses a saturating increment.  If
the pass has at most `H` steps and starts from zero, saturation is unreachable,
so the bounded finite vector is exactly the same crossing profile.

This removes the repeated-per-boundary replay at the counter level.  It does
not yet fuse the vector with local slab replay or construct the fixed-alpha
read-once branching program.
-/

/-- An unbounded vector of crossing counters for `m` named boundaries. -/
abbrev CrossingCounterVector (m : Nat) := Fin m → Nat

/-- Update every named coordinate for one pair of work-head positions. -/
def bumpCrossingCounterVector {m : Nat}
    (boundaries : Fin m → Nat) (fromHead toHead : Nat)
    (counters : CrossingCounterVector m) : CrossingCounterVector m :=
  fun i => counters i +
    if CrossesWorkBoundary (boundaries i) fromHead toHead then 1 else 0

/-- Follow one deterministic trajectory once, updating all named boundaries
at each transition. -/
def onePassCrossingCounterVectorFrom
    (machine : DeterministicMachine) (input : List Bool) {m : Nat}
    (boundaries : Fin m → Nat) :
    Configuration machine.State → Nat → CrossingCounterVector m →
      CrossingCounterVector m
  | _, 0, counters => counters
  | config, steps + 1, counters =>
      let next := step machine input config
      onePassCrossingCounterVectorFrom machine input boundaries next steps
        (bumpCrossingCounterVector boundaries
          config.workHead next.workHead counters)

/-- The fused vector pass is exactly the old streaming specification in every
coordinate, plus that coordinate's supplied initial value. -/
theorem onePassCrossingCounterVectorFrom_apply
    (machine : DeterministicMachine) (input : List Bool) {m : Nat}
    (boundaries : Fin m → Nat) (config : Configuration machine.State)
    (steps : Nat) (initial : CrossingCounterVector m) (i : Fin m) :
    onePassCrossingCounterVectorFrom machine input boundaries
        config steps initial i =
      initial i + streamingWorkBoundaryCrossingCountFrom
        machine input config steps (boundaries i) := by
  induction steps generalizing config initial with
  | zero =>
      simp [onePassCrossingCounterVectorFrom,
        streamingWorkBoundaryCrossingCountFrom]
  | succ steps ih =>
      simp only [onePassCrossingCounterVectorFrom]
      rw [ih]
      simp only [bumpCrossingCounterVector,
        streamingWorkBoundaryCrossingCountFrom]
      omega

/-- Starting from zero, the fused vector pass recovers the finite-sum crossing
count specification at every named boundary. -/
theorem onePassCrossingCounterVectorFrom_zero_apply_eq
    (machine : DeterministicMachine) (input : List Bool) {m : Nat}
    (boundaries : Fin m → Nat) (config : Configuration machine.State)
    (steps : Nat) (i : Fin m) :
    onePassCrossingCounterVectorFrom machine input boundaries config steps
        (fun _ => 0) i =
      workBoundaryCrossingCountFrom machine input config steps
        (boundaries i) := by
  rw [onePassCrossingCounterVectorFrom_apply,
    streamingWorkBoundaryCrossingCountFrom_eq]
  simp

/-- Finite crossing-counter vector at horizon `H`. -/
abbrev BoundedCrossingCounterVector (H m : Nat) := Fin m → Fin (H + 1)

/-- The all-zero bounded vector. -/
def zeroBoundedCrossingCounterVector (H m : Nat) :
    BoundedCrossingCounterVector H m :=
  fun _ => ⟨0, by omega⟩

/-- Saturating one-transition update in the finite carrier.  The exactness
theorem below proves that saturation is never reached on a zero-start pass of
length at most `H`. -/
def bumpBoundedCrossingCounterVector {H m : Nat}
    (boundaries : Fin m → Nat) (fromHead toHead : Nat)
    (counters : BoundedCrossingCounterVector H m) :
    BoundedCrossingCounterVector H m :=
  fun i =>
    ⟨min ((counters i).val +
        if CrossesWorkBoundary (boundaries i) fromHead toHead then 1 else 0) H,
      by
        have hle : min ((counters i).val +
            if CrossesWorkBoundary (boundaries i) fromHead toHead then 1 else 0)
              H ≤ H := min_le_right _ _
        omega⟩

/-- Bounded fused trajectory pass. -/
def onePassBoundedCrossingCounterVectorFrom
    (machine : DeterministicMachine) (input : List Bool) {H m : Nat}
    (boundaries : Fin m → Nat) :
    Configuration machine.State → Nat → BoundedCrossingCounterVector H m →
      BoundedCrossingCounterVector H m
  | _, 0, counters => counters
  | config, steps + 1, counters =>
      let next := step machine input config
      onePassBoundedCrossingCounterVectorFrom machine input boundaries
        next steps
        (bumpBoundedCrossingCounterVector boundaries
          config.workHead next.workHead counters)

/-- With enough remaining horizon for every coordinate, the bounded pass is
coordinatewise exact and therefore never uses its saturating branch. -/
theorem onePassBoundedCrossingCounterVectorFrom_apply_val
    (machine : DeterministicMachine) (input : List Bool) {H m : Nat}
    (boundaries : Fin m → Nat) (config : Configuration machine.State)
    (steps : Nat) (initial : BoundedCrossingCounterVector H m)
    (hroom : ∀ i, (initial i).val + steps ≤ H) (i : Fin m) :
    (onePassBoundedCrossingCounterVectorFrom machine input boundaries
        config steps initial i).val =
      (initial i).val + streamingWorkBoundaryCrossingCountFrom
        machine input config steps (boundaries i) := by
  induction steps generalizing config initial with
  | zero =>
      simp [onePassBoundedCrossingCounterVectorFrom,
        streamingWorkBoundaryCrossingCountFrom]
  | succ steps ih =>
      let next := step machine input config
      let bumped := bumpBoundedCrossingCounterVector boundaries
        config.workHead next.workHead initial
      have hbumpVal : ∀ j,
          (bumped j).val = (initial j).val +
            if CrossesWorkBoundary (boundaries j)
                config.workHead next.workHead then 1 else 0 := by
        intro j
        have hle : (initial j).val +
            (if CrossesWorkBoundary (boundaries j)
                config.workHead next.workHead then 1 else 0) ≤ H := by
          have := hroom j
          split <;> omega
        simp [bumped, bumpBoundedCrossingCounterVector,
          min_eq_left hle]
      have htailRoom : ∀ j, (bumped j).val + steps ≤ H := by
        intro j
        rw [hbumpVal]
        have := hroom j
        split <;> omega
      change
        (onePassBoundedCrossingCounterVectorFrom machine input boundaries
          next steps bumped i).val = _
      rw [ih next bumped htailRoom, hbumpVal]
      simp only [streamingWorkBoundaryCrossingCountFrom]
      simp only [next]
      omega

/-- A zero-start bounded pass of length at most `H` exactly recovers every
named work-boundary crossing count. -/
theorem onePassBoundedCrossingCounterVectorFrom_zero_apply_val_eq
    (machine : DeterministicMachine) (input : List Bool) {H m : Nat}
    (boundaries : Fin m → Nat) (config : Configuration machine.State)
    (steps : Nat) (hsteps : steps ≤ H) (i : Fin m) :
    (onePassBoundedCrossingCounterVectorFrom machine input boundaries
        config steps (zeroBoundedCrossingCounterVector H m) i).val =
      workBoundaryCrossingCountFrom machine input config steps
        (boundaries i) := by
  rw [onePassBoundedCrossingCounterVectorFrom_apply_val machine input
    boundaries config steps (zeroBoundedCrossingCounterVector H m)
    (by
      intro j
      simp [zeroBoundedCrossingCounterVector, hsteps]) i,
    streamingWorkBoundaryCrossingCountFrom_eq]
  simp [zeroBoundedCrossingCounterVector]

/-- The `2b` candidate cuts of two adjacent full buckets, packed into one
fixed vector. -/
def adjacentFullBucketBoundaries {T b : Nat}
    (left right : Fin (T / b)) : Fin (b + b) → Fin T :=
  Fin.addCases
    (fun offset => fullBucketBoundary left offset)
    (fun offset => fullBucketBoundary right offset)

@[simp]
theorem adjacentFullBucketBoundaries_left {T b : Nat}
    (left right : Fin (T / b)) (offset : Fin b) :
    adjacentFullBucketBoundaries left right (Fin.castAdd b offset) =
      fullBucketBoundary left offset := by
  exact Fin.addCases_left offset

@[simp]
theorem adjacentFullBucketBoundaries_right {T b : Nat}
    (left right : Fin (T / b)) (offset : Fin b) :
    adjacentFullBucketBoundaries left right (Fin.natAdd b offset) =
      fullBucketBoundary right offset := by
  exact Fin.addCases_right offset

/-- One zero-start pass over the first `T` transitions computes all candidates
from both adjacent buckets in the finite `(T + 1)^(2b)` carrier. -/
def onePassAdjacentBucketCutCounters
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (left right : Fin (T / b)) :
    BoundedCrossingCounterVector T (b + b) :=
  onePassBoundedCrossingCounterVectorFrom machine input
    (fun i => (adjacentFullBucketBoundaries left right i).val)
    (initialConfiguration machine) T
    (zeroBoundedCrossingCounterVector T (b + b))

/-- Every coordinate of the fused adjacent-bucket pass is the exact actual
crossing profile. -/
theorem onePassAdjacentBucketCutCounters_apply_val_eq_actual
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (left right : Fin (T / b)) (i : Fin (b + b)) :
    (onePassAdjacentBucketCutCounters
      machine input T b left right i).val =
      actualWorkBoundaryCrossingProfile machine input T
        (adjacentFullBucketBoundaries left right i) := by
  unfold onePassAdjacentBucketCutCounters
  rw [onePassBoundedCrossingCounterVectorFrom_zero_apply_val_eq
    machine input
      (fun i => (adjacentFullBucketBoundaries left right i).val)
      (initialConfiguration machine) T le_rfl i]
  rfl

/-- Left-bucket specialization of the fused pass. -/
theorem onePassAdjacentBucketCutCounters_left_val_eq_actual
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (left right : Fin (T / b)) (offset : Fin b) :
    (onePassAdjacentBucketCutCounters machine input T b left right
      (Fin.castAdd b offset)).val =
      actualWorkBoundaryCrossingProfile machine input T
        (fullBucketBoundary left offset) := by
  simpa using onePassAdjacentBucketCutCounters_apply_val_eq_actual
    machine input T b left right (Fin.castAdd b offset)

/-- Right-bucket specialization of the fused pass. -/
theorem onePassAdjacentBucketCutCounters_right_val_eq_actual
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (left right : Fin (T / b)) (offset : Fin b) :
    (onePassAdjacentBucketCutCounters machine input T b left right
      (Fin.natAdd b offset)).val =
      actualWorkBoundaryCrossingProfile machine input T
        (fullBucketBoundary right offset) := by
  calc
    (onePassAdjacentBucketCutCounters machine input T b left right
        (Fin.natAdd b offset)).val =
        actualWorkBoundaryCrossingProfile machine input T
          (adjacentFullBucketBoundaries left right
            (Fin.natAdd b offset)) :=
      onePassAdjacentBucketCutCounters_apply_val_eq_actual
        machine input T b left right (Fin.natAdd b offset)
    _ = actualWorkBoundaryCrossingProfile machine input T
          (fullBucketBoundary right offset) :=
      congrArg (actualWorkBoundaryCrossingProfile machine input T)
        (adjacentFullBucketBoundaries_right left right offset)

end OneTapeMagnification
end Frontier
end Pnp4
