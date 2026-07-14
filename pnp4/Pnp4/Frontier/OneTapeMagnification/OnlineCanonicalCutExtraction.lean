import Mathlib.Tactic
import Mathlib.Data.List.MinMax
import Pnp4.Frontier.OneTapeMagnification.OnePassBoundaryCounterVector
import Pnp4.Frontier.OneTapeMagnification.AdvertisedCutMinimalityChecker
import Pnp4.Frontier.OneTapeMagnification.ExecutableTimedAlphaComponent

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Online extraction of one canonical cut

The coherent timed-alpha union is indexed in part by the leftmost
minimum-crossing cut in every full bucket.  This file isolates the part of an
online canonicalizer that can already be carried out without guessing an
alpha: for one fixed bucket, a single chronological pass through the actual
one-tape trajectory updates all `b` candidate counts simultaneously, and a
deterministic leftmost-minimum decoder recovers exactly the canonical offset.

The auxiliary counter carrier has exactly `(T + 1)^b` elements.  This count
does not include the configuration needed to generate the actual trajectory;
thus the construction is not yet a bounded-width input branching program.
In contrast, the
literal carrier obtained by retaining the exact counter vector for every
bucket has `(T + 1)^(b * (T / b))` elements.  The final lower bound below is
only for lossless retention of all of those counter vectors; it does not rule
out a geometry-aware compressed canonicalizer that retains less information.
No transcript, provider, generator, or unproved complexity premise occurs in
the definitions.
-/

/-! ## A deterministic leftmost minimum of one bounded vector -/

/-- Executable finite scan for the least offset attaining the minimum of one
bounded counter vector.  `List.argmin` scans `finRange b` from left to right
and replaces the incumbent only on a strict decrease, so equal counts retain
the earlier offset.  The fallback branch is unreachable under `hb`. -/
def leftmostBoundedCounterMinimumOffset {H b : Nat}
    (hb : 0 < b) (counters : BoundedCrossingCounterVector H b) : Fin b :=
  match (List.finRange b).argmin (fun candidate => (counters candidate).val) with
  | some offset => offset
  | none => ⟨0, hb⟩

/-- The executable scan really is the `argmin` result; in particular the
empty-list fallback cannot occur for positive `b`. -/
theorem argmin_boundedCounters_eq_some_leftmost {H b : Nat}
    (hb : 0 < b) (counters : BoundedCrossingCounterVector H b) :
    (List.finRange b).argmin (fun candidate => (counters candidate).val) =
      some (leftmostBoundedCounterMinimumOffset hb counters) := by
  cases harg :
      (List.finRange b).argmin (fun candidate => (counters candidate).val) with
  | none =>
      have hnil : List.finRange b = [] :=
        List.argmin_eq_none.mp harg
      have hlength := congrArg List.length hnil
      simp at hlength
      omega
  | some offset =>
      simp [leftmostBoundedCounterMinimumOffset, harg]

/-- The selected bounded counter is no larger than any candidate counter. -/
theorem leftmostBoundedCounterMinimumOffset_is_minimum {H b : Nat}
    (hb : 0 < b) (counters : BoundedCrossingCounterVector H b)
    (candidate : Fin b) :
    (counters (leftmostBoundedCounterMinimumOffset hb counters)).val ≤
      (counters candidate).val := by
  have harg := argmin_boundedCounters_eq_some_leftmost hb counters
  have hspec := List.argmin_eq_some_iff.mp harg
  exact hspec.2.1 candidate (List.mem_finRange candidate)

/-- Equal counter values are resolved toward the smaller offset. -/
theorem leftmostBoundedCounterMinimumOffset_tie_leftmost {H b : Nat}
    (hb : 0 < b) (counters : BoundedCrossingCounterVector H b)
    (candidate : Fin b)
    (htie : (counters candidate).val =
      (counters (leftmostBoundedCounterMinimumOffset hb counters)).val) :
    (leftmostBoundedCounterMinimumOffset hb counters).val ≤ candidate.val := by
  have harg := argmin_boundedCounters_eq_some_leftmost hb counters
  have hspec := List.argmin_eq_some_iff.mp harg
  have hindex := hspec.2.2 candidate (List.mem_finRange candidate)
    (Nat.le_of_eq htie)
  simpa using hindex

/-! ## One chronological pass for one full bucket -/

/-- The `b` physical boundaries belonging to one full bucket. -/
def fullBucketBoundaryFamily {T b : Nat}
    (bucket : Fin (T / b)) : Fin b → Nat :=
  fun offset => (fullBucketBoundary bucket offset).val

/-- Run the actual trajectory once and retain all `b` crossing counts of one
full bucket in the bounded finite carrier. -/
def onePassFullBucketCutCounters
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (bucket : Fin (T / b)) :
    BoundedCrossingCounterVector T b :=
  onePassBoundedCrossingCounterVectorFrom machine input
    (fullBucketBoundaryFamily bucket)
    (initialConfiguration machine) T
    (zeroBoundedCrossingCounterVector T b)

/-- Every coordinate of the one-bucket pass is the exact actual crossing
count of the corresponding physical boundary. -/
theorem onePassFullBucketCutCounters_apply_val_eq_actual
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (bucket : Fin (T / b)) (offset : Fin b) :
    (onePassFullBucketCutCounters machine input T b bucket offset).val =
      actualWorkBoundaryCrossingProfile machine input T
        (fullBucketBoundary bucket offset) := by
  unfold onePassFullBucketCutCounters
  rw [onePassBoundedCrossingCounterVectorFrom_zero_apply_val_eq
    machine input (fullBucketBoundaryFamily bucket)
    (initialConfiguration machine) T le_rfl offset]
  rfl

/-- Decode the leftmost minimum after the one-bucket online pass. -/
def onePassCanonicalBoundaryOffset
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) (bucket : Fin (T / b)) : Fin b :=
  leftmostBoundedCounterMinimumOffset hb
    (onePassFullBucketCutCounters machine input T b bucket)

/-- **Exact online cut extraction.**  The bounded one-pass decoder returns
the same offset as the semantic canonical-boundary definition on the actual
one-tape crossing profile. -/
theorem onePassCanonicalBoundaryOffset_eq_actual
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) (bucket : Fin (T / b)) :
    onePassCanonicalBoundaryOffset machine input T b hb bucket =
      canonicalBoundaryOffset hb
        (actualWorkBoundaryCrossingProfile machine input T) bucket := by
  apply
    (advertisedCutOffsetIsLeftmostMinimum_iff_eq_canonicalBoundaryOffset
      hb (actualWorkBoundaryCrossingProfile machine input T) bucket
      (onePassCanonicalBoundaryOffset machine input T b hb bucket)).1
  constructor
  · intro candidate
    rw [← onePassFullBucketCutCounters_apply_val_eq_actual
      machine input T b bucket
        (onePassCanonicalBoundaryOffset machine input T b hb bucket),
      ← onePassFullBucketCutCounters_apply_val_eq_actual
        machine input T b bucket candidate]
    exact leftmostBoundedCounterMinimumOffset_is_minimum hb
      (onePassFullBucketCutCounters machine input T b bucket) candidate
  · intro candidate htie
    apply leftmostBoundedCounterMinimumOffset_tie_leftmost hb
      (onePassFullBucketCutCounters machine input T b bucket) candidate
    rw [onePassFullBucketCutCounters_apply_val_eq_actual,
      onePassFullBucketCutCounters_apply_val_eq_actual]
    exact htie

/-- Applying the one-bucket extractor independently to every full bucket
recovers the complete canonical cut-offset vector extensionally.  This is a
semantic composition theorem, not a claim that the passes have already been
serialized through one small live carrier. -/
def onePassCanonicalCutOffsets
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) : CanonicalCutOffsets T b :=
  fun bucket => onePassCanonicalBoundaryOffset machine input T b hb bucket

theorem onePassCanonicalCutOffsets_eq_canonical
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    onePassCanonicalCutOffsets machine input T b hb =
      canonicalCutOffsets machine input T b hb := by
  funext bucket
  exact onePassCanonicalBoundaryOffset_eq_actual
    machine input T b hb bucket

/-! ## Exact carrier accounting and the parallel-retention barrier -/

/-- One bucket's bounded online counter carrier has exactly `(T + 1)^b`
states. -/
theorem card_boundedCrossingCounterVector (T b : Nat) :
    Fintype.card (BoundedCrossingCounterVector T b) = (T + 1) ^ b := by
  simp [BoundedCrossingCounterVector]

/-- Literal simultaneous retention of every bucket's exact `b`-counter
vector. -/
abbrev AllFullBucketCounterVectors (T b : Nat) :=
  Fin (T / b) → BoundedCrossingCounterVector T b

/-- Zero initialization for every bucket's bounded counter vector. -/
def zeroAllFullBucketCounterVectors (T b : Nat) :
    AllFullBucketCounterVectors T b :=
  fun _ => zeroBoundedCrossingCounterVector T b

/-- One physical work-head move updates every bucket's candidate counters.
Although written as a nested finite function, this is one simultaneous state
transition, not a family of semantic replays. -/
def bumpAllFullBucketCounterVectors {T b : Nat}
    (fromHead toHead : Nat) (counters : AllFullBucketCounterVectors T b) :
    AllFullBucketCounterVectors T b :=
  fun bucket =>
    bumpBoundedCrossingCounterVector (fullBucketBoundaryFamily bucket)
      fromHead toHead (counters bucket)

/-- The auxiliary online transition is closed on the counted counter carrier:
it consumes only the two externally supplied work-head positions and stores
no machine configuration.  Producing those positions is deliberately not
included in this carrier claim. -/
@[simp]
theorem bumpAllFullBucketCounterVectors_apply {T b : Nat}
    (fromHead toHead : Nat) (counters : AllFullBucketCounterVectors T b)
    (bucket : Fin (T / b)) :
    bumpAllFullBucketCounterVectors fromHead toHead counters bucket =
      bumpBoundedCrossingCounterVector (fullBucketBoundaryFamily bucket)
        fromHead toHead (counters bucket) :=
  rfl

/-- One chronological trajectory pass with the literal all-bucket counter
carrier. -/
def onePassAllFullBucketCounterVectorsFrom
    (machine : DeterministicMachine) (input : List Bool) (T b : Nat) :
    Configuration machine.State → Nat → AllFullBucketCounterVectors T b →
      AllFullBucketCounterVectors T b
  | _, 0, counters => counters
  | config, steps + 1, counters =>
      let next := step machine input config
      onePassAllFullBucketCounterVectorsFrom machine input T b next steps
        (bumpAllFullBucketCounterVectors config.workHead next.workHead counters)

/-- Projection to one bucket commutes exactly with the simultaneous pass. -/
theorem onePassAllFullBucketCounterVectorsFrom_apply
    (machine : DeterministicMachine) (input : List Bool) (T b : Nat)
    (config : Configuration machine.State) (steps : Nat)
    (initial : AllFullBucketCounterVectors T b)
    (bucket : Fin (T / b)) :
    onePassAllFullBucketCounterVectorsFrom machine input T b config steps
        initial bucket =
      onePassBoundedCrossingCounterVectorFrom machine input
        (fullBucketBoundaryFamily bucket) config steps (initial bucket) := by
  induction steps generalizing config initial with
  | zero => rfl
  | succ steps ih =>
      simp only [onePassAllFullBucketCounterVectorsFrom,
        onePassBoundedCrossingCounterVectorFrom]
      rw [ih]
      rfl

/-- The concrete zero-start simultaneous pass over the first `T`
transitions. -/
def onePassAllFullBucketCutCounters
    (machine : DeterministicMachine) (input : List Bool) (T b : Nat) :
    AllFullBucketCounterVectors T b :=
  onePassAllFullBucketCounterVectorsFrom machine input T b
    (initialConfiguration machine) T
    (zeroAllFullBucketCounterVectors T b)

/-- Each bucket projection of the simultaneous pass is definitionally the
same exact bounded pass used by the one-cut extractor. -/
theorem onePassAllFullBucketCutCounters_apply_eq_onePass
    (machine : DeterministicMachine) (input : List Bool) (T b : Nat)
    (bucket : Fin (T / b)) :
    onePassAllFullBucketCutCounters machine input T b bucket =
      onePassFullBucketCutCounters machine input T b bucket := by
  unfold onePassAllFullBucketCutCounters onePassFullBucketCutCounters
  rw [onePassAllFullBucketCounterVectorsFrom_apply]
  rfl

/-- Coordinatewise correctness of the literal single-pass all-bucket
counter state. -/
theorem onePassAllFullBucketCutCounters_apply_val_eq_actual
    (machine : DeterministicMachine) (input : List Bool) (T b : Nat)
    (bucket : Fin (T / b)) (offset : Fin b) :
    (onePassAllFullBucketCutCounters machine input T b bucket offset).val =
      actualWorkBoundaryCrossingProfile machine input T
        (fullBucketBoundary bucket offset) := by
  rw [onePassAllFullBucketCutCounters_apply_eq_onePass]
  exact onePassFullBucketCutCounters_apply_val_eq_actual
    machine input T b bucket offset

/-- Decode one leftmost-minimum offset per bucket from a simultaneous exact
counter state. -/
def canonicalCutOffsetsOfAllFullBucketCounters
    {T b : Nat} (hb : 0 < b) (counters : AllFullBucketCounterVectors T b) :
    CanonicalCutOffsets T b :=
  fun bucket => leftmostBoundedCounterMinimumOffset hb (counters bucket)

/-- The complete cut vector produced by the literal one-pass trajectory-side
canonicalizer. -/
def onePassAllCanonicalCutOffsets
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) : CanonicalCutOffsets T b :=
  canonicalCutOffsetsOfAllFullBucketCounters hb
    (onePassAllFullBucketCutCounters machine input T b)

/-- **Exact simultaneous trajectory-side cut canonicalization.**  A single
fused pass through the work-head trajectory recovers every canonical cut
offset.  Generating that trajectory in small state remains a separate issue. -/
theorem onePassAllCanonicalCutOffsets_eq_canonical
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    onePassAllCanonicalCutOffsets machine input T b hb =
      canonicalCutOffsets machine input T b hb := by
  funext bucket
  unfold onePassAllCanonicalCutOffsets
    canonicalCutOffsetsOfAllFullBucketCounters
  rw [onePassAllFullBucketCutCounters_apply_eq_onePass]
  exact onePassCanonicalBoundaryOffset_eq_actual
    machine input T b hb bucket

/-- The cut field of the unique component accepted by the coherent canonical
checker is exactly the output of the simultaneous online cut extractor.  In
particular this conclusion does not enumerate or black-box query alpha
components. -/
theorem timedAlphaCanonicalComponentCheck_true_offsets_eq_onePassAll
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (hcheck : timedAlphaCanonicalComponentCheck
      machine input T b hb alpha = true) :
    alpha.offsets = onePassAllCanonicalCutOffsets machine input T b hb := by
  have halpha :=
    (timedAlphaCanonicalComponentCheck_eq_true_iff
      machine input T b hb alpha).1 hcheck
  subst alpha
  rw [onePassAllCanonicalCutOffsets_eq_canonical]
  rfl

/-- Exact size of the naive all-bucket counter carrier. -/
theorem card_allFullBucketCounterVectors (T b : Nat) :
    Fintype.card (AllFullBucketCounterVectors T b) =
      (T + 1) ^ (b * (T / b)) := by
  rw [Fintype.card_fun, Fintype.card_fin,
    card_boundedCrossingCounterVector, ← Nat.pow_mul]

/-- Any finite state space that losslessly encodes every literal all-bucket
counter vector must be at least as large as that carrier.  The premise is an
explicit left inverse, not a hidden canonicalizer assumption; a successful
compressed construction may evade the conclusion by not retaining all exact
counters. -/
theorem allFullBucketCounterVectors_card_le_of_leftInverse
    (T b : Nat) (State : Type) [Fintype State]
    (encode : AllFullBucketCounterVectors T b → State)
    (decode : State → AllFullBucketCounterVectors T b)
    (hleft : Function.LeftInverse decode encode) :
    (T + 1) ^ (b * (T / b)) ≤ Fintype.card State := by
  rw [← card_allFullBucketCounterVectors T b]
  exact Fintype.card_le_of_injective encode hleft.injective

end OneTapeMagnification
end Frontier
end Pnp4
