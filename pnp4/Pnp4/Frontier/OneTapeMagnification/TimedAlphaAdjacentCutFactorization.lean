import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.InPlaceTwoWindowScheduleClosure
import Pnp4.Frontier.OneTapeMagnification.ExecutableInPlaceTimedAlphaComponent
import Pnp4.Frontier.OneTapeMagnification.TimedAlphaBlockwisePathSplicing
import Pnp4.Frontier.OneTapeMagnification.TimedAlphaBlockCrossingPathCongruence
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanMaskedProductFactorization

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

open scoped BigOperators

/-!
# Nearest-neighbour factorization of timed-alpha cut canonicality

The accepted replay predicate factors over disjoint advertised block paths,
but canonical cut selection is not itself a product predicate.  Its remaining
interaction is nevertheless local: the crossing profile of one full bucket
is the sum of the contributions of exactly the two source blocks adjacent to
that bucket.  Consequently the complete leftmost-minimum check is a path of
nearest-neighbour factors, one factor per full bucket.

This file states and proves that factorization directly against
`canonicalCutOffsets`.  There is no cut-stability, splice, or correlation
hypothesis.  The result is the semantic separator interface needed before a
prefix/suffix splice can reduce canonicality to its single seam factor.
-/

/-- The crossing-count vector seen by one advertised cut, reconstructed only
from the two source blocks adjacent to its bucket. -/
def timedScheduleAdjacentBucketCrossingVector
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (bucket : Fin (T / b)) : Fin b → Nat :=
  fun candidate =>
    adjacentSourceBucketCrossingProfile machine input alpha
      (timedScheduleBlankBlockSlabs alpha)
      (timedScheduleBlockVisitFamily scheduled) bucket candidate

/-- One nearest-neighbour cut factor.  Strict comparison is retained on the
left of the advertised offset and weak comparison on the right, exactly
encoding leftmost tie-breaking. -/
def TimedScheduleAdjacentCutIsLeftmostMinimum
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (bucket : Fin (T / b)) : Prop :=
  let crossings := timedScheduleAdjacentBucketCrossingVector
    machine input alpha scheduled bucket
  OneSidedLeftmostMinimum
    (crossings (alpha.offsets bucket)) (alpha.offsets bucket) crossings

/-- The full path-factor predicate: every edge between consecutive advertised
work blocks passes its adjacent-source leftmost-minimum test. -/
def TimedScheduleAllAdjacentCutsAreLeftmostMinimum
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b)) : Prop :=
  ∀ bucket : Fin (T / b),
    TimedScheduleAdjacentCutIsLeftmostMinimum
      machine input alpha scheduled bucket

/-- Unary input factor for one advertised work block. -/
def TimedScheduleBlockReplayAcceptedFromBlank
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (block : Fin (T / b + 1)) : Prop :=
  FixedAlphaBlockVisitListAcceptedFromBlank machine input alpha block
    (timedAlphaBlockVisits block scheduled)

/-- Rational `0/1` indicator of a finite proposition. -/
noncomputable def finiteRatPropIndicator (proposition : Prop) : Rat :=
  @ite Rat proposition (Classical.propDecidable proposition) 1 0

/-- A universal finite indicator is the product of its pointwise indicators,
including the empty-index case. -/
theorem finiteRatPropIndicator_forall_eq_prod
    {Index : Type*} [Fintype Index] (predicate : Index → Prop) :
    finiteRatPropIndicator (∀ index, predicate index) =
      ∏ index, finiteRatPropIndicator (predicate index) := by
  classical
  by_cases hall : ∀ index, predicate index
  · simp [finiteRatPropIndicator, hall]
  · rw [finiteRatPropIndicator]
    simp only [hall, if_false]
    obtain ⟨index, hindex⟩ := not_forall.mp hall
    apply Eq.symm
    apply Finset.prod_eq_zero (Finset.mem_univ index)
    simp [finiteRatPropIndicator, hindex]

/-- Finite dependency set of one cached scheduled block replay. -/
def finiteCachedTimedScheduleBlockQuerySupport
    {State : Type} (n : Nat) {T b : Nat}
    (scheduled : List (TimedAlphaScheduledVisit State T b))
    (block : Fin (T / b + 1)) : Finset (Fin n) :=
  (finiteCachedBlockVisitListAdvertisedQueryOrder n
    (timedAlphaBlockVisits block scheduled)).toFinset

/-- Rational unary factor for one cached-machine scheduled block. -/
noncomputable def finiteCachedTimedScheduleBlockReplayRatFactor
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (block : Fin (T / b + 1)) : (Fin n → Bool) → Rat :=
  fun input => finiteRatPropIndicator
    (TimedScheduleBlockReplayAcceptedFromBlank
      (cachedInputMachine machine) (List.ofFn input) alpha scheduled block)

/-- The unary replay factor depends only on its exact advertised block path.
This is a genuine two-sided locality statement, obtained by applying the
cross-input path cylinder in both directions. -/
theorem finiteCachedTimedScheduleBlockReplayRatFactor_dependsOnlyOn
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (block : Fin (T / b + 1)) :
    FiniteBooleanFourier.DependsOnlyOn
      (finiteCachedTimedScheduleBlockQuerySupport n scheduled block)
      (finiteCachedTimedScheduleBlockReplayRatFactor
        machine alpha scheduled block) := by
  intro left right hagree
  let visits := timedAlphaBlockVisits block scheduled
  let initialSlab := blankWorkSlab
    (advertisedBlockWidth alpha.offsets block)
  have hagreeForward : ∀ coordinate ∈
      finiteCachedBlockVisitListAdvertisedQueryOrder n visits,
        right coordinate = left coordinate := by
    intro coordinate hcoordinate
    exact (hagree coordinate (by
      simpa [finiteCachedTimedScheduleBlockQuerySupport, visits] using
        hcoordinate)).symm
  have hagreeBackward : ∀ coordinate ∈
      finiteCachedBlockVisitListAdvertisedQueryOrder n visits,
        left coordinate = right coordinate := by
    intro coordinate hcoordinate
    exact hagree coordinate (by
      simpa [finiteCachedTimedScheduleBlockQuerySupport, visits] using
        hcoordinate)
  have hforward :
      TimedScheduleBlockReplayAcceptedFromBlank
          (cachedInputMachine machine) (List.ofFn left) alpha scheduled block →
        TimedScheduleBlockReplayAcceptedFromBlank
          (cachedInputMachine machine) (List.ofFn right) alpha scheduled block := by
    rintro ⟨hchronological, hreplay⟩
    refine ⟨hchronological, ?_⟩
    exact fixedAlphaBlockVisitReplayAccepted_of_advertisedAgreement
      machine alpha block initialSlab visits left right
        (by simpa [initialSlab, visits] using hreplay) hagreeForward
  have hbackward :
      TimedScheduleBlockReplayAcceptedFromBlank
          (cachedInputMachine machine) (List.ofFn right) alpha scheduled block →
        TimedScheduleBlockReplayAcceptedFromBlank
          (cachedInputMachine machine) (List.ofFn left) alpha scheduled block := by
    rintro ⟨hchronological, hreplay⟩
    refine ⟨hchronological, ?_⟩
    exact fixedAlphaBlockVisitReplayAccepted_of_advertisedAgreement
      machine alpha block initialSlab visits right left
        (by simpa [initialSlab, visits] using hreplay) hagreeBackward
  by_cases hleft : TimedScheduleBlockReplayAcceptedFromBlank
      (cachedInputMachine machine) (List.ofFn left) alpha scheduled block
  · have hright := hforward hleft
    simp [finiteCachedTimedScheduleBlockReplayRatFactor,
      finiteRatPropIndicator, hleft, hright]
  · have hright : ¬ TimedScheduleBlockReplayAcceptedFromBlank
        (cachedInputMachine machine) (List.ofFn right) alpha scheduled block :=
      fun h => hleft (hbackward h)
    simp [finiteCachedTimedScheduleBlockReplayRatFactor,
      finiteRatPropIndicator, hleft, hright]

/-- Exact query support of one adjacent selector pair: the union of the two
advertised paths on the sides of its cut. -/
def finiteCachedTimedScheduleAdjacentCutQuerySupport
    {State : Type} (n : Nat) {T b : Nat}
    (scheduled : List (TimedAlphaScheduledVisit State T b))
    (bucket : Fin (T / b)) : Finset (Fin n) :=
  finiteCachedTimedScheduleBlockQuerySupport n scheduled
      (leftSourceBlockOfBucket bucket) ∪
    finiteCachedTimedScheduleBlockQuerySupport n scheduled
      (rightSourceBlockOfBucket bucket)

/-- Rational `0/1` factor of one adjacent leftmost-minimum selector pair. -/
noncomputable def finiteCachedTimedScheduleAdjacentCutRatFactor
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (bucket : Fin (T / b)) : (Fin n → Bool) → Rat :=
  fun input => finiteRatPropIndicator
    (TimedScheduleAdjacentCutIsLeftmostMinimum
      (cachedInputMachine machine) (List.ofFn input) alpha scheduled bucket)

/-- If the source input passes both adjacent replay checks, then the raw
selector-pair factor is fixed by the union of the two advertised paths.
The replay hypotheses are used only to certify the exact semantic crossing
profiles; no canonical-offset or cut-stability hypothesis is present. -/
theorem finiteCachedTimedScheduleAdjacentCutRatFactor_eq_of_pathAgreement
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (source candidate : Fin n → Bool)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (bucket : Fin (T / b))
    (hleft : TimedScheduleBlockReplayAcceptedFromBlank
      (cachedInputMachine machine) (List.ofFn source) alpha scheduled
        (leftSourceBlockOfBucket bucket))
    (hright : TimedScheduleBlockReplayAcceptedFromBlank
      (cachedInputMachine machine) (List.ofFn source) alpha scheduled
        (rightSourceBlockOfBucket bucket))
    (hagree : ∀ coordinate ∈
      finiteCachedTimedScheduleAdjacentCutQuerySupport n scheduled bucket,
        candidate coordinate = source coordinate) :
    finiteCachedTimedScheduleAdjacentCutRatFactor
        machine alpha scheduled bucket candidate =
      finiteCachedTimedScheduleAdjacentCutRatFactor
        machine alpha scheduled bucket source := by
  let left := leftSourceBlockOfBucket bucket
  let right := rightSourceBlockOfBucket bucket
  let leftVisits := timedAlphaBlockVisits left scheduled
  let rightVisits := timedAlphaBlockVisits right scheduled
  have hagreeLeft : ∀ coordinate ∈
      finiteCachedBlockVisitListAdvertisedQueryOrder n leftVisits,
        candidate coordinate = source coordinate := by
    intro coordinate hcoordinate
    apply hagree coordinate
    simp [finiteCachedTimedScheduleAdjacentCutQuerySupport,
      finiteCachedTimedScheduleBlockQuerySupport, left, leftVisits,
      hcoordinate]
  have hagreeRight : ∀ coordinate ∈
      finiteCachedBlockVisitListAdvertisedQueryOrder n rightVisits,
        candidate coordinate = source coordinate := by
    intro coordinate hcoordinate
    apply hagree coordinate
    simp [finiteCachedTimedScheduleAdjacentCutQuerySupport,
      finiteCachedTimedScheduleBlockQuerySupport, right, rightVisits,
      hcoordinate]
  have hleftProfile :=
    fixedAlphaBlockVisitListCrossingProfile_eq_of_pathAgreement
      machine source candidate alpha left
        (blankWorkSlab (advertisedBlockWidth alpha.offsets left)) leftVisits
        (by simpa [TimedScheduleBlockReplayAcceptedFromBlank,
          FixedAlphaBlockVisitListAcceptedFromBlank, left, leftVisits] using
            hleft.2)
        hagreeLeft
        (fixedAlphaBlockVisitsTotalSteps_le_horizon leftVisits hleft.1)
  have hrightProfile :=
    fixedAlphaBlockVisitListCrossingProfile_eq_of_pathAgreement
      machine source candidate alpha right
        (blankWorkSlab (advertisedBlockWidth alpha.offsets right)) rightVisits
        (by simpa [TimedScheduleBlockReplayAcceptedFromBlank,
          FixedAlphaBlockVisitListAcceptedFromBlank, right, rightVisits] using
            hright.2)
        hagreeRight
        (fixedAlphaBlockVisitsTotalSteps_le_horizon rightVisits hright.1)
  have hvectors :
      timedScheduleAdjacentBucketCrossingVector
          (cachedInputMachine machine) (List.ofFn candidate) alpha scheduled
            bucket =
        timedScheduleAdjacentBucketCrossingVector
          (cachedInputMachine machine) (List.ofFn source) alpha scheduled
            bucket := by
    funext offset
    unfold timedScheduleAdjacentBucketCrossingVector
      adjacentSourceBucketCrossingProfile
      fixedAlphaSourceBlockCrossingContribution
      timedScheduleBlankBlockSlabs timedScheduleBlockVisitFamily
    change
      fixedAlphaBlockVisitListCrossingProfile
            (cachedInputMachine machine) (List.ofFn candidate) alpha left
            (blankWorkSlab (advertisedBlockWidth alpha.offsets left))
            leftVisits (fullBucketBoundary bucket offset) +
          fixedAlphaBlockVisitListCrossingProfile
            (cachedInputMachine machine) (List.ofFn candidate) alpha right
            (blankWorkSlab (advertisedBlockWidth alpha.offsets right))
            rightVisits (fullBucketBoundary bucket offset) =
        fixedAlphaBlockVisitListCrossingProfile
            (cachedInputMachine machine) (List.ofFn source) alpha left
            (blankWorkSlab (advertisedBlockWidth alpha.offsets left))
            leftVisits (fullBucketBoundary bucket offset) +
          fixedAlphaBlockVisitListCrossingProfile
            (cachedInputMachine machine) (List.ofFn source) alpha right
            (blankWorkSlab (advertisedBlockWidth alpha.offsets right))
            rightVisits (fullBucketBoundary bucket offset)
    rw [congrFun hleftProfile (fullBucketBoundary bucket offset),
      congrFun hrightProfile (fullBucketBoundary bucket offset)]
  unfold finiteCachedTimedScheduleAdjacentCutRatFactor
    TimedScheduleAdjacentCutIsLeftmostMinimum
  rw [hvectors]

/-- Guard the raw selector-pair test by the two local replay indicators.  The
guard is algebraically harmless inside the full `0/1` factor graph and makes
two-sided locality unconditional. -/
noncomputable def finiteCachedTimedScheduleGuardedAdjacentCutRatFactor
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (bucket : Fin (T / b)) : (Fin n → Bool) → Rat :=
  fun input =>
    finiteCachedTimedScheduleBlockReplayRatFactor machine alpha scheduled
        (leftSourceBlockOfBucket bucket) input *
      finiteCachedTimedScheduleBlockReplayRatFactor machine alpha scheduled
        (rightSourceBlockOfBucket bucket) input *
      finiteCachedTimedScheduleAdjacentCutRatFactor machine alpha scheduled
        bucket input

/-- **Small-seed selector-pair locality.**  The guarded adjacent selector
factor depends only on the union of its two advertised query paths.  This is
an unconditional `DependsOnlyOn` theorem: failed replay inputs are killed by
the guard, while accepted inputs use exact crossing-profile congruence. -/
theorem finiteCachedTimedScheduleGuardedAdjacentCutRatFactor_dependsOnlyOn
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (bucket : Fin (T / b)) :
    FiniteBooleanFourier.DependsOnlyOn
      (finiteCachedTimedScheduleAdjacentCutQuerySupport n scheduled bucket)
      (finiteCachedTimedScheduleGuardedAdjacentCutRatFactor
        machine alpha scheduled bucket) := by
  intro left right hagree
  have hagreeLeft : ∀ coordinate ∈
      finiteCachedTimedScheduleBlockQuerySupport n scheduled
        (leftSourceBlockOfBucket bucket),
      left coordinate = right coordinate := by
    intro coordinate hcoordinate
    exact hagree coordinate (Finset.mem_union_left _ hcoordinate)
  have hagreeRight : ∀ coordinate ∈
      finiteCachedTimedScheduleBlockQuerySupport n scheduled
        (rightSourceBlockOfBucket bucket),
      left coordinate = right coordinate := by
    intro coordinate hcoordinate
    exact hagree coordinate (Finset.mem_union_right _ hcoordinate)
  have hleftFactor :=
    finiteCachedTimedScheduleBlockReplayRatFactor_dependsOnlyOn
      machine alpha scheduled (leftSourceBlockOfBucket bucket) hagreeLeft
  have hrightFactor :=
    finiteCachedTimedScheduleBlockReplayRatFactor_dependsOnlyOn
      machine alpha scheduled (rightSourceBlockOfBucket bucket) hagreeRight
  let leftAccepted := TimedScheduleBlockReplayAcceptedFromBlank
    (cachedInputMachine machine) (List.ofFn left) alpha scheduled
      (leftSourceBlockOfBucket bucket)
  let rightAccepted := TimedScheduleBlockReplayAcceptedFromBlank
    (cachedInputMachine machine) (List.ofFn left) alpha scheduled
      (rightSourceBlockOfBucket bucket)
  by_cases hl : leftAccepted
  · by_cases hr : rightAccepted
    · have hedge :=
        finiteCachedTimedScheduleAdjacentCutRatFactor_eq_of_pathAgreement
          machine left right alpha scheduled bucket hl hr (by
            intro coordinate hcoordinate
            exact (hagree coordinate hcoordinate).symm)
      unfold finiteCachedTimedScheduleGuardedAdjacentCutRatFactor
      rw [hleftFactor, hrightFactor]
      exact congrArg
        (fun value =>
          finiteCachedTimedScheduleBlockReplayRatFactor machine alpha scheduled
              (leftSourceBlockOfBucket bucket) right *
            finiteCachedTimedScheduleBlockReplayRatFactor machine alpha scheduled
              (rightSourceBlockOfBucket bucket) right * value)
        hedge.symm
    · have hzero : finiteCachedTimedScheduleBlockReplayRatFactor
          machine alpha scheduled (rightSourceBlockOfBucket bucket) left = 0 := by
        simp [finiteCachedTimedScheduleBlockReplayRatFactor,
          finiteRatPropIndicator, rightAccepted, hr]
      have hzeroRight : finiteCachedTimedScheduleBlockReplayRatFactor
          machine alpha scheduled (rightSourceBlockOfBucket bucket) right = 0 :=
        hrightFactor.symm.trans hzero
      simp [finiteCachedTimedScheduleGuardedAdjacentCutRatFactor,
        hzero, hzeroRight]
  · have hzero : finiteCachedTimedScheduleBlockReplayRatFactor
        machine alpha scheduled (leftSourceBlockOfBucket bucket) left = 0 := by
      simp [finiteCachedTimedScheduleBlockReplayRatFactor,
        finiteRatPropIndicator, leftAccepted, hl]
    have hzeroRight : finiteCachedTimedScheduleBlockReplayRatFactor
        machine alpha scheduled (leftSourceBlockOfBucket bucket) right = 0 :=
      hleftFactor.symm.trans hzero
    simp [finiteCachedTimedScheduleGuardedAdjacentCutRatFactor,
      hzero, hzeroRight]

/-- Under the already proved schedule/replay semantics, one adjacent factor
is exactly the corresponding actual-run cut condition. -/
theorem timedScheduleAdjacentCutIsLeftmostMinimum_iff_actual
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha scheduled)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha scheduled)
    (bucket : Fin (T / b)) :
    TimedScheduleAdjacentCutIsLeftmostMinimum
        machine input alpha scheduled bucket ↔
      AdvertisedCutOffsetIsLeftmostMinimum
        (actualWorkBoundaryCrossingProfile machine input T) bucket
        (alpha.offsets bucket) := by
  have hdecomposition :=
    timedScheduleAdjacentSourceDecomposesActual_of_validity
      machine input alpha scheduled hschedule haccepted
  let adjacent := timedScheduleAdjacentBucketCrossingVector
    machine input alpha scheduled bucket
  let actual : Fin b → Nat := fun candidate =>
    actualWorkBoundaryCrossingProfile machine input T
      (fullBucketBoundary bucket candidate)
  have hvectors : adjacent = actual := by
    funext candidate
    exact hdecomposition bucket candidate
  change OneSidedLeftmostMinimum
      (adjacent (alpha.offsets bucket)) (alpha.offsets bucket) adjacent ↔ _
  rw [hvectors]
  exact oneSidedLeftmostMinimum_bucket_iff
    (actualWorkBoundaryCrossingProfile machine input T)
      bucket (alpha.offsets bucket)

/-- Exact nearest-neighbour factorization of all actual-run cut checks. -/
theorem timedScheduleAllAdjacentCutsAreLeftmostMinimum_iff_actual
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha scheduled)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha scheduled) :
    TimedScheduleAllAdjacentCutsAreLeftmostMinimum
        machine input alpha scheduled ↔
      AdvertisedTimedAlphaCutsAreLeftmostMinimum machine input alpha := by
  unfold TimedScheduleAllAdjacentCutsAreLeftmostMinimum
    AdvertisedTimedAlphaCutsAreLeftmostMinimum
    AdvertisedCutOffsetsAreLeftmostMinimum
  constructor
  · intro hall bucket
    exact (timedScheduleAdjacentCutIsLeftmostMinimum_iff_actual
      machine input alpha scheduled hschedule haccepted bucket).1
        (hall bucket)
  · intro hall bucket
    exact (timedScheduleAdjacentCutIsLeftmostMinimum_iff_actual
      machine input alpha scheduled hschedule haccepted bucket).2
        (hall bucket)

/-- **Canonical-alpha path-factor theorem.**

For positive block size, a valid locally replayed timed alpha has the actual
canonical offset vector iff every nearest-neighbour bucket factor accepts.
Thus the non-product part of one alpha fiber is a one-dimensional edge
interaction, not an unrestricted global transcript predicate. -/
theorem timedScheduleAllAdjacentCutsAreLeftmostMinimum_iff_offsets_eq
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha scheduled)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha scheduled) :
    TimedScheduleAllAdjacentCutsAreLeftmostMinimum
        machine input alpha scheduled ↔
      alpha.offsets = canonicalCutOffsets machine input T b hb := by
  rw [timedScheduleAllAdjacentCutsAreLeftmostMinimum_iff_actual
    machine input alpha scheduled hschedule haccepted]
  exact
    (advertisedTimedAlphaCutMinimalityCheck_eq_true_iff
      machine input alpha).symm.trans
        (advertisedTimedAlphaCutMinimalityCheck_eq_true_iff_offsets_eq
          machine input T b hb alpha)

/-- Exact factor-graph semantics of the executable fixed-alpha component.

The input-dependent predicate is a conjunction of unary block-replay factors
and nearest-neighbour cut factors.  Schedule validity is the remaining static
alpha condition.  No global crossing-profile or canonical-offset equality
remains on the right-hand side. -/
theorem timedAlphaVisitScheduleInPlaceCanonicalCutCheck_eq_true_iff_factors
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b)) :
    timedAlphaVisitScheduleInPlaceCanonicalCutCheck
        machine input alpha scheduled = true ↔
      TimedAlphaVisitScheduleValid machine alpha scheduled ∧
        AllFixedAlphaBlockVisitListsAcceptedFromBlank
          machine input alpha scheduled ∧
        TimedScheduleAllAdjacentCutsAreLeftmostMinimum
          machine input alpha scheduled := by
  constructor
  · intro hcheck
    have hparts :=
      (timedAlphaVisitScheduleInPlaceCanonicalCutCheck_eq_true_iff
        machine input T b hb alpha scheduled).1 hcheck
    have hbase :=
      (timedAlphaVisitScheduleAllBlockVisitsCheck_eq_true_iff
        machine input alpha scheduled).1 hparts.1
    refine ⟨hbase.1, hbase.2, ?_⟩
    exact
      (timedScheduleAllAdjacentCutsAreLeftmostMinimum_iff_offsets_eq
        machine input T b hb alpha scheduled hbase.1 hbase.2).2 hparts.2
  · rintro ⟨hschedule, haccepted, hadjacent⟩
    have hbase : timedAlphaVisitScheduleAllBlockVisitsCheck
        machine input alpha scheduled = true :=
      (timedAlphaVisitScheduleAllBlockVisitsCheck_eq_true_iff
        machine input alpha scheduled).2 ⟨hschedule, haccepted⟩
    apply
      (timedAlphaVisitScheduleInPlaceCanonicalCutCheck_eq_true_iff
        machine input T b hb alpha scheduled).2
    exact ⟨hbase,
      (timedScheduleAllAdjacentCutsAreLeftmostMinimum_iff_offsets_eq
        machine input T b hb alpha scheduled hschedule haccepted).1 hadjacent⟩

/-- Pointwise `0/1` partition-function identity for the fixed-alpha
component.  Unary factors are the individual advertised block replays; edge
factors are the nearest-neighbour cut tests.  This is the exact algebraic
surface needed for a later even/odd tensor-layer Fourier expansion. -/
theorem finiteRatPropIndicator_inPlaceCanonicalCutCheck_eq_factorGraph
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b)) :
    finiteRatPropIndicator
        (timedAlphaVisitScheduleInPlaceCanonicalCutCheck
          machine input alpha scheduled = true) =
      finiteRatPropIndicator
          (TimedAlphaVisitScheduleValid machine alpha scheduled) *
        (∏ block : Fin (T / b + 1),
          finiteRatPropIndicator
            (TimedScheduleBlockReplayAcceptedFromBlank
              machine input alpha scheduled block)) *
        (∏ bucket : Fin (T / b),
          finiteRatPropIndicator
            (TimedScheduleAdjacentCutIsLeftmostMinimum
              machine input alpha scheduled bucket)) := by
  classical
  rw [← finiteRatPropIndicator_forall_eq_prod
      (fun block : Fin (T / b + 1) =>
        TimedScheduleBlockReplayAcceptedFromBlank
          machine input alpha scheduled block),
    ← finiteRatPropIndicator_forall_eq_prod
      (fun bucket : Fin (T / b) =>
        TimedScheduleAdjacentCutIsLeftmostMinimum
          machine input alpha scheduled bucket)]
  have hiff :=
    timedAlphaVisitScheduleInPlaceCanonicalCutCheck_eq_true_iff_factors
      machine input T b hb alpha scheduled
  have hacceptedIff :
      (∀ block : Fin (T / b + 1),
        TimedScheduleBlockReplayAcceptedFromBlank
          machine input alpha scheduled block) ↔
        AllFixedAlphaBlockVisitListsAcceptedFromBlank
          machine input alpha scheduled := by
    rfl
  by_cases hschedule : TimedAlphaVisitScheduleValid machine alpha scheduled
  · by_cases haccepted : ∀ block : Fin (T / b + 1),
        TimedScheduleBlockReplayAcceptedFromBlank
          machine input alpha scheduled block
    · by_cases hadjacent : TimedScheduleAllAdjacentCutsAreLeftmostMinimum
          machine input alpha scheduled
      · have hcheck := hiff.2
          ⟨hschedule, hacceptedIff.1 haccepted, hadjacent⟩
        have hadjacent' : ∀ bucket : Fin (T / b),
            TimedScheduleAdjacentCutIsLeftmostMinimum
              machine input alpha scheduled bucket := by
          simpa [TimedScheduleAllAdjacentCutsAreLeftmostMinimum] using
            hadjacent
        simp [finiteRatPropIndicator, hschedule, haccepted, hadjacent', hcheck]
      · have hcheck : timedAlphaVisitScheduleInPlaceCanonicalCutCheck
            machine input alpha scheduled ≠ true := by
          intro htrue
          exact hadjacent (hiff.1 htrue).2.2
        have hadjacent' : ¬ ∀ bucket : Fin (T / b),
            TimedScheduleAdjacentCutIsLeftmostMinimum
              machine input alpha scheduled bucket := by
          simpa [TimedScheduleAllAdjacentCutsAreLeftmostMinimum] using
            hadjacent
        simp [finiteRatPropIndicator, hschedule, haccepted, hadjacent', hcheck]
    · have hcheck : timedAlphaVisitScheduleInPlaceCanonicalCutCheck
          machine input alpha scheduled ≠ true := by
        intro htrue
        exact haccepted (hacceptedIff.2 (hiff.1 htrue).2.1)
      simp [finiteRatPropIndicator, hschedule, haccepted, hcheck]
  · have hcheck : timedAlphaVisitScheduleInPlaceCanonicalCutCheck
        machine input alpha scheduled ≠ true := by
      intro htrue
      exact hschedule (hiff.1 htrue).1
    simp [finiteRatPropIndicator, hschedule, hcheck]

end OneTapeMagnification
end Frontier
end Pnp4
