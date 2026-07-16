import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.AdvertisedSelectedCutMultiplicityReplay
import Pnp4.Frontier.OneTapeMagnification.TimedAlphaAdjacentCutSupportDisjointness

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

local instance cachedInputMachineStateDecidableEqForCanonicalFiberSplicing
    (machine : DeterministicMachine) [DecidableEq machine.State] :
    DecidableEq (cachedInputMachine machine).State :=
  cachedInputStateDecidableEq machine

/-!
# Rectangular closure of a fixed timed-alpha canonical fiber

An arbitrary mixture of two adjacent crossing-count vectors need not retain
the same minimum.  The splice theorem below therefore does not assume such a
false mixed-sum principle.  It uses the sharper advertised-slab geometry:

* a candidate strictly left of an advertised selected cut belongs only to
  the left source block;
* a candidate strictly right belongs only to the right source block;
* the count at the selected cut itself is the alpha-word multiplicity, by
  `advertisedSelectedCutMultiplicity_eq_actual_of_scheduleReplay`.

Thus one canonical cut condition splits into two directed one-sided
conditions, one owned by each adjacent source block.  The theorem
`advertisedBlock_relevant_and_complementary_iff_adjacentCuts` is used in both
directions: first to extract the owned conditions from canonical sources, and
then to glue independently transported block conditions back into complete
cut minimality.  No direction or source-block assumption is hidden.
-/

/-! ## Internal-boundary ownership -/

/-- A replayed block list contributes zero at a boundary separated from its
entire advertised slab. -/
theorem
    fixedAlphaBlockVisitListStreamingCrossingCount_eq_zero_of_separatedSlab
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1)) (boundary : Nat)
    (carried : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit machine.State T))
    (haccepted : FixedAlphaBlockVisitReplayAccepted
      machine input alpha block carried visits)
    (hseparated :
      advertisedBlockLower alpha.offsets block +
          advertisedBlockWidth alpha.offsets block ≤ boundary ∨
        boundary + 1 < advertisedBlockLower alpha.offsets block) :
    fixedAlphaBlockVisitListStreamingCrossingCount machine input alpha block
      boundary carried visits = 0 := by
  induction visits generalizing carried with
  | nil => rfl
  | cons visit rest ih =>
      have hfirst :=
        streamingWorkBoundaryCrossingCountFrom_eq_zero_of_inside_separated
          machine input
          (fixedAlphaBlockVisitEntryConfiguration
            alpha block visit carried)
          visit.steps boundary
          (advertisedBlockLower alpha.offsets block)
          (advertisedBlockWidth alpha.offsets block)
          haccepted.1.1 hseparated
      simp only [fixedAlphaBlockVisitListStreamingCrossingCount]
      rw [hfirst, Nat.zero_add]
      exact ih
        (fixedAlphaBlockVisitOutputSlab
          machine input alpha block visit carried)
        haccepted.2

/-- If both cells of a boundary lie strictly inside one advertised block,
that block's local replay profile is the complete actual crossing count at
the boundary.  Every other block slab is geometrically separated. -/
theorem timedScheduleBlockCrossingProfile_eq_actual_of_strictlyInside
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha scheduled)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha scheduled)
    (block : Fin (T / b + 1)) (boundary : Fin T)
    (hinside : WorkBoundaryStrictlyInsideAdvertisedBlock
      alpha.offsets block boundary) :
    fixedAlphaBlockVisitListCrossingProfile machine input alpha block
        (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
        (timedAlphaBlockVisits block scheduled) boundary =
      actualWorkBoundaryCrossingProfile machine input T boundary := by
  have hsum := congrFun
    (sourceBlockSummedCrossingProfile_eq_actual
      machine input alpha scheduled hschedule haccepted) boundary
  calc
    fixedAlphaBlockVisitListCrossingProfile machine input alpha block
        (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
        (timedAlphaBlockVisits block scheduled) boundary =
      sourceBlockSummedCrossingProfile machine input alpha
        (timedScheduleBlankBlockSlabs alpha)
        (timedScheduleBlockVisitFamily scheduled) boundary := by
          symm
          unfold sourceBlockSummedCrossingProfile
          apply Finset.sum_eq_single block
          · intro other _ hne
            unfold fixedAlphaSourceBlockCrossingContribution
              timedScheduleBlankBlockSlabs timedScheduleBlockVisitFamily
            apply
              fixedAlphaBlockVisitListStreamingCrossingCount_eq_zero_of_separatedSlab
                machine input alpha other boundary.val
                (blankWorkSlab
                  (advertisedBlockWidth alpha.offsets other))
                (timedAlphaBlockVisits other scheduled) (haccepted other).2
            have horder : other < block ∨ block < other :=
              lt_or_gt_of_ne hne
            rcases horder with hbefore | hafter
            · left
              rw [advertisedBlockLower_add_width_eq_upperExclusive]
              exact
                (advertisedBlockUpperExclusive_le_lower_of_lt
                  alpha.offsets hbefore).trans hinside.1
            · right
              exact hinside.2.trans_le
                (advertisedBlockUpperExclusive_le_lower_of_lt
                  alpha.offsets hafter)
          · intro hnot
            exact (hnot (Finset.mem_univ block)).elim
    _ = actualWorkBoundaryCrossingProfile machine input T boundary := hsum

/-! ## Directed block factors -/

/-- The two one-sided candidate inequalities genuinely owned by one block.
The selected reference count is the input-independent multiplicity hardwired
in the fixed timed alpha. -/
def TimedScheduleBlockRelevantOneSidedMinimum
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (block : Fin (T / b + 1)) : Prop :=
  AdvertisedBlockRelevantOneSidedMinimum alpha.offsets block
    (advertisedSelectedCutMultiplicity alpha)
    (fixedAlphaBlockVisitListCrossingProfile machine input alpha block
      (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
      (timedAlphaBlockVisits block scheduled))

/-- Complete adjacent-cut canonicality of an accepted source implies the
directed one-sided condition owned by each block.  The selected-count premise
of the relevant/complementary theorem is supplied by multiplicity replay. -/
theorem timedScheduleBlockRelevantOneSidedMinimum_of_allAdjacentCuts
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha scheduled)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha scheduled)
    (hcanonical : TimedScheduleAllAdjacentCutsAreLeftmostMinimum
      machine input alpha scheduled)
    (block : Fin (T / b + 1)) :
    TimedScheduleBlockRelevantOneSidedMinimum
      machine input alpha scheduled block := by
  let actual := actualWorkBoundaryCrossingProfile machine input T
  have hselected : ∀ bucket : Fin (T / b),
      advertisedSelectedCutMultiplicity alpha bucket =
        actual (fullBucketBoundary bucket (alpha.offsets bucket)) := by
    intro bucket
    exact
      advertisedSelectedCutMultiplicity_eq_actual_of_scheduleReplay
        machine input alpha scheduled hschedule haccepted bucket
  have hadjacent : AdvertisedBlockAdjacentCutsLeftmostMinimum
      alpha.offsets block actual := by
    constructor
    · intro hleft
      let bucket : Fin (T / b) := ⟨block.val - 1, by omega⟩
      exact
        (timedScheduleAdjacentCutIsLeftmostMinimum_iff_actual
          machine input alpha scheduled hschedule haccepted bucket).1
          (hcanonical bucket)
    · intro hright
      let bucket : Fin (T / b) := ⟨block.val, hright⟩
      exact
        (timedScheduleAdjacentCutIsLeftmostMinimum_iff_actual
          machine input alpha scheduled hschedule haccepted bucket).1
          (hcanonical bucket)
  have hactualRelevant : AdvertisedBlockRelevantOneSidedMinimum
      alpha.offsets block (advertisedSelectedCutMultiplicity alpha) actual :=
    ((advertisedBlock_relevant_and_complementary_iff_adjacentCuts
      alpha.offsets block (advertisedSelectedCutMultiplicity alpha)
      actual hselected).2 hadjacent).1
  constructor
  · intro hleft candidate hcandidate
    let boundary := fullBucketBoundary
      (show Fin (T / b) from ⟨block.val - 1, by omega⟩) candidate
    have hown :=
      timedScheduleBlockCrossingProfile_eq_actual_of_strictlyInside
        machine input alpha scheduled hschedule haccepted block boundary
        (leftBucketTailCandidate_strictlyInsideAdvertisedBlock
          alpha.offsets block hleft candidate hcandidate)
    rw [hown]
    exact hactualRelevant.1 hleft candidate hcandidate
  · intro hright candidate hcandidate
    let boundary := fullBucketBoundary
      (show Fin (T / b) from ⟨block.val, hright⟩) candidate
    have hown :=
      timedScheduleBlockCrossingProfile_eq_actual_of_strictlyInside
        machine input alpha scheduled hschedule haccepted block boundary
        (rightBucketPrefixCandidate_strictlyInsideAdvertisedBlock
          alpha.offsets block hright candidate hcandidate)
    rw [hown]
    exact hactualRelevant.2 hright candidate hcandidate

/-- Conversely, an accepted block's transported local inequalities are the
corresponding inequalities of the candidate's actual global profile, because
all relevant candidate boundaries are strictly internal to that block. -/
theorem timedScheduleBlockActualRelevantOneSidedMinimum_of_local
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha scheduled)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha scheduled)
    (block : Fin (T / b + 1))
    (hlocal : TimedScheduleBlockRelevantOneSidedMinimum
      machine input alpha scheduled block) :
    AdvertisedBlockRelevantOneSidedMinimum alpha.offsets block
      (advertisedSelectedCutMultiplicity alpha)
      (actualWorkBoundaryCrossingProfile machine input T) := by
  constructor
  · intro hleft candidate hcandidate
    let boundary := fullBucketBoundary
      (show Fin (T / b) from ⟨block.val - 1, by omega⟩) candidate
    have hown :=
      timedScheduleBlockCrossingProfile_eq_actual_of_strictlyInside
        machine input alpha scheduled hschedule haccepted block boundary
        (leftBucketTailCandidate_strictlyInsideAdvertisedBlock
          alpha.offsets block hleft candidate hcandidate)
    rw [← hown]
    exact hlocal.1 hleft candidate hcandidate
  · intro hright candidate hcandidate
    let boundary := fullBucketBoundary
      (show Fin (T / b) from ⟨block.val, hright⟩) candidate
    have hown :=
      timedScheduleBlockCrossingProfile_eq_actual_of_strictlyInside
        machine input alpha scheduled hschedule haccepted block boundary
        (rightBucketPrefixCandidate_strictlyInsideAdvertisedBlock
          alpha.offsets block hright candidate hcandidate)
    rw [← hown]
    exact hlocal.2 hright candidate hcandidate

/-- Relevant halves of all blocks supply the complementary halves of any one
block: its left prefix is owned by the left neighbour and its right tail by
the right neighbour. -/
theorem advertisedBlockComplementaryOneSidedMinimum_of_all_relevant
    {T b : Nat} (offsets : CanonicalCutOffsets T b)
    (selectedCounts : Fin (T / b) → Nat) (crossings : Fin T → Nat)
    (hall : ∀ block : Fin (T / b + 1),
      AdvertisedBlockRelevantOneSidedMinimum
        offsets block selectedCounts crossings)
    (block : Fin (T / b + 1)) :
    AdvertisedBlockComplementaryOneSidedMinimum
      offsets block selectedCounts crossings := by
  constructor
  · intro hleft candidate hcandidate
    let bucket : Fin (T / b) := ⟨block.val - 1, by omega⟩
    let neighbor : Fin (T / b + 1) := leftSourceBlockOfBucket bucket
    have hneighborRight : neighbor.val < T / b := by
      simp [neighbor, leftSourceBlockOfBucket]
    have hbucketEq :
        (⟨neighbor.val, hneighborRight⟩ : Fin (T / b)) = bucket := by
      apply Fin.ext
      rfl
    have h := (hall neighbor).2 hneighborRight candidate
    simpa [bucket, neighbor, hbucketEq] using h (by
      simpa [bucket, neighbor, hbucketEq] using hcandidate)
  · intro hright candidate hcandidate
    let bucket : Fin (T / b) := ⟨block.val, hright⟩
    let neighbor : Fin (T / b + 1) := rightSourceBlockOfBucket bucket
    have hneighborLeft : 0 < neighbor.val := by
      simp [neighbor, rightSourceBlockOfBucket]
    have hbucketEq :
        (⟨neighbor.val - 1, by omega⟩ : Fin (T / b)) = bucket := by
      apply Fin.ext
      simp [neighbor, rightSourceBlockOfBucket]
    have h := (hall neighbor).1 hneighborLeft candidate
    simpa [bucket, neighbor, hbucketEq] using h (by
      simpa [bucket, neighbor, hbucketEq] using hcandidate)

/-- All directed block halves, together with exact selected counts, glue to
the full leftmost-minimum condition in every bucket. -/
theorem advertisedCutsLeftmostMinimum_of_allBlockRelevant
    {T b : Nat} (offsets : CanonicalCutOffsets T b)
    (selectedCounts : Fin (T / b) → Nat) (crossings : Fin T → Nat)
    (hselected : ∀ bucket, selectedCounts bucket =
      crossings (fullBucketBoundary bucket (offsets bucket)))
    (hall : ∀ block : Fin (T / b + 1),
      AdvertisedBlockRelevantOneSidedMinimum
        offsets block selectedCounts crossings) :
    ∀ bucket : Fin (T / b),
      AdvertisedCutOffsetIsLeftmostMinimum
        crossings bucket (offsets bucket) := by
  intro bucket
  let block : Fin (T / b + 1) := leftSourceBlockOfBucket bucket
  have hright : block.val < T / b := by
    simp [block, leftSourceBlockOfBucket]
  have hadjacent :=
    (advertisedBlock_relevant_and_complementary_iff_adjacentCuts
      offsets block selectedCounts crossings hselected).1
      ⟨hall block,
        advertisedBlockComplementaryOneSidedMinimum_of_all_relevant
          offsets selectedCounts crossings hall block⟩
  have h := hadjacent.2 hright
  simpa [block, leftSourceBlockOfBucket] using h

/-- Accepted replay plus the transported relevant half of every block imply
all nearest-neighbour schedule factors. -/
theorem timedScheduleAllAdjacentCutsAreLeftmostMinimum_of_allBlockRelevant
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha scheduled)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha scheduled)
    (hall : ∀ block : Fin (T / b + 1),
      TimedScheduleBlockRelevantOneSidedMinimum
        machine input alpha scheduled block) :
    TimedScheduleAllAdjacentCutsAreLeftmostMinimum
      machine input alpha scheduled := by
  let actual := actualWorkBoundaryCrossingProfile machine input T
  have hselected : ∀ bucket : Fin (T / b),
      advertisedSelectedCutMultiplicity alpha bucket =
        actual (fullBucketBoundary bucket (alpha.offsets bucket)) := by
    intro bucket
    exact
      advertisedSelectedCutMultiplicity_eq_actual_of_scheduleReplay
        machine input alpha scheduled hschedule haccepted bucket
  have hallActual : ∀ block : Fin (T / b + 1),
      AdvertisedBlockRelevantOneSidedMinimum alpha.offsets block
        (advertisedSelectedCutMultiplicity alpha) actual := by
    intro block
    exact timedScheduleBlockActualRelevantOneSidedMinimum_of_local
      machine input alpha scheduled hschedule haccepted block (hall block)
  have hcuts := advertisedCutsLeftmostMinimum_of_allBlockRelevant
    alpha.offsets (advertisedSelectedCutMultiplicity alpha) actual
      hselected hallActual
  intro bucket
  exact
    (timedScheduleAdjacentCutIsLeftmostMinimum_iff_actual
      machine input alpha scheduled hschedule haccepted bucket).2
      (hcuts bucket)

/-! ## Path-local transport and concrete splices -/

/-- Exact block-profile congruence transports the directed local condition
from an accepted source to any input agreeing on that block's advertised
query path. -/
theorem timedScheduleBlockRelevantOneSidedMinimum_of_pathAgreement
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat} (source candidate : Fin n → Bool)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (block : Fin (T / b + 1))
    (hsourceAccepted : FixedAlphaBlockVisitListAcceptedFromBlank
      (cachedInputMachine machine) (List.ofFn source) alpha block
      (timedAlphaBlockVisits block scheduled))
    (hsourceRelevant : TimedScheduleBlockRelevantOneSidedMinimum
      (cachedInputMachine machine) (List.ofFn source)
        alpha scheduled block)
    (hagreement : TimedAlphaBlockAdvertisedAgreement
      scheduled block source candidate) :
    TimedScheduleBlockRelevantOneSidedMinimum
      (cachedInputMachine machine) (List.ofFn candidate)
        alpha scheduled block := by
  have hprofile := fixedAlphaBlockVisitListCrossingProfile_eq_of_pathAgreement
    machine source candidate alpha block
      (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
      (timedAlphaBlockVisits block scheduled) hsourceAccepted.2 hagreement
      (fixedAlphaBlockVisitsTotalSteps_le_horizon
        (timedAlphaBlockVisits block scheduled) hsourceAccepted.1)
  unfold TimedScheduleBlockRelevantOneSidedMinimum at hsourceRelevant ⊢
  rw [hprofile]
  exact hsourceRelevant

/-- A single-block splice agrees with the donor on the selected advertised
path. -/
theorem finiteCachedTimedAlphaSingleBlockSplice_agreesWith_donor
    {State : Type} {n T b : Nat}
    (scheduled : List (TimedAlphaScheduledVisit State T b))
    (selected : Fin (T / b + 1)) (donor base : Fin n → Bool) :
    TimedAlphaBlockAdvertisedAgreement scheduled selected donor
      (finiteCachedTimedAlphaSingleBlockSplice
        scheduled selected donor base) := by
  intro coordinate hcoordinate
  exact finiteCachedTimedAlphaSingleBlockSplice_eq_donor
    scheduled selected donor base coordinate hcoordinate

/-- On every nonselected block path, disjointness makes a single-block splice
agree with the base. -/
theorem finiteCachedTimedAlphaSingleBlockSplice_agreesWith_base_of_ne
    {State : Type} {n T b : Nat}
    (scheduled : List (TimedAlphaScheduledVisit State T b))
    (hchained : TimedAlphaScheduledVisitsChained scheduled)
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled)
    (selected block : Fin (T / b + 1)) (hne : block ≠ selected)
    (donor base : Fin n → Bool) :
    TimedAlphaBlockAdvertisedAgreement scheduled block base
      (finiteCachedTimedAlphaSingleBlockSplice
        scheduled selected donor base) := by
  intro coordinate hcoordinate
  have hdisjoint :=
    finiteCachedTimedScheduleBlockQuerySupport_disjoint_of_ne
      (n := n) scheduled hchained hmonotone hne
  have hnotSelected : coordinate ∉
      finiteCachedBlockVisitListAdvertisedQueryOrder n
        (timedAlphaBlockVisits selected scheduled) := by
    intro hselected
    have hblockSupport : coordinate ∈
        finiteCachedTimedScheduleBlockQuerySupport n scheduled block := by
      simpa [finiteCachedTimedScheduleBlockQuerySupport] using hcoordinate
    have hselectedSupport : coordinate ∈
        finiteCachedTimedScheduleBlockQuerySupport n scheduled selected := by
      simpa [finiteCachedTimedScheduleBlockQuerySupport] using hselected
    exact (Finset.disjoint_left.mp hdisjoint)
      hblockSupport hselectedSupport
  exact finiteCachedTimedAlphaSingleBlockSplice_eq_base
    scheduled selected donor base coordinate hnotSelected

/-! ## Canonical-fiber closure -/

/-- **Single-block canonical splice.**

Two inputs accepted by the same fixed-alpha in-place canonical component may
exchange the complete advertised path of one block.  The splice remains in
that canonical component. -/
theorem timedAlphaVisitScheduleInPlaceCanonicalCutCheck_singleBlockSplice
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat} (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (selected : Fin (T / b + 1)) (donor base : Fin n → Bool)
    (hdonor : timedAlphaVisitScheduleInPlaceCanonicalCutCheck
      (cachedInputMachine machine) (List.ofFn donor) alpha scheduled = true)
    (hbase : timedAlphaVisitScheduleInPlaceCanonicalCutCheck
      (cachedInputMachine machine) (List.ofFn base) alpha scheduled = true) :
    timedAlphaVisitScheduleInPlaceCanonicalCutCheck
      (cachedInputMachine machine)
      (List.ofFn (finiteCachedTimedAlphaSingleBlockSplice
        scheduled selected donor base)) alpha scheduled = true := by
  let splice := finiteCachedTimedAlphaSingleBlockSplice
    scheduled selected donor base
  have hdonorParts :=
    (timedAlphaVisitScheduleInPlaceCanonicalCutCheck_eq_true_iff_factors
      (cachedInputMachine machine) (List.ofFn donor) T b hb
        alpha scheduled).1 hdonor
  have hbaseParts :=
    (timedAlphaVisitScheduleInPlaceCanonicalCutCheck_eq_true_iff_factors
      (cachedInputMachine machine) (List.ofFn base) T b hb
        alpha scheduled).1 hbase
  have hspliceAccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      (cachedInputMachine machine) (List.ofFn splice) alpha scheduled := by
    exact allFixedAlphaBlockVisitListsAcceptedFromBlank_singleBlockSplice
      machine alpha scheduled hbaseParts.1 selected donor base
        hdonorParts.2.1 hbaseParts.2.1
  have hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled :=
    allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
      (cachedInputMachine machine) (List.ofFn base)
        alpha scheduled hbaseParts.2.1
  have hchained : TimedAlphaScheduledVisitsChained scheduled := by
    obtain ⟨_syntactic, _finalCursor, _visitsSoFar, _hfold, _hfinish,
      hchained⟩ := hbaseParts.1
    exact hchained
  have hallRelevant : ∀ block : Fin (T / b + 1),
      TimedScheduleBlockRelevantOneSidedMinimum
        (cachedInputMachine machine) (List.ofFn splice)
          alpha scheduled block := by
    intro block
    by_cases hselected : block = selected
    · subst block
      apply timedScheduleBlockRelevantOneSidedMinimum_of_pathAgreement
        machine donor splice alpha scheduled selected
          (hdonorParts.2.1 selected)
      · exact timedScheduleBlockRelevantOneSidedMinimum_of_allAdjacentCuts
          (cachedInputMachine machine) (List.ofFn donor) alpha scheduled
            hdonorParts.1 hdonorParts.2.1 hdonorParts.2.2 selected
      · exact finiteCachedTimedAlphaSingleBlockSplice_agreesWith_donor
          scheduled selected donor base
    · apply timedScheduleBlockRelevantOneSidedMinimum_of_pathAgreement
        machine base splice alpha scheduled block (hbaseParts.2.1 block)
      · exact timedScheduleBlockRelevantOneSidedMinimum_of_allAdjacentCuts
          (cachedInputMachine machine) (List.ofFn base) alpha scheduled
            hbaseParts.1 hbaseParts.2.1 hbaseParts.2.2 block
      · exact finiteCachedTimedAlphaSingleBlockSplice_agreesWith_base_of_ne
          scheduled hchained hmonotone selected block hselected donor base
  have hspliceCanonical : TimedScheduleAllAdjacentCutsAreLeftmostMinimum
      (cachedInputMachine machine) (List.ofFn splice) alpha scheduled :=
    timedScheduleAllAdjacentCutsAreLeftmostMinimum_of_allBlockRelevant
      (cachedInputMachine machine) (List.ofFn splice) alpha scheduled
        hbaseParts.1 hspliceAccepted hallRelevant
  apply
    (timedAlphaVisitScheduleInPlaceCanonicalCutCheck_eq_true_iff_factors
      (cachedInputMachine machine) (List.ofFn splice) T b hb
        alpha scheduled).2
  exact ⟨hbaseParts.1, hspliceAccepted, hspliceCanonical⟩

/-- Every finite sequence of independent canonical block replacements stays
inside the same fixed-alpha canonical component. -/
theorem timedAlphaVisitScheduleInPlaceCanonicalCutCheck_blockSpliceFold
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat} (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (sources : Fin (T / b + 1) → Fin n → Bool)
    (blocks : List (Fin (T / b + 1))) (base : Fin n → Bool)
    (hsources : ∀ block : Fin (T / b + 1),
      timedAlphaVisitScheduleInPlaceCanonicalCutCheck
        (cachedInputMachine machine) (List.ofFn (sources block))
          alpha scheduled = true)
    (hbase : timedAlphaVisitScheduleInPlaceCanonicalCutCheck
      (cachedInputMachine machine) (List.ofFn base) alpha scheduled = true) :
    timedAlphaVisitScheduleInPlaceCanonicalCutCheck
      (cachedInputMachine machine)
      (List.ofFn (finiteCachedTimedAlphaBlockSpliceFold
        scheduled sources blocks base)) alpha scheduled = true := by
  induction blocks generalizing base with
  | nil =>
      simpa [finiteCachedTimedAlphaBlockSpliceFold] using hbase
  | cons block blocks ih =>
      apply ih
      exact
        timedAlphaVisitScheduleInPlaceCanonicalCutCheck_singleBlockSplice
          machine hb alpha scheduled block (sources block) base
            (hsources block) hbase

/-- **All-block rectangular closure of the fixed-alpha canonical fiber.** -/
theorem timedAlphaVisitScheduleInPlaceCanonicalCutCheck_allBlockSplice
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat} (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (sources : Fin (T / b + 1) → Fin n → Bool)
    (fallback : Fin n → Bool)
    (hsources : ∀ block : Fin (T / b + 1),
      timedAlphaVisitScheduleInPlaceCanonicalCutCheck
        (cachedInputMachine machine) (List.ofFn (sources block))
          alpha scheduled = true)
    (hfallback : timedAlphaVisitScheduleInPlaceCanonicalCutCheck
      (cachedInputMachine machine) (List.ofFn fallback)
        alpha scheduled = true) :
    timedAlphaVisitScheduleInPlaceCanonicalCutCheck
      (cachedInputMachine machine)
      (List.ofFn (finiteCachedTimedAlphaAllBlockSplice
        scheduled sources fallback)) alpha scheduled = true := by
  exact timedAlphaVisitScheduleInPlaceCanonicalCutCheck_blockSpliceFold
    machine hb alpha scheduled sources (List.finRange (T / b + 1))
      fallback hsources hfallback

/-! ## Projection/rectangle characterization -/

/-- Exact block projection of the fixed-alpha canonical fiber: some canonical
source realizes the candidate's advertised path in this block. -/
def TimedAlphaCanonicalBlockProjection
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat} (_hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (block : Fin (T / b + 1)) (candidate : Fin n → Bool) : Prop :=
  ∃ source : Fin n → Bool,
    timedAlphaVisitScheduleInPlaceCanonicalCutCheck
        (cachedInputMachine machine) (List.ofFn source)
          alpha scheduled = true ∧
      TimedAlphaBlockAdvertisedAgreement
        scheduled block source candidate

/-- **Exact rectangle characterization.** Membership in one fixed-alpha
canonical fiber is equivalent to membership in every advertised block
projection of that fiber.  The reverse implication actually needs no extra
fallback: the per-block canonical witnesses supply schedule validity, local
replay, and every directed cut half. -/
theorem timedAlphaVisitScheduleInPlaceCanonicalCutCheck_iff_blockProjections
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat} (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (candidate : Fin n → Bool) :
    timedAlphaVisitScheduleInPlaceCanonicalCutCheck
        (cachedInputMachine machine) (List.ofFn candidate)
          alpha scheduled = true ↔
      ∀ block : Fin (T / b + 1),
        TimedAlphaCanonicalBlockProjection
          machine hb alpha scheduled block candidate := by
  classical
  constructor
  · intro hcandidate block
    exact ⟨candidate, hcandidate, by
      intro coordinate _
      rfl⟩
  · intro hprojections
    choose sources hsourcesChecks hsourcesAgreements using hprojections
    let initialBlock : Fin (T / b + 1) :=
      ⟨0, Nat.zero_lt_succ (T / b)⟩
    have hinitialParts :=
      (timedAlphaVisitScheduleInPlaceCanonicalCutCheck_eq_true_iff_factors
        (cachedInputMachine machine) (List.ofFn (sources initialBlock))
          T b hb alpha scheduled).1 (hsourcesChecks initialBlock)
    have hsourceParts : ∀ block : Fin (T / b + 1),
        TimedAlphaVisitScheduleValid (cachedInputMachine machine)
            alpha scheduled ∧
          AllFixedAlphaBlockVisitListsAcceptedFromBlank
            (cachedInputMachine machine) (List.ofFn (sources block))
              alpha scheduled ∧
          TimedScheduleAllAdjacentCutsAreLeftmostMinimum
            (cachedInputMachine machine) (List.ofFn (sources block))
              alpha scheduled := by
      intro block
      exact
        (timedAlphaVisitScheduleInPlaceCanonicalCutCheck_eq_true_iff_factors
          (cachedInputMachine machine) (List.ofFn (sources block))
            T b hb alpha scheduled).1 (hsourcesChecks block)
    have hcandidateAccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
        (cachedInputMachine machine) (List.ofFn candidate)
          alpha scheduled := by
      apply
        allFixedAlphaBlockVisitListsAcceptedFromBlank_of_blockwise_pathAgreement
          machine alpha scheduled hinitialParts.1 sources candidate
      · intro block
        exact (hsourceParts block).2.1 block |>.2
      · exact hsourcesAgreements
    have hallRelevant : ∀ block : Fin (T / b + 1),
        TimedScheduleBlockRelevantOneSidedMinimum
          (cachedInputMachine machine) (List.ofFn candidate)
            alpha scheduled block := by
      intro block
      apply timedScheduleBlockRelevantOneSidedMinimum_of_pathAgreement
        machine (sources block) candidate alpha scheduled block
          ((hsourceParts block).2.1 block)
      · exact timedScheduleBlockRelevantOneSidedMinimum_of_allAdjacentCuts
          (cachedInputMachine machine) (List.ofFn (sources block))
            alpha scheduled (hsourceParts block).1
            (hsourceParts block).2.1 (hsourceParts block).2.2 block
      · exact hsourcesAgreements block
    have hcandidateCanonical : TimedScheduleAllAdjacentCutsAreLeftmostMinimum
        (cachedInputMachine machine) (List.ofFn candidate)
          alpha scheduled :=
      timedScheduleAllAdjacentCutsAreLeftmostMinimum_of_allBlockRelevant
        (cachedInputMachine machine) (List.ofFn candidate) alpha scheduled
          hinitialParts.1 hcandidateAccepted hallRelevant
    apply
      (timedAlphaVisitScheduleInPlaceCanonicalCutCheck_eq_true_iff_factors
        (cachedInputMachine machine) (List.ofFn candidate)
          T b hb alpha scheduled).2
    exact ⟨hinitialParts.1, hcandidateAccepted, hcandidateCanonical⟩

/-- Product-indicator form of the exact block-projection characterization. -/
theorem finiteRatPropIndicator_inPlaceCanonicalCutCheck_eq_blockProjectionProduct
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {n T b : Nat} (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (candidate : Fin n → Bool) :
    finiteRatPropIndicator
        (timedAlphaVisitScheduleInPlaceCanonicalCutCheck
          (cachedInputMachine machine) (List.ofFn candidate)
            alpha scheduled = true) =
      ∏ block : Fin (T / b + 1),
        finiteRatPropIndicator
          (TimedAlphaCanonicalBlockProjection
            machine hb alpha scheduled block candidate) := by
  rw [← finiteRatPropIndicator_forall_eq_prod]
  have hiff :=
    timedAlphaVisitScheduleInPlaceCanonicalCutCheck_iff_blockProjections
      machine hb alpha scheduled candidate
  by_cases hleft : timedAlphaVisitScheduleInPlaceCanonicalCutCheck
      (cachedInputMachine machine) (List.ofFn candidate)
        alpha scheduled = true
  · have hright := hiff.1 hleft
    simp [finiteRatPropIndicator, hleft, hright]
  · have hright : ¬ ∀ block : Fin (T / b + 1),
        TimedAlphaCanonicalBlockProjection
          machine hb alpha scheduled block candidate :=
      fun hall => hleft (hiff.2 hall)
    simp [finiteRatPropIndicator, hleft, hright]

end OneTapeMagnification
end Frontier
end Pnp4
