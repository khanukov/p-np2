import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.OnePassFixedAlphaBlockList
import Pnp4.Frontier.OneTapeMagnification.AdvertisedBlockCandidateGeometry
import Pnp4.Frontier.OneTapeMagnification.OneSidedCutMinimumCheck

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# One-pass cut checks at the two boundaries of one advertised block

For one advertised work block, only two windows of candidate cuts can be
relevant: the bucket immediately to its left and the bucket immediately to
its right.  The initial block has only the right window, and the final block
has only the left window.  We nevertheless use one uniform `Fin (b + b)`
counter vector, filling a missing edge window with a harmless dummy boundary.

The local check is necessarily asymmetric.  The current block checks the
right-hand candidates of its left cut and the left-hand candidates of its
right cut.  `AdvertisedBlockCandidateGeometry` proves that precisely those
candidate boundaries lie strictly inside the current slab.  The complementary
halves are owned by the neighbouring blocks.  Accordingly, the final theorem
below exposes the exact complementary-half hypotheses needed to recover full
leftmost-minimum conditions; it does not claim a global block compiler.
-/

/-- The two adjacent `b`-windows packed into one vector.  At an edge block,
the absent window is mapped to boundary `0`; none of its coordinates is read
by the edge-aware checker. -/
def advertisedBlockTwoWindowBoundaries {T b : Nat}
    (block : Fin (T / b + 1)) : Fin (b + b) -> Nat :=
  Fin.addCases
    (fun candidate =>
      if hleft : 0 < block.val then
        (fullBucketBoundary
          (show Fin (T / b) from
            ⟨block.val - 1, by omega⟩) candidate).val
      else 0)
    (fun candidate =>
      if hright : block.val < T / b then
        (fullBucketBoundary
          (show Fin (T / b) from ⟨block.val, hright⟩) candidate).val
      else 0)

@[simp]
theorem advertisedBlockTwoWindowBoundaries_left {T b : Nat}
    (block : Fin (T / b + 1)) (hleft : 0 < block.val)
    (candidate : Fin b) :
    advertisedBlockTwoWindowBoundaries block (Fin.castAdd b candidate) =
      (fullBucketBoundary
        (show Fin (T / b) from ⟨block.val - 1, by omega⟩) candidate).val := by
  simp [advertisedBlockTwoWindowBoundaries, hleft]

@[simp]
theorem advertisedBlockTwoWindowBoundaries_right {T b : Nat}
    (block : Fin (T / b + 1)) (hright : block.val < T / b)
    (candidate : Fin b) :
    advertisedBlockTwoWindowBoundaries block (Fin.natAdd b candidate) =
      (fullBucketBoundary
        (show Fin (T / b) from ⟨block.val, hright⟩) candidate).val := by
  unfold advertisedBlockTwoWindowBoundaries
  rw [Fin.addCases_right]
  simp [hright]

/-- Run all supplied visits of one block once, threading one slab and one
bounded vector containing exactly the two adjacent `b`-windows. -/
def onePassAdvertisedBlockTwoWindowRun
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit machine.State T)) :
    OnePassFixedAlphaBlockListResult T (b + b)
      (advertisedBlockWidth alpha.offsets block) :=
  onePassFixedAlphaBlockList (H := T) machine input alpha block
    (advertisedBlockTwoWindowBoundaries block) initialSlab visits

/-- Every left-window coordinate is exact for the recursive local replay. -/
theorem onePassAdvertisedBlockTwoWindowRun_left_val
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1)) (hleft : 0 < block.val)
    (initialSlab : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit machine.State T))
    (hsteps : fixedAlphaBlockVisitsTotalSteps visits <= T)
    (candidate : Fin b) :
    ((onePassAdvertisedBlockTwoWindowRun machine input alpha block
        initialSlab visits).counters (Fin.castAdd b candidate)).val =
      fixedAlphaBlockVisitListStreamingCrossingCount machine input alpha block
        (fullBucketBoundary
          (show Fin (T / b) from
            ⟨block.val - 1, by omega⟩) candidate).val
        initialSlab visits := by
  unfold onePassAdvertisedBlockTwoWindowRun
  rw [onePassFixedAlphaBlockList_counter_val machine input alpha block
    (advertisedBlockTwoWindowBoundaries block) initialSlab visits hsteps
    (Fin.castAdd b candidate)]
  rw [advertisedBlockTwoWindowBoundaries_left block hleft candidate]

/-- Every right-window coordinate is exact for the recursive local replay. -/
theorem onePassAdvertisedBlockTwoWindowRun_right_val
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1)) (hright : block.val < T / b)
    (initialSlab : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit machine.State T))
    (hsteps : fixedAlphaBlockVisitsTotalSteps visits <= T)
    (candidate : Fin b) :
    ((onePassAdvertisedBlockTwoWindowRun machine input alpha block
        initialSlab visits).counters (Fin.natAdd b candidate)).val =
      fixedAlphaBlockVisitListStreamingCrossingCount machine input alpha block
        (fullBucketBoundary
          (show Fin (T / b) from ⟨block.val, hright⟩) candidate).val
        initialSlab visits := by
  unfold onePassAdvertisedBlockTwoWindowRun
  rw [onePassFixedAlphaBlockList_counter_val machine input alpha block
    (advertisedBlockTwoWindowBoundaries block) initialSlab visits hsteps
    (Fin.natAdd b candidate)]
  rw [advertisedBlockTwoWindowBoundaries_right block hright candidate]

/-- Complete a right-half check with canonical dummy values on the ignored
left half. -/
def completeOneSidedRightHalf {b : Nat}
    (selected : Nat) (offset : Fin b) (values : Fin b -> Nat) : Fin b -> Nat :=
  fun candidate =>
    if candidate.val < offset.val then selected + 1
    else if candidate = offset then selected
    else values candidate

/-- Complete a left-half check with canonical dummy values on the ignored
right half. -/
def completeOneSidedLeftHalf {b : Nat}
    (selected : Nat) (offset : Fin b) (values : Fin b -> Nat) : Fin b -> Nat :=
  fun candidate =>
    if candidate.val < offset.val then values candidate else selected

/-- Executable check of only the right half of a one-sided minimum. -/
def oneSidedRightHalfCheck {b : Nat}
    (selected : Nat) (offset : Fin b) (values : Fin b -> Nat) : Bool :=
  oneSidedLeftmostMinimumCheck selected offset
    (completeOneSidedRightHalf selected offset values)

/-- Executable check of only the left half of a one-sided minimum. -/
def oneSidedLeftHalfCheck {b : Nat}
    (selected : Nat) (offset : Fin b) (values : Fin b -> Nat) : Bool :=
  oneSidedLeftmostMinimumCheck selected offset
    (completeOneSidedLeftHalf selected offset values)

theorem oneSidedRightHalfCheck_eq_true_iff {b : Nat}
    (selected : Nat) (offset : Fin b) (values : Fin b -> Nat) :
    oneSidedRightHalfCheck selected offset values = true <->
      forall candidate : Fin b, offset.val < candidate.val ->
        selected <= values candidate := by
  rw [oneSidedRightHalfCheck,
    oneSidedLeftmostMinimumCheck_eq_true_iff]
  constructor
  · rintro ⟨_, hright⟩ candidate hcandidate
    have hnot : ¬ candidate.val < offset.val := by omega
    have hne : candidate ≠ offset := by
      intro heq
      subst candidate
      omega
    simpa [completeOneSidedRightHalf, hnot, hne] using
      hright candidate hcandidate
  · intro hright
    constructor
    · intro candidate hcandidate
      simp [completeOneSidedRightHalf, hcandidate]
    · intro candidate hcandidate
      have hnot : ¬ candidate.val < offset.val := by omega
      have hne : candidate ≠ offset := by
        intro heq
        subst candidate
        omega
      simpa [completeOneSidedRightHalf, hnot, hne] using
        hright candidate hcandidate

theorem oneSidedLeftHalfCheck_eq_true_iff {b : Nat}
    (selected : Nat) (offset : Fin b) (values : Fin b -> Nat) :
    oneSidedLeftHalfCheck selected offset values = true <->
      forall candidate : Fin b, candidate.val < offset.val ->
        selected < values candidate := by
  rw [oneSidedLeftHalfCheck,
    oneSidedLeftmostMinimumCheck_eq_true_iff]
  constructor
  · rintro ⟨hleft, _⟩ candidate hcandidate
    simpa [completeOneSidedLeftHalf, hcandidate] using
      hleft candidate hcandidate
  · intro hleft
    constructor
    · intro candidate hcandidate
      simpa [completeOneSidedLeftHalf, hcandidate] using
        hleft candidate hcandidate
    · intro candidate hcandidate
      have hnot : ¬ candidate.val < offset.val := by omega
      simp [completeOneSidedLeftHalf, hnot]

/-- Geometry package for exactly the candidates consumed by the two local
half-checks.  Its quantified form is uniform at initial and final blocks. -/
theorem advertisedBlockTwoWindow_relevantCandidateGeometry
    {T b : Nat} (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1)) :
    (forall (hleft : 0 < block.val) (candidate : Fin b),
      (offsets
          (show Fin (T / b) from ⟨block.val - 1, by omega⟩)).val <
        candidate.val ->
      WorkBoundaryStrictlyInsideAdvertisedBlock offsets block
        (fullBucketBoundary
          (show Fin (T / b) from
            ⟨block.val - 1, by omega⟩) candidate)) /\
    forall (hright : block.val < T / b) (candidate : Fin b),
      candidate.val <
          (offsets (show Fin (T / b) from
            ⟨block.val, hright⟩)).val ->
      WorkBoundaryStrictlyInsideAdvertisedBlock offsets block
        (fullBucketBoundary
          (show Fin (T / b) from ⟨block.val, hright⟩) candidate) := by
  constructor
  · intro hleft candidate hcandidate
    exact leftBucketTailCandidate_strictlyInsideAdvertisedBlock
      offsets block hleft candidate hcandidate
  · intro hright candidate hcandidate
    exact rightBucketPrefixCandidate_strictlyInsideAdvertisedBlock
      offsets block hright candidate hcandidate

/-- The executable block-local check.  The left window checks the tail of
the left bucket, while the right window checks the prefix of the right
bucket.  Missing edge windows reduce definitionally to `true`. -/
def advertisedBlockTwoWindowOneSidedCheck
    {T b H width : Nat} (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1)) (selectedCounts : Fin (T / b) -> Nat)
    (result : OnePassFixedAlphaBlockListResult H (b + b) width) : Bool :=
  (if hleft : 0 < block.val then
      let left : Fin (T / b) := ⟨block.val - 1, by omega⟩
      oneSidedRightHalfCheck (selectedCounts left) (offsets left)
        (fun candidate =>
          (result.counters (Fin.castAdd b candidate)).val)
    else true) &&
  (if hright : block.val < T / b then
      let right : Fin (T / b) := ⟨block.val, hright⟩
      oneSidedLeftHalfCheck (selectedCounts right) (offsets right)
        (fun candidate =>
          (result.counters (Fin.natAdd b candidate)).val)
    else true)

/-- Semantic form of the two local halves, stated directly on the packed
counter vector. -/
def AdvertisedBlockTwoWindowCounterCondition
    {T b H width : Nat} (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1)) (selectedCounts : Fin (T / b) -> Nat)
    (result : OnePassFixedAlphaBlockListResult H (b + b) width) : Prop :=
  (forall (hleft : 0 < block.val) (candidate : Fin b),
      (offsets
          (show Fin (T / b) from ⟨block.val - 1, by omega⟩)).val <
        candidate.val ->
      selectedCounts
          (show Fin (T / b) from ⟨block.val - 1, by omega⟩) <=
        (result.counters (Fin.castAdd b candidate)).val) /\
    forall (hright : block.val < T / b) (candidate : Fin b),
      candidate.val <
          (offsets
            (show Fin (T / b) from ⟨block.val, hright⟩)).val ->
      selectedCounts
          (show Fin (T / b) from ⟨block.val, hright⟩) <
        (result.counters (Fin.natAdd b candidate)).val

private theorem dependentBoolIf_eq_true_iff
    (P : Prop) [Decidable P] (check : P -> Bool) :
    (if h : P then check h else true) = true <->
      forall h : P, check h = true := by
  by_cases hp : P
  · simp only [dif_pos hp]
    constructor
    · intro hcheck hproof
      simpa only [Subsingleton.elim hproof hp] using hcheck
    · intro h
      exact h hp
  · simp [hp]

/-- Exact Boolean reflection, including the initial and final edge blocks. -/
theorem advertisedBlockTwoWindowOneSidedCheck_eq_true_iff
    {T b H width : Nat} (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1)) (selectedCounts : Fin (T / b) -> Nat)
    (result : OnePassFixedAlphaBlockListResult H (b + b) width) :
    advertisedBlockTwoWindowOneSidedCheck offsets block selectedCounts result =
        true <->
      AdvertisedBlockTwoWindowCounterCondition
        offsets block selectedCounts result := by
  unfold advertisedBlockTwoWindowOneSidedCheck
    AdvertisedBlockTwoWindowCounterCondition
  simp only [Bool.and_eq_true]
  rw [dependentBoolIf_eq_true_iff, dependentBoolIf_eq_true_iff]
  constructor
  · rintro ⟨hleft, hright⟩
    constructor
    · intro hleftProof candidate hcandidate
      exact (oneSidedRightHalfCheck_eq_true_iff _ _ _).1
        (hleft hleftProof) candidate hcandidate
    · intro hrightProof candidate hcandidate
      exact (oneSidedLeftHalfCheck_eq_true_iff _ _ _).1
        (hright hrightProof) candidate hcandidate
  · rintro ⟨hleft, hright⟩
    constructor
    · intro hleftProof
      exact (oneSidedRightHalfCheck_eq_true_iff _ _ _).2
        (hleft hleftProof)
    · intro hrightProof
      exact (oneSidedLeftHalfCheck_eq_true_iff _ _ _).2
        (hright hrightProof)

/-- The same two local halves stated against an arbitrary crossing profile.
This is the interface used to glue neighbouring block checks. -/
def AdvertisedBlockRelevantOneSidedMinimum {T b : Nat}
    (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1)) (selectedCounts : Fin (T / b) -> Nat)
    (crossings : Fin T -> Nat) : Prop :=
  (forall (hleft : 0 < block.val) (candidate : Fin b),
      (offsets
          (show Fin (T / b) from ⟨block.val - 1, by omega⟩)).val <
        candidate.val ->
      selectedCounts
          (show Fin (T / b) from ⟨block.val - 1, by omega⟩) <=
        crossings (fullBucketBoundary
          (show Fin (T / b) from ⟨block.val - 1, by omega⟩)
          candidate)) /\
    forall (hright : block.val < T / b) (candidate : Fin b),
      candidate.val <
          (offsets
            (show Fin (T / b) from ⟨block.val, hright⟩)).val ->
      selectedCounts
          (show Fin (T / b) from ⟨block.val, hright⟩) <
        crossings (fullBucketBoundary
          (show Fin (T / b) from ⟨block.val, hright⟩) candidate)

/-- Once the two relevant windows are exact for a crossing profile, the
packed-counter condition is exactly the semantic two-half condition. -/
theorem advertisedBlockTwoWindowCounterCondition_iff_relevant_of_exact
    {T b H width : Nat} (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1)) (selectedCounts : Fin (T / b) -> Nat)
    (result : OnePassFixedAlphaBlockListResult H (b + b) width)
    (crossings : Fin T -> Nat)
    (hleftExact : forall (hleft : 0 < block.val) (candidate : Fin b),
      (result.counters (Fin.castAdd b candidate)).val =
        crossings (fullBucketBoundary
          (show Fin (T / b) from ⟨block.val - 1, by omega⟩)
          candidate))
    (hrightExact : forall (hright : block.val < T / b) (candidate : Fin b),
      (result.counters (Fin.natAdd b candidate)).val =
        crossings (fullBucketBoundary
          (show Fin (T / b) from ⟨block.val, hright⟩) candidate)) :
    AdvertisedBlockTwoWindowCounterCondition
        offsets block selectedCounts result <->
      AdvertisedBlockRelevantOneSidedMinimum
        offsets block selectedCounts crossings := by
  constructor
  · rintro ⟨hleft, hright⟩
    constructor
    · intro hleftProof candidate hcandidate
      rw [<- hleftExact hleftProof candidate]
      exact hleft hleftProof candidate hcandidate
    · intro hrightProof candidate hcandidate
      rw [<- hrightExact hrightProof candidate]
      exact hright hrightProof candidate hcandidate
  · rintro ⟨hleft, hright⟩
    constructor
    · intro hleftProof candidate hcandidate
      rw [hleftExact hleftProof candidate]
      exact hleft hleftProof candidate hcandidate
    · intro hrightProof candidate hcandidate
      rw [hrightExact hrightProof candidate]
      exact hright hrightProof candidate hcandidate

/-- Reflection directly against an exact semantic crossing profile. -/
theorem advertisedBlockTwoWindowOneSidedCheck_eq_true_iff_of_exact
    {T b H width : Nat} (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1)) (selectedCounts : Fin (T / b) -> Nat)
    (result : OnePassFixedAlphaBlockListResult H (b + b) width)
    (crossings : Fin T -> Nat)
    (hleftExact : forall (hleft : 0 < block.val) (candidate : Fin b),
      (result.counters (Fin.castAdd b candidate)).val =
        crossings (fullBucketBoundary
          (show Fin (T / b) from ⟨block.val - 1, by omega⟩)
          candidate))
    (hrightExact : forall (hright : block.val < T / b) (candidate : Fin b),
      (result.counters (Fin.natAdd b candidate)).val =
        crossings (fullBucketBoundary
          (show Fin (T / b) from ⟨block.val, hright⟩) candidate)) :
    advertisedBlockTwoWindowOneSidedCheck
        offsets block selectedCounts result = true <->
      AdvertisedBlockRelevantOneSidedMinimum
        offsets block selectedCounts crossings := by
  rw [advertisedBlockTwoWindowOneSidedCheck_eq_true_iff,
    advertisedBlockTwoWindowCounterCondition_iff_relevant_of_exact
      offsets block selectedCounts result crossings hleftExact hrightExact]

/-- Crossing profile contributed by the supplied visit list of one block. -/
def fixedAlphaBlockVisitListCrossingProfile
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (initialSlab : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit machine.State T)) : Fin T -> Nat :=
  fun boundary =>
    fixedAlphaBlockVisitListStreamingCrossingCount machine input alpha block
      boundary.val initialSlab visits

/-- The actual one-pass run reflects exactly the relevant one-sided
conditions on its locally replayed crossing profile. -/
theorem onePassAdvertisedBlockTwoWindowCheck_eq_true_iff_local
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (selectedCounts : Fin (T / b) -> Nat)
    (initialSlab : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit machine.State T))
    (hsteps : fixedAlphaBlockVisitsTotalSteps visits <= T) :
    advertisedBlockTwoWindowOneSidedCheck alpha.offsets block selectedCounts
        (onePassAdvertisedBlockTwoWindowRun machine input alpha block
          initialSlab visits) = true <->
      AdvertisedBlockRelevantOneSidedMinimum alpha.offsets block
        selectedCounts
        (fixedAlphaBlockVisitListCrossingProfile machine input alpha block
          initialSlab visits) := by
  apply advertisedBlockTwoWindowOneSidedCheck_eq_true_iff_of_exact
  · intro hleft candidate
    exact onePassAdvertisedBlockTwoWindowRun_left_val machine input alpha
      block hleft initialSlab visits hsteps candidate
  · intro hright candidate
    exact onePassAdvertisedBlockTwoWindowRun_right_val machine input alpha
      block hright initialSlab visits hsteps candidate

/-- The complementary halves owned by neighbouring advertised blocks: the
prefix of the left bucket and the tail of the right bucket. -/
def AdvertisedBlockComplementaryOneSidedMinimum {T b : Nat}
    (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1)) (selectedCounts : Fin (T / b) -> Nat)
    (crossings : Fin T -> Nat) : Prop :=
  (forall (hleft : 0 < block.val) (candidate : Fin b),
      candidate.val <
          (offsets
            (show Fin (T / b) from ⟨block.val - 1, by omega⟩)).val ->
      selectedCounts
          (show Fin (T / b) from ⟨block.val - 1, by omega⟩) <
        crossings (fullBucketBoundary
          (show Fin (T / b) from ⟨block.val - 1, by omega⟩)
          candidate)) /\
    forall (hright : block.val < T / b) (candidate : Fin b),
      (offsets
          (show Fin (T / b) from ⟨block.val, hright⟩)).val <
        candidate.val ->
      selectedCounts
          (show Fin (T / b) from ⟨block.val, hright⟩) <=
        crossings (fullBucketBoundary
          (show Fin (T / b) from ⟨block.val, hright⟩) candidate)

/-- Full leftmost-minimum conditions for every cut adjacent to this block.
At an edge, the missing adjacent cut contributes no obligation. -/
def AdvertisedBlockAdjacentCutsLeftmostMinimum {T b : Nat}
    (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1)) (crossings : Fin T -> Nat) : Prop :=
  (forall hleft : 0 < block.val,
      AdvertisedCutOffsetIsLeftmostMinimum crossings
        (show Fin (T / b) from ⟨block.val - 1, by omega⟩)
        (offsets
          (show Fin (T / b) from ⟨block.val - 1, by omega⟩))) /\
    forall hright : block.val < T / b,
      AdvertisedCutOffsetIsLeftmostMinimum crossings
        (show Fin (T / b) from ⟨block.val, hright⟩)
        (offsets (show Fin (T / b) from ⟨block.val, hright⟩))

/-- The two halves checked in the current block plus the two halves checked
in its neighbours are exactly the full leftmost-minimum conditions for both
adjacent cuts. -/
theorem advertisedBlock_relevant_and_complementary_iff_adjacentCuts
    {T b : Nat} (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1)) (selectedCounts : Fin (T / b) -> Nat)
    (crossings : Fin T -> Nat)
    (hselected : forall bucket : Fin (T / b),
      selectedCounts bucket =
        crossings (fullBucketBoundary bucket (offsets bucket))) :
    (AdvertisedBlockRelevantOneSidedMinimum
        offsets block selectedCounts crossings /\
      AdvertisedBlockComplementaryOneSidedMinimum
        offsets block selectedCounts crossings) <->
      AdvertisedBlockAdjacentCutsLeftmostMinimum
        offsets block crossings := by
  constructor
  · rintro ⟨⟨hleftTail, hrightPrefix⟩,
      ⟨hleftPrefix, hrightTail⟩⟩
    constructor
    · intro hleft
      let left : Fin (T / b) := ⟨block.val - 1, by omega⟩
      apply (oneSidedLeftmostMinimum_bucket_iff crossings left
        (offsets left)).1
      constructor
      · intro candidate hcandidate
        rw [<- hselected left]
        exact hleftPrefix hleft candidate hcandidate
      · intro candidate hcandidate
        rw [<- hselected left]
        exact hleftTail hleft candidate hcandidate
    · intro hright
      let right : Fin (T / b) := ⟨block.val, hright⟩
      apply (oneSidedLeftmostMinimum_bucket_iff crossings right
        (offsets right)).1
      constructor
      · intro candidate hcandidate
        rw [<- hselected right]
        exact hrightPrefix hright candidate hcandidate
      · intro candidate hcandidate
        rw [<- hselected right]
        exact hrightTail hright candidate hcandidate
  · rintro ⟨hleftFull, hrightFull⟩
    have hleftOneSided : forall hleft : 0 < block.val,
        OneSidedLeftmostMinimum
          (crossings (fullBucketBoundary
            (show Fin (T / b) from ⟨block.val - 1, by omega⟩)
            (offsets
              (show Fin (T / b) from ⟨block.val - 1, by omega⟩))))
          (offsets
            (show Fin (T / b) from ⟨block.val - 1, by omega⟩))
          (fun candidate => crossings (fullBucketBoundary
            (show Fin (T / b) from ⟨block.val - 1, by omega⟩)
            candidate)) := by
      intro hleft
      exact (oneSidedLeftmostMinimum_bucket_iff crossings
        (show Fin (T / b) from ⟨block.val - 1, by omega⟩)
        (offsets
          (show Fin (T / b) from ⟨block.val - 1, by omega⟩))).2
        (hleftFull hleft)
    have hrightOneSided : forall hright : block.val < T / b,
        OneSidedLeftmostMinimum
          (crossings (fullBucketBoundary
            (show Fin (T / b) from ⟨block.val, hright⟩)
            (offsets (show Fin (T / b) from ⟨block.val, hright⟩))))
          (offsets (show Fin (T / b) from ⟨block.val, hright⟩))
          (fun candidate => crossings (fullBucketBoundary
            (show Fin (T / b) from ⟨block.val, hright⟩)
            candidate)) := by
      intro hright
      exact (oneSidedLeftmostMinimum_bucket_iff crossings
        (show Fin (T / b) from ⟨block.val, hright⟩)
        (offsets (show Fin (T / b) from ⟨block.val, hright⟩))).2
        (hrightFull hright)
    constructor
    · constructor
      · intro hleft candidate hcandidate
        rw [hselected]
        exact (hleftOneSided hleft).2 candidate hcandidate
      · intro hright candidate hcandidate
        rw [hselected]
        exact (hrightOneSided hright).1 candidate hcandidate
    · constructor
      · intro hleft candidate hcandidate
        rw [hselected]
        exact (hleftOneSided hleft).1 candidate hcandidate
      · intro hright candidate hcandidate
        rw [hselected]
        exact (hrightOneSided hright).2 candidate hcandidate

/-- Main two-window sufficiency theorem.  If the final packed coordinates
are exact for a crossing profile, the selected coordinates have their
advertised values, and neighbouring blocks supply the complementary halves,
then this block's single Boolean check is equivalent to full leftmost-minimum
for both adjacent cuts. -/
theorem advertisedBlockTwoWindowOneSidedCheck_eq_true_iff_adjacentCuts_of_exact
    {T b H width : Nat} (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1)) (selectedCounts : Fin (T / b) -> Nat)
    (result : OnePassFixedAlphaBlockListResult H (b + b) width)
    (crossings : Fin T -> Nat)
    (hleftExact : forall (hleft : 0 < block.val) (candidate : Fin b),
      (result.counters (Fin.castAdd b candidate)).val =
        crossings (fullBucketBoundary
          (show Fin (T / b) from ⟨block.val - 1, by omega⟩)
          candidate))
    (hrightExact : forall (hright : block.val < T / b) (candidate : Fin b),
      (result.counters (Fin.natAdd b candidate)).val =
        crossings (fullBucketBoundary
          (show Fin (T / b) from ⟨block.val, hright⟩) candidate))
    (hselected : forall bucket : Fin (T / b),
      selectedCounts bucket =
        crossings (fullBucketBoundary bucket (offsets bucket)))
    (hcomplementary : AdvertisedBlockComplementaryOneSidedMinimum
      offsets block selectedCounts crossings) :
    advertisedBlockTwoWindowOneSidedCheck
        offsets block selectedCounts result = true <->
      AdvertisedBlockAdjacentCutsLeftmostMinimum
        offsets block crossings := by
  have hreflect :=
    advertisedBlockTwoWindowOneSidedCheck_eq_true_iff_of_exact
      offsets block selectedCounts result crossings hleftExact hrightExact
  have hglue :=
    advertisedBlock_relevant_and_complementary_iff_adjacentCuts
      offsets block selectedCounts crossings hselected
  constructor
  · intro hcheck
    exact hglue.1 ⟨hreflect.1 hcheck, hcomplementary⟩
  · intro hfull
    exact hreflect.2 (hglue.2 hfull).1

/-- One-pass specialization of the main theorem.  Coordinate exactness is
discharged by `OnePassFixedAlphaBlockList`; only the mathematically necessary
selected-count and neighbouring-half glue hypotheses remain. -/
theorem onePassAdvertisedBlockTwoWindowCheck_eq_true_iff_adjacentCuts
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (selectedCounts : Fin (T / b) -> Nat)
    (initialSlab : WorkSlab (advertisedBlockWidth alpha.offsets block))
    (visits : List (FixedAlphaBlockVisit machine.State T))
    (hsteps : fixedAlphaBlockVisitsTotalSteps visits <= T)
    (hselected : forall bucket : Fin (T / b),
      selectedCounts bucket =
        fixedAlphaBlockVisitListCrossingProfile machine input alpha block
          initialSlab visits
          (fullBucketBoundary bucket (alpha.offsets bucket)))
    (hcomplementary : AdvertisedBlockComplementaryOneSidedMinimum
      alpha.offsets block selectedCounts
      (fixedAlphaBlockVisitListCrossingProfile machine input alpha block
        initialSlab visits)) :
    advertisedBlockTwoWindowOneSidedCheck alpha.offsets block selectedCounts
        (onePassAdvertisedBlockTwoWindowRun machine input alpha block
          initialSlab visits) = true <->
      AdvertisedBlockAdjacentCutsLeftmostMinimum alpha.offsets block
        (fixedAlphaBlockVisitListCrossingProfile machine input alpha block
          initialSlab visits) := by
  apply advertisedBlockTwoWindowOneSidedCheck_eq_true_iff_adjacentCuts_of_exact
    alpha.offsets block selectedCounts
    (onePassAdvertisedBlockTwoWindowRun machine input alpha block
      initialSlab visits)
    (fixedAlphaBlockVisitListCrossingProfile machine input alpha block
      initialSlab visits)
  · intro hleft candidate
    exact onePassAdvertisedBlockTwoWindowRun_left_val machine input alpha
      block hleft initialSlab visits hsteps candidate
  · intro hright candidate
    exact onePassAdvertisedBlockTwoWindowRun_right_val machine input alpha
      block hright initialSlab visits hsteps candidate
  · exact hselected
  · exact hcomplementary

/-- At an initial block the absent left window disappears: only the prefix
of the right bucket is checked. -/
theorem advertisedBlockTwoWindowOneSidedCheck_initial
    {T b H width : Nat} (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1)) (hzero : block.val = 0)
    (hright : block.val < T / b)
    (selectedCounts : Fin (T / b) -> Nat)
    (result : OnePassFixedAlphaBlockListResult H (b + b) width) :
    advertisedBlockTwoWindowOneSidedCheck offsets block selectedCounts result =
      oneSidedLeftHalfCheck
        (selectedCounts
          (show Fin (T / b) from ⟨block.val, hright⟩))
        (offsets (show Fin (T / b) from ⟨block.val, hright⟩))
        (fun candidate =>
          (result.counters (Fin.natAdd b candidate)).val) := by
  unfold advertisedBlockTwoWindowOneSidedCheck
  have hnotLeft : ¬ 0 < block.val := by omega
  simp [hnotLeft, hright]

/-- At a final noninitial block the absent right window disappears: only the
tail of the left bucket is checked. -/
theorem advertisedBlockTwoWindowOneSidedCheck_final
    {T b H width : Nat} (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1)) (hleft : 0 < block.val)
    (hfinal : ¬ block.val < T / b)
    (selectedCounts : Fin (T / b) -> Nat)
    (result : OnePassFixedAlphaBlockListResult H (b + b) width) :
    advertisedBlockTwoWindowOneSidedCheck offsets block selectedCounts result =
      oneSidedRightHalfCheck
        (selectedCounts
          (show Fin (T / b) from ⟨block.val - 1, by omega⟩))
        (offsets
          (show Fin (T / b) from ⟨block.val - 1, by omega⟩))
        (fun candidate =>
          (result.counters (Fin.castAdd b candidate)).val) := by
  unfold advertisedBlockTwoWindowOneSidedCheck
  simp [hleft, hfinal]

/-- If there are no full buckets, the unique edge block has no cut
obligations and its two-window check accepts. -/
theorem advertisedBlockTwoWindowOneSidedCheck_noFullBuckets
    {T b H width : Nat} (offsets : CanonicalCutOffsets T b)
    (block : Fin (T / b + 1)) (hnoBuckets : T / b = 0)
    (selectedCounts : Fin (T / b) -> Nat)
    (result : OnePassFixedAlphaBlockListResult H (b + b) width) :
    advertisedBlockTwoWindowOneSidedCheck
      offsets block selectedCounts result = true := by
  unfold advertisedBlockTwoWindowOneSidedCheck
  have hzero : block.val = 0 := by omega
  have hnotLeft : ¬ 0 < block.val := by omega
  have hnotRight : ¬ block.val < T / b := by omega
  simp [hnotLeft, hnotRight]

end OneTapeMagnification
end Frontier
end Pnp4
