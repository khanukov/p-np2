import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.ActualCrossingSchedule
import Pnp4.Frontier.OneTapeMagnification.CanonicalCrossingRecords
import Pnp4.Frontier.OneTapeMagnification.CanonicalCutOffsets
import Pnp4.Frontier.OneTapeMagnification.PaddedCanonicalAlpha

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Chronological canonical alpha extraction

`CanonicalCrossingRecords` enumerates a finite set of selected-cut events by
choice, so its resulting list deliberately carries no chronological-order
theorem.  This file removes that ordering caveat for one concrete run.  It
starts from `actualSelectedBoundaryCrossingTimes`, which is a filter of
`List.finRange T`, identifies the unique selected bucket crossed at each such
time, and extracts the corresponding record in that order.

The chronological token list has length at most `T / b`, retains enough
information to reconstruct every physical cut from the canonical offset
vector, and is faithfully prefix-padded into the existing
`PaddedCanonicalAlpha` carrier.  This is still extraction from one
input-dependent run.  No local-validity predicate, input-independent advice,
branching program, or width bound is asserted here.
-/

/-- Canonical selected cuts in distinct full buckets are distinct. -/
theorem canonicalBoundary_injective {T b : Nat} (hb : 0 < b)
    (crossings : Fin T → Nat) :
    Function.Injective (canonicalBoundary hb crossings) := by
  intro left right hCut
  apply Fin.ext
  by_contra hIndex
  rcases lt_or_gt_of_ne hIndex with hLeft | hRight
  · have hStrict := canonicalBoundary_lt_of_index_lt hb crossings hLeft
    have hVal := congrArg Fin.val hCut
    omega
  · have hStrict := canonicalBoundary_lt_of_index_lt hb crossings hRight
    have hVal := congrArg Fin.val hCut
    omega

/-- At an extracted selected-crossing time there is exactly one selected
full-bucket boundary which is crossed. -/
theorem existsUnique_actualSelectedBoundaryAtTime
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) (time : Fin T)
    (hTime : time ∈ actualSelectedBoundaryCrossingTimes machine input T b hb) :
    ∃! boundary : Fin (T / b),
      WorkBoundaryCrossingAt machine input time.val
        (canonicalBoundary hb
          (actualWorkBoundaryCounts machine input T) boundary).val := by
  obtain ⟨boundary, hCross⟩ :=
    (mem_actualSelectedBoundaryCrossingTimes_iff
      machine input T b hb time).mp hTime
  refine ⟨boundary, hCross, ?_⟩
  intro candidate hCandidate
  have hPhysicalVal :
      (canonicalBoundary hb
          (actualWorkBoundaryCounts machine input T) candidate).val =
        (canonicalBoundary hb
          (actualWorkBoundaryCounts machine input T) boundary).val := by
    exact workBoundaryCrossingAtFrom_unique machine input
      (initialConfiguration machine) time.val hCandidate hCross
  apply canonicalBoundary_injective hb
    (actualWorkBoundaryCounts machine input T)
  exact Fin.ext hPhysicalVal

/-- A selected crossing time together with its exact membership proof. -/
abbrev ChronologicalSelectedCrossingOccurrence
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :=
  { time // time ∈ actualSelectedBoundaryCrossingTimes machine input T b hb }

/-- The unique selected bucket crossed by one chronological occurrence. -/
noncomputable def chronologicalSelectedBoundaryOfOccurrence
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (occurrence : ChronologicalSelectedCrossingOccurrence
      machine input T b hb) : Fin (T / b) :=
  Classical.choose
    ((existsUnique_actualSelectedBoundaryAtTime machine input T b hb
      occurrence.val occurrence.property).exists)

/-- The bucket chosen above really is crossed at the occurrence time. -/
theorem chronologicalSelectedBoundaryOfOccurrence_crossing
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (occurrence : ChronologicalSelectedCrossingOccurrence
      machine input T b hb) :
    WorkBoundaryCrossingAt machine input occurrence.val.val
      (canonicalBoundary hb
        (actualWorkBoundaryCounts machine input T)
        (chronologicalSelectedBoundaryOfOccurrence
          machine input T b hb occurrence)).val := by
  exact Classical.choose_spec
    ((existsUnique_actualSelectedBoundaryAtTime machine input T b hb
      occurrence.val occurrence.property).exists)

/-- The selected-bucket choice is uniquely characterized by its crossing. -/
theorem chronologicalSelectedBoundaryOfOccurrence_unique
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (occurrence : ChronologicalSelectedCrossingOccurrence
      machine input T b hb) (candidate : Fin (T / b))
    (hCandidate : WorkBoundaryCrossingAt machine input occurrence.val.val
      (canonicalBoundary hb
        (actualWorkBoundaryCounts machine input T) candidate).val) :
    candidate = chronologicalSelectedBoundaryOfOccurrence
      machine input T b hb occurrence := by
  exact (existsUnique_actualSelectedBoundaryAtTime machine input T b hb
    occurrence.val occurrence.property).unique hCandidate
      (chronologicalSelectedBoundaryOfOccurrence_crossing
        machine input T b hb occurrence)

/-- Extract the same post-transition payload convention as
`CanonicalCrossingRecords`, now from a chronologically indexed occurrence. -/
noncomputable def chronologicalCanonicalCrossingRecordOfOccurrence
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (occurrence : ChronologicalSelectedCrossingOccurrence
      machine input T b hb) :
    CanonicalCrossingRecord machine.State T b := by
  let boundary := chronologicalSelectedBoundaryOfOccurrence
    machine input T b hb occurrence
  have hCross : WorkBoundaryCrossingAt machine input occurrence.val.val
      (canonicalBoundary hb
        (actualWorkBoundaryCounts machine input T) boundary).val := by
    exact chronologicalSelectedBoundaryOfOccurrence_crossing
      machine input T b hb occurrence
  let postConfig := run machine input (occurrence.val.val + 1)
  exact
    { selectedCut := boundary
      physicalCut := canonicalBoundary hb
        (actualWorkBoundaryCounts machine input T) boundary
      payload :=
        { direction := workCrossingDirectionOf hCross
          postState := postConfig.state
          postInputHead :=
            ⟨postConfig.inputHead, by
              have hTime : occurrence.val.val + 1 ≤ T := occurrence.val.isLt
              exact Nat.lt_succ_of_le
                ((inputHead_run_le_time_for_crossingRecord machine input
                  (occurrence.val.val + 1)).trans hTime)⟩ } }

/-- A timed entry makes the source of the chronological record order explicit. -/
structure ChronologicalCanonicalCrossingEntry
    (State : Type) (T b : Nat) where
  time : Fin T
  record : CanonicalCrossingRecord State T b

/-- Attach the occurrence time to its extracted record. -/
noncomputable def chronologicalCanonicalCrossingEntryOfOccurrence
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (occurrence : ChronologicalSelectedCrossingOccurrence
      machine input T b hb) :
    ChronologicalCanonicalCrossingEntry machine.State T b :=
  { time := occurrence.val
    record := chronologicalCanonicalCrossingRecordOfOccurrence
      machine input T b hb occurrence }

/-- All selected crossings in the chronological order inherited from
`List.finRange T`. -/
noncomputable def chronologicalCanonicalCrossingEntries
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    List (ChronologicalCanonicalCrossingEntry machine.State T b) :=
  (actualSelectedBoundaryCrossingTimes machine input T b hb).attach.map
    (chronologicalCanonicalCrossingEntryOfOccurrence machine input T b hb)

/-- Projecting the times from the entry list recovers the strictly
chronological source list exactly. -/
theorem map_time_chronologicalCanonicalCrossingEntries
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    (chronologicalCanonicalCrossingEntries machine input T b hb).map
        ChronologicalCanonicalCrossingEntry.time =
      actualSelectedBoundaryCrossingTimes machine input T b hb := by
  simp [chronologicalCanonicalCrossingEntries,
    chronologicalCanonicalCrossingEntryOfOccurrence]

/-- The retained source times are strictly increasing, so erasing those times
from the entries preserves a genuinely chronological record/token order. -/
theorem chronologicalCanonicalCrossingEntries_times_pairwise_lt
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    ((chronologicalCanonicalCrossingEntries machine input T b hb).map
      ChronologicalCanonicalCrossingEntry.time).Pairwise
        (fun earlier later => earlier < later) := by
  rw [map_time_chronologicalCanonicalCrossingEntries]
  exact actualSelectedBoundaryCrossingTimes_pairwise_lt
    machine input T b hb

/-- Chronological records with the auxiliary source times erased. -/
noncomputable def chronologicalCanonicalCrossingRecords
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    List (CanonicalCrossingRecord machine.State T b) :=
  (chronologicalCanonicalCrossingEntries machine input T b hb).map
    ChronologicalCanonicalCrossingEntry.record

/-- Erasing source times does not change the number of crossings. -/
theorem length_chronologicalCanonicalCrossingRecords_eq_times
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    (chronologicalCanonicalCrossingRecords machine input T b hb).length =
      (actualSelectedBoundaryCrossingTimes machine input T b hb).length := by
  rw [chronologicalCanonicalCrossingRecords, List.length_map,
    ← List.length_map ChronologicalCanonicalCrossingEntry.time]
  rw [map_time_chronologicalCanonicalCrossingEntries]

/-- The chronological record list obeys the same canonical charging bound. -/
theorem length_chronologicalCanonicalCrossingRecords_le_div
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    (chronologicalCanonicalCrossingRecords machine input T b hb).length ≤
      T / b := by
  rw [length_chronologicalCanonicalCrossingRecords_eq_times]
  exact length_actualSelectedBoundaryCrossingTimes_le_div
    machine input T b hb

/-- Every chronological record's physical cut is recovered from its selected
bucket and the retained canonical offset vector. -/
theorem chronologicalCanonicalCrossingRecordOfOccurrence_physicalCut_recovered
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (occurrence : ChronologicalSelectedCrossingOccurrence
      machine input T b hb) :
    (chronologicalCanonicalCrossingRecordOfOccurrence
        machine input T b hb occurrence).physicalCut =
      physicalCutOfCanonicalToken
        (canonicalCutOffsets machine input T b hb)
        (canonicalCrossingTokenOfRecord
          (chronologicalCanonicalCrossingRecordOfOccurrence
            machine input T b hb occurrence)) := by
  rfl

/-- The physical-cut recovery property holds for every record in the
chronological list. -/
theorem mem_chronologicalCanonicalCrossingRecords_physicalCut_recovered
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (record : CanonicalCrossingRecord machine.State T b)
    (hRecord : record ∈
      chronologicalCanonicalCrossingRecords machine input T b hb) :
    record.physicalCut =
      physicalCutOfCanonicalToken
        (canonicalCutOffsets machine input T b hb)
        (canonicalCrossingTokenOfRecord record) := by
  rw [chronologicalCanonicalCrossingRecords,
    chronologicalCanonicalCrossingEntries] at hRecord
  rcases List.mem_map.mp hRecord with ⟨entry, hEntry, rfl⟩
  rcases List.mem_map.mp hEntry with ⟨occurrence, -, rfl⟩
  exact
    chronologicalCanonicalCrossingRecordOfOccurrence_physicalCut_recovered
      machine input T b hb occurrence

/-- Bucket-labelled payload tokens in the newly proved chronological order. -/
noncomputable def chronologicalCanonicalCrossingTokens
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    List (CanonicalCrossingToken machine.State T b) :=
  (chronologicalCanonicalCrossingRecords machine input T b hb).map
    canonicalCrossingTokenOfRecord

@[simp]
theorem length_chronologicalCanonicalCrossingTokens
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    (chronologicalCanonicalCrossingTokens machine input T b hb).length =
      (chronologicalCanonicalCrossingRecords machine input T b hb).length := by
  simp [chronologicalCanonicalCrossingTokens]

/-- The chronological token list fits in the canonical `T / b` slots. -/
theorem length_chronologicalCanonicalCrossingTokens_le_div
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    (chronologicalCanonicalCrossingTokens machine input T b hb).length ≤
      T / b := by
  rw [length_chronologicalCanonicalCrossingTokens]
  exact length_chronologicalCanonicalCrossingRecords_le_div
    machine input T b hb

/-- The existing padded carrier populated with the chronological token list. -/
noncomputable def chronologicalCanonicalPaddedAlpha
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    PaddedCanonicalAlpha machine.State T b :=
  { offsets := canonicalCutOffsets machine input T b hb
    word := encodePaddedWord (T / b)
      (chronologicalCanonicalCrossingTokens machine input T b hb) }

/-- Prefix decoding exactly recovers the chronological token list. -/
theorem decode_chronologicalCanonicalPaddedAlpha_word
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    decodePaddedWord (T / b)
        (chronologicalCanonicalPaddedAlpha machine input T b hb).word =
      chronologicalCanonicalCrossingTokens machine input T b hb := by
  exact decode_encodePaddedWord (T / b)
    (chronologicalCanonicalCrossingTokens machine input T b hb)
    (length_chronologicalCanonicalCrossingTokens_le_div
      machine input T b hb)

end OneTapeMagnification
end Frontier
end Pnp4
