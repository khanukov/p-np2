import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.ExecutableTimedAlphaComponent

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Selected-cut crossing multiplicity hardwired in timed alpha

Every decoded timed token names the selected bucket whose advertised cut was
crossed.  Therefore, for fixed alpha, the number of crossings of an advertised
selected cut can be obtained without a live counter: it is the multiplicity
of that bucket label in the hardwired token word.

This file proves that statement for the chronological alpha and transfers it
to every alpha accepted by the executable canonical component.  Candidate
boundaries still require the one-pass live vector; this result supplies the
comparison value for the selected boundary itself.
-/

/-- Number of decoded timed tokens carrying one selected-bucket label. -/
def advertisedSelectedCutMultiplicity
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (bucket : Fin (T / b)) : Nat :=
  List.countP (fun crossing => decide (crossing.token.1 = bucket))
    (decodePaddedWord (T / b) alpha.word)

private theorem countP_eq_sum_indicators {α : Type}
    (predicate : α → Bool) (items : List α) :
    List.countP predicate items =
      (items.map fun item => if predicate item = true then 1 else 0).sum := by
  induction items with
  | nil => simp
  | cons item items ih =>
      rw [List.countP_cons]
      simp only [List.map_cons, List.sum_cons, ih]
      omega

private theorem countP_finRange_eq_sum {n : Nat}
    (predicate : Fin n → Bool) :
    List.countP predicate (List.finRange n) =
      ∑ i : Fin n, if predicate i = true then 1 else 0 := by
  rw [countP_eq_sum_indicators, ← List.ofFn_id,
    List.map_ofFn, List.sum_ofFn]
  rfl

/-- The chronological occurrence chooses a bucket iff that bucket's canonical
boundary is crossed at the occurrence time. -/
theorem chronologicalSelectedBoundaryOfOccurrence_eq_iff_crossing
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (occurrence : ChronologicalSelectedCrossingOccurrence
      machine input T b hb) (bucket : Fin (T / b)) :
    chronologicalSelectedBoundaryOfOccurrence
        machine input T b hb occurrence = bucket ↔
      WorkBoundaryCrossingAt machine input occurrence.val.val
        (canonicalBoundary hb
          (actualWorkBoundaryCounts machine input T) bucket).val := by
  constructor
  · intro heq
    rw [← heq]
    exact chronologicalSelectedBoundaryOfOccurrence_crossing
      machine input T b hb occurrence
  · intro hcross
    exact (chronologicalSelectedBoundaryOfOccurrence_unique
      machine input T b hb occurrence bucket hcross).symm

/-- For the extracted chronological alpha, bucket-label multiplicity is the
actual crossing count of that bucket's canonical cut. -/
theorem advertisedSelectedCutMultiplicity_chronological_eq_actual
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) (bucket : Fin (T / b)) :
    advertisedSelectedCutMultiplicity
        (chronologicalTimedCanonicalAlpha machine input T b hb) bucket =
      workBoundaryCrossingCount machine input T
        (canonicalWorkBoundary machine input T b hb bucket).val := by
  unfold advertisedSelectedCutMultiplicity
  rw [decode_chronologicalTimedCanonicalAlpha_word]
  rw [chronologicalTimedCanonicalCrossingTokens,
    chronologicalCanonicalCrossingEntries]
  simp only [List.map_map, List.countP_map]
  let times := actualSelectedBoundaryCrossingTimes machine input T b hb
  let occurrencePredicate :
      {time // time ∈ actualSelectedBoundaryCrossingTimes
        machine input T b hb} → Bool :=
    (fun crossing => decide (crossing.token.1 = bucket)) ∘
      timedCanonicalCrossingTokenOfEntry ∘
        chronologicalCanonicalCrossingEntryOfOccurrence
          machine input T b hb
  let crossingPredicate : Fin T → Bool := fun time =>
    decide (WorkBoundaryCrossingAtFrom machine input
      (initialConfiguration machine) time.val
        (canonicalWorkBoundary machine input T b hb bucket).val)
  change List.countP occurrencePredicate times.attach = _
  calc
    List.countP occurrencePredicate times.attach =
        List.countP (fun occurrence => crossingPredicate occurrence.val)
          times.attach := by
      apply List.countP_congr
      intro occurrence _
      change decide
          (chronologicalSelectedBoundaryOfOccurrence
              machine input T b hb occurrence = bucket) = true ↔
        decide (WorkBoundaryCrossingAtFrom machine input
          (initialConfiguration machine) occurrence.val.val
            (canonicalWorkBoundary machine input T b hb bucket).val) = true
      simp only [decide_eq_true_eq]
      simpa [canonicalWorkBoundary, WorkBoundaryCrossingAt] using
        (chronologicalSelectedBoundaryOfOccurrence_eq_iff_crossing
          machine input T b hb occurrence bucket)
    _ = List.countP crossingPredicate times := by
      change List.countP
        (crossingPredicate ∘ fun occurrence => occurrence.val) times.attach = _
      rw [← List.countP_map]
      simp [times]
    _ = List.countP crossingPredicate (List.finRange T) := by
      unfold times actualSelectedBoundaryCrossingTimes
      rw [List.countP_filter]
      apply List.countP_congr
      intro time _
      simp only [crossingPredicate, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · exact fun h => h.1
      · intro hcross
        refine ⟨hcross, ?_⟩
        exact (actualCanonicalWorkBlockAtTime_change_iff_selectedCrossing
          machine input T b hb time.val).2
            ⟨bucket, by
              simpa [canonicalWorkBoundary, WorkBoundaryCrossingAt] using
                hcross⟩
    _ = workBoundaryCrossingCount machine input T
          (canonicalWorkBoundary machine input T b hb bucket).val := by
      rw [countP_finRange_eq_sum]
      unfold workBoundaryCrossingCount workBoundaryCrossingCountFrom
      apply Finset.sum_congr rfl
      intro time _
      simp [crossingPredicate]

/-- Any alpha accepted by the canonical component has the same hardwired
selected-cut multiplicities as the actual run. -/
theorem advertisedSelectedCutMultiplicity_eq_actual_of_componentCheck
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (hcheck : timedAlphaCanonicalComponentCheck
      machine input T b hb alpha = true)
    (bucket : Fin (T / b)) :
    advertisedSelectedCutMultiplicity alpha bucket =
      workBoundaryCrossingCount machine input T
        (fullBucketBoundary bucket (alpha.offsets bucket)) := by
  have halpha := (timedAlphaCanonicalComponentCheck_eq_true_iff
    machine input T b hb alpha).1 hcheck
  subst alpha
  simpa [chronologicalTimedCanonicalAlpha, canonicalWorkBoundary] using
    advertisedSelectedCutMultiplicity_chronological_eq_actual
      machine input T b hb bucket

end OneTapeMagnification
end Frontier
end Pnp4
