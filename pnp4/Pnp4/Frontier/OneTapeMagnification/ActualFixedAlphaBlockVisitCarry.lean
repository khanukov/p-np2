import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.ActualBlockVisitPersistence
import Pnp4.Frontier.OneTapeMagnification.ActualGroupFixedAlphaVisit

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Carrying one fixed-alpha slab between two actual visits

The one-group completeness theorem initializes a fixed-alpha visit with the
actual slab restriction at that group's entry.  This file identifies the glue
between two consecutive visits of the same target block.  If every intervening
maximal group has a non-target label, persistence of the target slab shows
that the validator's computed output from the first visit is exactly the
carried entry slab of the second visit.

Consequently the second visit is locally valid when run directly from the
first visit's computed output.  This is the first actual-run instance of the
recursive one-slab fold; it does not reset the slab and does not carry a full
work tape.

The theorem still consumes a true maximal-group decomposition.  It is a
completeness bridge for the actual timed alpha, not a soundness theorem for an
arbitrary advertised word.  Constructing and validating the visit list from
that word remains separate.
-/

/-- Prefix of maximal groups ending immediately before `secondVisit`. -/
def actualSecondVisitPrefix {T : Nat}
    (before : List (List (Fin T))) (firstVisit : List (Fin T))
    (between : List (List (Fin T))) : List (List (Fin T)) :=
  before ++ [firstVisit] ++ between

/-- The decomposition exposing the first of two named visits. -/
theorem actualTwoVisits_first_split
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before : List (List (Fin T)))
    (firstVisit : List (Fin T))
    (between : List (List (Fin T)))
    (secondVisit : List (Fin T))
    (after : List (List (Fin T)))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ [firstVisit] ++ between ++ [secondVisit] ++ after) :
    actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ firstVisit :: (between ++ [secondVisit] ++ after) := by
  simpa [List.append_assoc] using hsplit

/-- The same decomposition exposing the second named visit. -/
theorem actualTwoVisits_second_split
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before : List (List (Fin T)))
    (firstVisit : List (Fin T))
    (between : List (List (Fin T)))
    (secondVisit : List (Fin T))
    (after : List (List (Fin T)))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ [firstVisit] ++ between ++ [secondVisit] ++ after) :
    actualCanonicalWorkBlockRuns machine input T b hb =
      actualSecondVisitPrefix before firstVisit between ++
        secondVisit :: after := by
  simpa [actualSecondVisitPrefix, List.append_assoc] using hsplit

/-- Two distinct maximal visits carrying the same target label cannot be
adjacent: at least one non-target maximal group lies between them. -/
theorem actualTwoTargetVisits_between_ne_nil
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (target : Fin (T / b + 1))
    (before : List (List (Fin T)))
    (firstVisit : List (Fin T))
    (between : List (List (Fin T)))
    (secondVisit : List (Fin T))
    (after : List (List (Fin T)))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ [firstVisit] ++ between ++ [secondVisit] ++ after)
    (hfirstTarget :
      actualCanonicalWorkBlockAtTime machine input T b hb
        (timeGroupsLength before) = target)
    (hsecondTarget :
      actualCanonicalWorkBlockAtTime machine input T b hb
        (timeGroupsLength before + firstVisit.length +
          timeGroupsLength between) = target) :
    between ≠ [] := by
  intro hnil
  subst between
  have hsplitAdjacent :
      actualCanonicalWorkBlockRuns machine input T b hb =
        before ++ firstVisit :: secondVisit :: after := by
    simpa [List.append_assoc] using hsplit
  have hfirstNonempty := actualCanonicalWorkBlockGroup_nonempty
    machine input T b hb before (secondVisit :: after) firstVisit
      hsplitAdjacent
  have hsecondSplit :
      actualCanonicalWorkBlockRuns machine input T b hb =
        (before ++ [firstVisit]) ++ secondVisit :: after := by
    simpa [List.append_assoc] using hsplitAdjacent
  have hsecondNonempty := actualCanonicalWorkBlockGroup_nonempty
    machine input T b hb (before ++ [firstVisit]) after secondVisit
      hsecondSplit
  have hfirstLastLabel := actualCanonicalWorkBlockGroup_label_eq_initial
    machine input T b hb before (secondVisit :: after) firstVisit
      hsplitAdjacent (firstVisit.getLast hfirstNonempty)
      (List.getLast_mem hfirstNonempty)
  have hsecondHeadLabel := actualCanonicalWorkBlockGroup_label_eq_initial
    machine input T b hb (before ++ [firstVisit]) after secondVisit
      hsecondSplit (secondVisit.head hsecondNonempty)
      (List.head_mem hsecondNonempty)
  have hsecondStart :
      timeGroupsLength (before ++ [firstVisit]) =
        timeGroupsLength before + firstVisit.length := by
    simp [timeGroupsLength_append]
  rw [hsecondStart] at hsecondHeadLabel
  have hsecondTarget' :
      actualCanonicalWorkBlockAtTime machine input T b hb
          (timeGroupsLength before + firstVisit.length) = target := by
    simpa using hsecondTarget
  have hchain := actualCanonicalWorkBlockRuns_adjacent_differ
    machine input T b hb
  have hadjacent :=
    (List.chain'_iff_forall_rel_of_append_cons_cons.mp hchain)
      hsplitAdjacent
  rcases hadjacent with ⟨_, _, hdifferent⟩
  apply hdifferent
  exact (hfirstLastLabel.trans hfirstTarget).trans
    (hsecondHeadLabel.trans hsecondTarget').symm

/-- Hence the intervening slice has a positive number of transition times. -/
theorem timeGroupsLength_between_actualTargetVisits_pos
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (target : Fin (T / b + 1))
    (before : List (List (Fin T)))
    (firstVisit : List (Fin T))
    (between : List (List (Fin T)))
    (secondVisit : List (Fin T))
    (after : List (List (Fin T)))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ [firstVisit] ++ between ++ [secondVisit] ++ after)
    (hfirstTarget :
      actualCanonicalWorkBlockAtTime machine input T b hb
        (timeGroupsLength before) = target)
    (hsecondTarget :
      actualCanonicalWorkBlockAtTime machine input T b hb
        (timeGroupsLength before + firstVisit.length +
          timeGroupsLength between) = target) :
    0 < timeGroupsLength between := by
  have hne := actualTwoTargetVisits_between_ne_nil machine input T b hb
    target before firstVisit between secondVisit after hsplit
      hfirstTarget hsecondTarget
  cases between with
  | nil => exact False.elim (hne rfl)
  | cons middle rest =>
      have hmiddleMem : middle ∈
          actualCanonicalWorkBlockRuns machine input T b hb := by
        rw [hsplit]
        simp
      have hmiddleNonempty := actualCanonicalWorkBlockRuns_nonempty
        machine input T b hb hmiddleMem
      rw [timeGroupsLength_cons]
      have hlength : 0 < middle.length :=
        List.length_pos_iff.mpr hmiddleNonempty
      omega

/-- The two actual target visits satisfy the strict separation required by
the fixed-list validator. -/
theorem actualTwoTargetBlockVisits_strictlySeparated
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (target : Fin (T / b + 1))
    (before : List (List (Fin T)))
    (firstVisit : List (Fin T))
    (between : List (List (Fin T)))
    (secondVisit : List (Fin T))
    (after : List (List (Fin T)))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ [firstVisit] ++ between ++ [secondVisit] ++ after)
    (hfirstTarget :
      actualCanonicalWorkBlockAtTime machine input T b hb
        (timeGroupsLength before) = target)
    (hsecondTarget :
      actualCanonicalWorkBlockAtTime machine input T b hb
        (timeGroupsLength before + firstVisit.length +
          timeGroupsLength between) = target) :
    (actualCanonicalWorkBlockGroupVisit machine input T b hb
        before (between ++ [secondVisit] ++ after) firstVisit
        (actualTwoVisits_first_split machine input T b hb before
          firstVisit between secondVisit after hsplit)).exitTime.val <
      (actualCanonicalWorkBlockGroupVisit machine input T b hb
        (actualSecondVisitPrefix before firstVisit between) after secondVisit
        (actualTwoVisits_second_split machine input T b hb before
          firstVisit between secondVisit after hsplit)).entryTime.val := by
  have hbetweenPos := timeGroupsLength_between_actualTargetVisits_pos
    machine input T b hb target before firstVisit between secondVisit after
      hsplit hfirstTarget hsecondTarget
  simp [actualSecondVisitPrefix, timeGroupsLength_append]
  omega

/-- The fixed-alpha output slab of `firstVisit` is exactly the carried actual
entry slab of `secondVisit` when these are consecutive visits to `target`.

All geometry on the two sides is advertised by the actual timed alpha; the
canonical-run geometry appears only inside the persistence proof and is
eliminated by the actual-offset bridge. -/
theorem actualTargetBlockVisit_outputSlab_eq_nextEntrySlab
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (target : Fin (T / b + 1))
    (before : List (List (Fin T)))
    (firstVisit : List (Fin T))
    (between : List (List (Fin T)))
    (secondVisit : List (Fin T))
    (after : List (List (Fin T)))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ [firstVisit] ++ between ++ [secondVisit] ++ after)
    (hfirstTarget :
      actualCanonicalWorkBlockAtTime machine input T b hb
        (timeGroupsLength before) = target)
    (hsecondTarget :
      actualCanonicalWorkBlockAtTime machine input T b hb
        (timeGroupsLength before + firstVisit.length +
          timeGroupsLength between) = target)
    (hbetween : ∀ time : Fin T, time ∈ between.flatten →
      actualCanonicalWorkBlockAtTime machine input T b hb time.val ≠ target) :
    fixedAlphaBlockVisitOutputSlab machine input
        (chronologicalTimedCanonicalAlpha machine input T b hb)
        target
        (actualCanonicalWorkBlockGroupVisit machine input T b hb
          before (between ++ [secondVisit] ++ after) firstVisit
          (actualTwoVisits_first_split machine input T b hb before
            firstVisit between secondVisit after hsplit))
        (actualFixedAlphaBlockSlabAtTime machine input T b hb target
          (timeGroupsLength before)) =
      actualFixedAlphaBlockSlabAtTime machine input T b hb target
        (timeGroupsLength before + firstVisit.length +
          timeGroupsLength between) := by
  let firstSplit := actualTwoVisits_first_split machine input T b hb before
    firstVisit between secondVisit after hsplit
  have hfirstLabel :
      actualCanonicalWorkBlockGroupLabel machine input T b hb before =
        target := by
    exact hfirstTarget
  have houtput := actualCanonicalWorkBlockGroupVisit_outputSlab_for_target
    machine input T b hb target before
      (between ++ [secondVisit] ++ after) firstVisit firstSplit hfirstLabel
  rw [houtput]
  have hpersistence := targetCanonicalSlab_eq_between_actualVisits
    machine input T b hb target before firstVisit between secondVisit after
      hsplit hfirstTarget hsecondTarget hbetween
  simpa [actualFixedAlphaBlockSlabAtTime,
    chronologicalTimedCanonicalAlpha, actualWorkBoundaryCounts] using
      hpersistence

/-- Therefore the second actual visit is accepted when its carried slab is
the validator-computed output of the first actual visit, rather than a newly
supplied or reset tape restriction. -/
theorem actualSecondTargetBlockVisit_valid_from_firstOutput
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (target : Fin (T / b + 1))
    (before : List (List (Fin T)))
    (firstVisit : List (Fin T))
    (between : List (List (Fin T)))
    (secondVisit : List (Fin T))
    (after : List (List (Fin T)))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ [firstVisit] ++ between ++ [secondVisit] ++ after)
    (hfirstTarget :
      actualCanonicalWorkBlockAtTime machine input T b hb
        (timeGroupsLength before) = target)
    (hsecondTarget :
      actualCanonicalWorkBlockAtTime machine input T b hb
        (timeGroupsLength before + firstVisit.length +
          timeGroupsLength between) = target)
    (hbetween : ∀ time : Fin T, time ∈ between.flatten →
      actualCanonicalWorkBlockAtTime machine input T b hb time.val ≠ target) :
    FixedAlphaBlockVisitValid machine input
      (chronologicalTimedCanonicalAlpha machine input T b hb)
      target
      (actualCanonicalWorkBlockGroupVisit machine input T b hb
        (actualSecondVisitPrefix before firstVisit between) after secondVisit
        (actualTwoVisits_second_split machine input T b hb before
          firstVisit between secondVisit after hsplit))
      (fixedAlphaBlockVisitOutputSlab machine input
        (chronologicalTimedCanonicalAlpha machine input T b hb)
        target
        (actualCanonicalWorkBlockGroupVisit machine input T b hb
          before (between ++ [secondVisit] ++ after) firstVisit
          (actualTwoVisits_first_split machine input T b hb before
            firstVisit between secondVisit after hsplit))
        (actualFixedAlphaBlockSlabAtTime machine input T b hb target
          (timeGroupsLength before))) := by
  let firstSplit := actualTwoVisits_first_split machine input T b hb before
    firstVisit between secondVisit after hsplit
  let secondSplit := actualTwoVisits_second_split machine input T b hb before
    firstVisit between secondVisit after hsplit
  have hcarry := actualTargetBlockVisit_outputSlab_eq_nextEntrySlab
    machine input T b hb target before firstVisit between secondVisit after
      hsplit hfirstTarget hsecondTarget hbetween
  rw [hcarry]
  have hsecondLabel :
      actualCanonicalWorkBlockGroupLabel machine input T b hb
          (actualSecondVisitPrefix before firstVisit between) = target := by
    simpa [actualCanonicalWorkBlockGroupLabel, actualSecondVisitPrefix,
      timeGroupsLength_append, Nat.add_assoc] using hsecondTarget
  simpa [actualSecondVisitPrefix, timeGroupsLength_append,
    Nat.add_assoc] using
      (actualCanonicalWorkBlockGroupVisit_valid_for_target
        machine input T b hb
        target (actualSecondVisitPrefix before firstVisit between) after
        secondVisit secondSplit hsecondLabel)

/-- The recursive validator relation accepts the two visits using one carried
target slab: actual entry restriction, first output, then second output. -/
theorem actualTwoTargetBlockVisits_replayAccepted
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (target : Fin (T / b + 1))
    (before : List (List (Fin T)))
    (firstVisit : List (Fin T))
    (between : List (List (Fin T)))
    (secondVisit : List (Fin T))
    (after : List (List (Fin T)))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ [firstVisit] ++ between ++ [secondVisit] ++ after)
    (hfirstTarget :
      actualCanonicalWorkBlockAtTime machine input T b hb
        (timeGroupsLength before) = target)
    (hsecondTarget :
      actualCanonicalWorkBlockAtTime machine input T b hb
        (timeGroupsLength before + firstVisit.length +
          timeGroupsLength between) = target)
    (hbetween : ∀ time : Fin T, time ∈ between.flatten →
      actualCanonicalWorkBlockAtTime machine input T b hb time.val ≠ target) :
    FixedAlphaBlockVisitReplayAccepted machine input
      (chronologicalTimedCanonicalAlpha machine input T b hb) target
      (actualFixedAlphaBlockSlabAtTime machine input T b hb target
        (timeGroupsLength before))
      [actualCanonicalWorkBlockGroupVisit machine input T b hb
          before (between ++ [secondVisit] ++ after) firstVisit
          (actualTwoVisits_first_split machine input T b hb before
            firstVisit between secondVisit after hsplit),
        actualCanonicalWorkBlockGroupVisit machine input T b hb
          (actualSecondVisitPrefix before firstVisit between) after secondVisit
          (actualTwoVisits_second_split machine input T b hb before
            firstVisit between secondVisit after hsplit)] := by
  have hfirstLabel :
      actualCanonicalWorkBlockGroupLabel machine input T b hb before =
        target := hfirstTarget
  have hfirstValid :=
    actualCanonicalWorkBlockGroupVisit_valid_for_target
      machine input T b hb target before
      (between ++ [secondVisit] ++ after) firstVisit
      (actualTwoVisits_first_split machine input T b hb before
        firstVisit between secondVisit after hsplit) hfirstLabel
  have hsecondValid :=
    actualSecondTargetBlockVisit_valid_from_firstOutput
      machine input T b hb target before firstVisit between secondVisit after
      hsplit hfirstTarget hsecondTarget hbetween
  exact ⟨hfirstValid, hsecondValid, True.intro⟩

/-- The same two visits satisfy the complete public fixed-list acceptance
interface: strict chronological separation and the recursive carried-slab
checks. -/
theorem actualTwoTargetBlockVisits_listAccepted
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (target : Fin (T / b + 1))
    (before : List (List (Fin T)))
    (firstVisit : List (Fin T))
    (between : List (List (Fin T)))
    (secondVisit : List (Fin T))
    (after : List (List (Fin T)))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ [firstVisit] ++ between ++ [secondVisit] ++ after)
    (hfirstTarget :
      actualCanonicalWorkBlockAtTime machine input T b hb
        (timeGroupsLength before) = target)
    (hsecondTarget :
      actualCanonicalWorkBlockAtTime machine input T b hb
        (timeGroupsLength before + firstVisit.length +
          timeGroupsLength between) = target)
    (hbetween : ∀ time : Fin T, time ∈ between.flatten →
      actualCanonicalWorkBlockAtTime machine input T b hb time.val ≠ target) :
    FixedAlphaBlockVisitListAccepted machine input
      (chronologicalTimedCanonicalAlpha machine input T b hb) target
      (actualFixedAlphaBlockSlabAtTime machine input T b hb target
        (timeGroupsLength before))
      [actualCanonicalWorkBlockGroupVisit machine input T b hb
          before (between ++ [secondVisit] ++ after) firstVisit
          (actualTwoVisits_first_split machine input T b hb before
            firstVisit between secondVisit after hsplit),
        actualCanonicalWorkBlockGroupVisit machine input T b hb
          (actualSecondVisitPrefix before firstVisit between) after secondVisit
          (actualTwoVisits_second_split machine input T b hb before
            firstVisit between secondVisit after hsplit)] := by
  constructor
  · have hseparated := actualTwoTargetBlockVisits_strictlySeparated
      machine input T b hb target before firstVisit between secondVisit after
        hsplit hfirstTarget hsecondTarget
    simpa [FixedAlphaBlockVisitsChronological] using hseparated
  · exact actualTwoTargetBlockVisits_replayAccepted
      machine input T b hb target before firstVisit between secondVisit after
        hsplit hfirstTarget hsecondTarget hbetween

/-- The deterministic two-visit fold ends at the exact actual slab
restriction at the second visit's exit. -/
theorem replayActualTwoTargetBlockVisits_eq_secondExitSlab
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (target : Fin (T / b + 1))
    (before : List (List (Fin T)))
    (firstVisit : List (Fin T))
    (between : List (List (Fin T)))
    (secondVisit : List (Fin T))
    (after : List (List (Fin T)))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ [firstVisit] ++ between ++ [secondVisit] ++ after)
    (hfirstTarget :
      actualCanonicalWorkBlockAtTime machine input T b hb
        (timeGroupsLength before) = target)
    (hsecondTarget :
      actualCanonicalWorkBlockAtTime machine input T b hb
        (timeGroupsLength before + firstVisit.length +
          timeGroupsLength between) = target)
    (hbetween : ∀ time : Fin T, time ∈ between.flatten →
      actualCanonicalWorkBlockAtTime machine input T b hb time.val ≠ target) :
    replayFixedAlphaBlockVisits machine input
        (chronologicalTimedCanonicalAlpha machine input T b hb) target
        (actualFixedAlphaBlockSlabAtTime machine input T b hb target
          (timeGroupsLength before))
        [actualCanonicalWorkBlockGroupVisit machine input T b hb
            before (between ++ [secondVisit] ++ after) firstVisit
            (actualTwoVisits_first_split machine input T b hb before
              firstVisit between secondVisit after hsplit),
          actualCanonicalWorkBlockGroupVisit machine input T b hb
            (actualSecondVisitPrefix before firstVisit between) after
            secondVisit
            (actualTwoVisits_second_split machine input T b hb before
              firstVisit between secondVisit after hsplit)] =
      actualFixedAlphaBlockSlabAtTime machine input T b hb target
        (timeGroupsLength before + firstVisit.length +
          timeGroupsLength between + secondVisit.length) := by
  have hcarry := actualTargetBlockVisit_outputSlab_eq_nextEntrySlab
    machine input T b hb target before firstVisit between secondVisit after
      hsplit hfirstTarget hsecondTarget hbetween
  have hsecondLabel :
      actualCanonicalWorkBlockGroupLabel machine input T b hb
          (actualSecondVisitPrefix before firstVisit between) = target := by
    simpa [actualCanonicalWorkBlockGroupLabel, actualSecondVisitPrefix,
      timeGroupsLength_append, Nat.add_assoc] using hsecondTarget
  have hsecondOutput :=
    actualCanonicalWorkBlockGroupVisit_outputSlab_for_target
      machine input T b hb target
      (actualSecondVisitPrefix before firstVisit between) after secondVisit
      (actualTwoVisits_second_split machine input T b hb before
        firstVisit between secondVisit after hsplit) hsecondLabel
  simp only [replayFixedAlphaBlockVisits]
  rw [hcarry]
  simpa [actualSecondVisitPrefix, timeGroupsLength_append,
    Nat.add_assoc] using hsecondOutput

end OneTapeMagnification
end Frontier
end Pnp4
