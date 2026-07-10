import Mathlib.Data.List.SplitBy
import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.ActualCrossingSchedule
import Pnp4.Frontier.OneTapeMagnification.CanonicalBlockSlabs
import Pnp4.Frontier.OneTapeMagnification.LocalBlockReplay

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Actual maximal segments stay inside one canonical slab

`ActualCrossingSchedule` partitions the chronological transition times into
maximal groups with one pre-transition canonical work-block label.  This file
first closes the indexing detail: a group after a prefix of total length `s`
is exactly the consecutive interval `s, ..., s + group.length - 1`.

Consequently every pre-transition work head of that group lies in the slab of
its initial canonical block.  The final theorem feeds precisely this fact to
`runFrom_sameOnWorkSlab_same_input`: any alternative entry configuration that
agrees with the actual entry on this slab reproduces state, both heads, and
the slab contents for the length of the segment, on the same immutable input.
The final transition may leave the slab, as required by `LocalBlockReplay`.

All statements remain input-dependent.  No local branching program, width
bound, input-independent schedule, or transcript-count bound is asserted.
-/

/-- Total number of time indices contained in a prefix of groups. -/
def timeGroupsLength {steps : Nat} (groups : List (List (Fin steps))) : Nat :=
  (groups.map List.length).sum

@[simp]
theorem timeGroupsLength_nil {steps : Nat} :
    timeGroupsLength ([] : List (List (Fin steps))) = 0 := by
  rfl

@[simp]
theorem timeGroupsLength_cons {steps : Nat} (group : List (Fin steps))
    (groups : List (List (Fin steps))) :
    timeGroupsLength (group :: groups) =
      group.length + timeGroupsLength groups := by
  simp [timeGroupsLength]

@[simp]
theorem timeGroupsLength_append {steps : Nat}
    (left right : List (List (Fin steps))) :
    timeGroupsLength (left ++ right) =
      timeGroupsLength left + timeGroupsLength right := by
  simp [timeGroupsLength, List.sum_append]

/-- Any ordered partition of `Fin steps` has the expected consecutive values
in each group.  The prefix decomposition identifies the group's cumulative
start time. -/
theorem group_map_val_eq_range'_of_flatten_eq_finRange
    {steps : Nat} {groups before after : List (List (Fin steps))}
    {group : List (Fin steps)}
    (hflatten : groups.flatten = List.finRange steps)
    (hsplit : groups = before ++ group :: after) :
    group.map Fin.val =
      List.range' (timeGroupsLength before) group.length := by
  let prefixLength := timeGroupsLength before
  let suffixLength := timeGroupsLength after
  have hlength : prefixLength + (group.length + suffixLength) = steps := by
    have h := congrArg List.length hflatten
    rw [hsplit] at h
    simp only [List.flatten_append, List.flatten_cons, List.length_append,
      List.length_flatten, List.length_finRange] at h
    simpa [prefixLength, suffixLength, timeGroupsLength,
      Nat.add_assoc] using h
  have hvalues := congrArg (List.map Fin.val) hflatten
  rw [hsplit] at hvalues
  simp only [List.flatten_append, List.flatten_cons, List.map_append,
    List.map_coe_finRange] at hvalues
  have hrange :
      List.range steps =
        List.range' 0 prefixLength ++
          (List.range' prefixLength group.length ++
            List.range' (prefixLength + group.length) suffixLength) := by
    calc
      List.range steps = List.range' 0 steps := List.range_eq_range'
      _ = List.range' 0 (prefixLength + (group.length + suffixLength)) := by
        rw [hlength]
      _ = List.range' 0 prefixLength ++
          List.range' prefixLength (group.length + suffixLength) := by
        symm
        simpa using
          (List.range'_append (s := 0) (m := prefixLength)
            (n := group.length + suffixLength) (step := 1))
      _ = List.range' 0 prefixLength ++
          (List.range' prefixLength group.length ++
            List.range' (prefixLength + group.length) suffixLength) := by
        congr 1
        symm
        simpa only [Nat.one_mul] using
          (List.range'_append (s := prefixLength) (m := group.length)
            (n := suffixLength) (step := 1))
  have happend :
      before.flatten.map Fin.val ++
          (group.map Fin.val ++ after.flatten.map Fin.val) =
        List.range' 0 prefixLength ++
          (List.range' prefixLength group.length ++
            List.range' (prefixLength + group.length) suffixLength) := by
    calc
      before.flatten.map Fin.val ++
          (group.map Fin.val ++ after.flatten.map Fin.val) =
          List.range steps := by
        simpa [List.map_append, List.append_assoc] using hvalues
      _ = _ := hrange
  have hprefixLength :
      (before.flatten.map Fin.val).length =
        (List.range' 0 prefixLength).length := by
    simp [prefixLength, timeGroupsLength, List.length_flatten,
      Function.comp_def]
  have hremainders := (List.append_inj happend hprefixLength).2
  exact (List.append_inj hremainders (by simp)).1

/-- Specialization to the maximal actual canonical work-block groups. -/
theorem actualCanonicalWorkBlockGroup_map_val_eq_range'
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b)
    (before after : List (List (Fin steps))) (group : List (Fin steps))
    (hsplit : actualCanonicalWorkBlockRuns machine input steps b hb =
      before ++ group :: after) :
    group.map Fin.val =
      List.range' (timeGroupsLength before) group.length := by
  exact group_map_val_eq_range'_of_flatten_eq_finRange
    (flatten_actualCanonicalWorkBlockRuns machine input steps b hb) hsplit

/-- A group named by a prefix/suffix decomposition is genuinely one of the
maximal groups and therefore is nonempty. -/
theorem actualCanonicalWorkBlockGroup_nonempty
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b)
    (before after : List (List (Fin steps))) (group : List (Fin steps))
    (hsplit : actualCanonicalWorkBlockRuns machine input steps b hb =
      before ++ group :: after) :
    group ≠ [] := by
  apply actualCanonicalWorkBlockRuns_nonempty machine input steps b hb
  rw [hsplit]
  simp

/-- Every time in a maximal group has the label at the group's cumulative
start time. -/
theorem actualCanonicalWorkBlockGroup_label_eq_initial
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b)
    (before after : List (List (Fin steps))) (group : List (Fin steps))
    (hsplit : actualCanonicalWorkBlockRuns machine input steps b hb =
      before ++ group :: after)
    (time : Fin steps) (htime : time ∈ group) :
    actualCanonicalWorkBlockAtTime machine input steps b hb time.val =
      actualCanonicalWorkBlockAtTime machine input steps b hb
        (timeGroupsLength before) := by
  have hgroup :
      group ∈ actualCanonicalWorkBlockRuns machine input steps b hb := by
    rw [hsplit]
    simp
  have hmap := actualCanonicalWorkBlockGroup_map_val_eq_range'
    machine input steps b hb before after group hsplit
  have hpairwise := actualCanonicalWorkBlockRuns_pairwise_same
    machine input steps b hb hgroup
  have hnonempty := actualCanonicalWorkBlockGroup_nonempty
    machine input steps b hb before after group hsplit
  cases group with
  | nil => exact False.elim (hnonempty rfl)
  | cons first rest =>
      have hfirst : first.val = timeGroupsLength before := by
        have hhead := congrArg List.head? hmap
        simpa [List.head?_range'] using hhead
      simp only [List.pairwise_cons] at hpairwise
      rw [List.mem_cons] at htime
      rcases htime with rfl | htime
      · simp [hfirst]
      · have hsame := hpairwise.1 time htime
        rw [hfirst] at hsame
        exact hsame.symm

/-- Offset form of within-group label constancy. -/
theorem actualCanonicalWorkBlockGroup_label_constant
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b)
    (before after : List (List (Fin steps))) (group : List (Fin steps))
    (hsplit : actualCanonicalWorkBlockRuns machine input steps b hb =
      before ++ group :: after)
    (offset : Nat) (hoffset : offset < group.length) :
    actualCanonicalWorkBlockAtTime machine input steps b hb
        (timeGroupsLength before + offset) =
      actualCanonicalWorkBlockAtTime machine input steps b hb
        (timeGroupsLength before) := by
  have hmap := actualCanonicalWorkBlockGroup_map_val_eq_range'
    machine input steps b hb before after group hsplit
  have hposition : timeGroupsLength before + offset ∈
      List.range' (timeGroupsLength before) group.length := by
    simp
    omega
  rw [← hmap] at hposition
  obtain ⟨time, htime, hval⟩ := List.mem_map.mp hposition
  have hlabel := actualCanonicalWorkBlockGroup_label_eq_initial
    machine input steps b hb before after group hsplit time htime
  simpa [hval] using hlabel

/-- Cumulative time at the end of a group never exceeds the represented run
length `steps`. -/
theorem actualCanonicalWorkBlockGroup_end_le_steps
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b)
    (before after : List (List (Fin steps))) (group : List (Fin steps))
    (hsplit : actualCanonicalWorkBlockRuns machine input steps b hb =
      before ++ group :: after) :
    timeGroupsLength before + group.length ≤ steps := by
  have htotal :
      timeGroupsLength
        (actualCanonicalWorkBlockRuns machine input steps b hb) = steps := by
    unfold timeGroupsLength
    rw [← List.length_flatten,
      flatten_actualCanonicalWorkBlockRuns machine input steps b hb]
    simp
  rw [hsplit, timeGroupsLength_append, timeGroupsLength_cons] at htotal
  omega

/-- Every pre-transition work head of a maximal group lies in the canonical
slab of the group's initial block.  In particular, the crossing transition
at the end of a group is assigned to the block it exits. -/
theorem actualCanonicalWorkBlockGroup_workHead_in_slab
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b)
    (before after : List (List (Fin steps))) (group : List (Fin steps))
    (hsplit : actualCanonicalWorkBlockRuns machine input steps b hb =
      before ++ group :: after)
    (offset : Nat) (hoffset : offset < group.length) :
    WorkCellInSlab
      (canonicalBlockLower hb
        (actualWorkBoundaryCounts machine input steps)
        (actualCanonicalWorkBlockAtTime machine input steps b hb
          (timeGroupsLength before)))
      (canonicalBlockWidth hb
        (actualWorkBoundaryCounts machine input steps)
        (actualCanonicalWorkBlockAtTime machine input steps b hb
          (timeGroupsLength before)))
      (run machine input (timeGroupsLength before + offset)).workHead := by
  have hend := actualCanonicalWorkBlockGroup_end_le_steps
    machine input steps b hb before after group hsplit
  have htime : timeGroupsLength before + offset ≤ steps := by
    omega
  have hlabel := actualCanonicalWorkBlockGroup_label_constant
    machine input steps b hb before after group hsplit offset hoffset
  have hslab := workHeadTrajectory_in_canonicalBlockSlab
    (T := steps) (b := b) hb
    (actualWorkBoundaryCounts machine input steps)
    machine input (timeGroupsLength before + offset) htime
    (actualCanonicalWorkBlockAtTime machine input steps b hb
      (timeGroupsLength before)) (by
        simpa [actualCanonicalWorkBlockAtTime,
          actualWorkBoundaryCounts] using hlabel)
  simpa [workHeadTrajectory] using hslab

/-- Exact local replay of one actual maximal group on the same immutable
input.  Agreement is required only at the entry configuration, on the
canonical slab named by the group's initial label.  The result includes the
control state, both heads, and the entire slab restriction at segment exit.
The alternative work tape may be arbitrary outside the slab. -/
theorem runFrom_sameOn_actualCanonicalWorkBlockGroup
    (machine : DeterministicMachine) (input : List Bool)
    (steps b : Nat) (hb : 0 < b)
    (before after : List (List (Fin steps))) (group : List (Fin steps))
    (hsplit : actualCanonicalWorkBlockRuns machine input steps b hb =
      before ++ group :: after)
    (alternativeEntry : Configuration machine.State)
    (hsame : SameOnWorkSlab
      (canonicalBlockLower hb
        (actualWorkBoundaryCounts machine input steps)
        (actualCanonicalWorkBlockAtTime machine input steps b hb
          (timeGroupsLength before)))
      (canonicalBlockWidth hb
        (actualWorkBoundaryCounts machine input steps)
        (actualCanonicalWorkBlockAtTime machine input steps b hb
          (timeGroupsLength before)))
      (run machine input (timeGroupsLength before)) alternativeEntry) :
    SameOnWorkSlab
      (canonicalBlockLower hb
        (actualWorkBoundaryCounts machine input steps)
        (actualCanonicalWorkBlockAtTime machine input steps b hb
          (timeGroupsLength before)))
      (canonicalBlockWidth hb
        (actualWorkBoundaryCounts machine input steps)
        (actualCanonicalWorkBlockAtTime machine input steps b hb
          (timeGroupsLength before)))
      (run machine input (timeGroupsLength before + group.length))
      (runFrom machine input alternativeEntry group.length) := by
  let base := canonicalBlockLower hb
    (actualWorkBoundaryCounts machine input steps)
    (actualCanonicalWorkBlockAtTime machine input steps b hb
      (timeGroupsLength before))
  let width := canonicalBlockWidth hb
    (actualWorkBoundaryCounts machine input steps)
    (actualCanonicalWorkBlockAtTime machine input steps b hb
      (timeGroupsLength before))
  have hinside : ∀ time, time < group.length →
      WorkCellInSlab base width
        (runFrom machine input
          (run machine input (timeGroupsLength before)) time).workHead := by
    intro time htime
    have hglobal := actualCanonicalWorkBlockGroup_workHead_in_slab
      machine input steps b hb before after group hsplit time htime
    have hrun := runFrom_add_eq_runFrom_runFrom machine input
      (initialConfiguration machine) (timeGroupsLength before) time
    change WorkCellInSlab base width
      (runFrom machine input
        (run machine input (timeGroupsLength before)) time).workHead
    simpa [base, width, run] using congrArg Configuration.workHead hrun
      ▸ hglobal
  have hreplay := runFrom_sameOnWorkSlab_same_input machine input
    (base := base) (width := width) hsame hinside
  change SameOnWorkSlab base width
    (run machine input (timeGroupsLength before + group.length))
    (runFrom machine input alternativeEntry group.length)
  rw [run, runFrom_add_eq_runFrom_runFrom]
  exact hreplay

end OneTapeMagnification
end Frontier
end Pnp4
