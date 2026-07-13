import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.CanonicalSlabPersistence

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Persistence between two actual visits to one canonical block

The maximal-group decomposition is written

`before ++ [firstVisit] ++ between ++ [secondVisit] ++ after`.

The target slab snapshot after `firstVisit` is taken at

`timeGroupsLength before + firstVisit.length`.

The entry time of `secondVisit` is that exit time plus
`timeGroupsLength between`.  Thus every protected pre-transition time belongs
to `between`.  The final intervening transition may enter the target slab: its
old head still has a non-target block label, and the machine writes before
moving its head.

An empty `between` gives a zero-length persistence interval and hence a
reflexive equality.  For genuine maximal groups, two adjacent visits carrying
the same target label are excluded by maximality, but no artificial
nonemptiness premise is needed here.  At `T = 0` the displayed two-visit list
decomposition is impossible.  Likewise, a crossing on transition `T - 1`
which enters the target at post-time `T` creates no `secondVisit`, because
there is no further pre-transition time.

Everything below concerns one actual, input-dependent run.  No fixed-alpha
validator, cross-input invariant, branching program, or width bound is
asserted.
-/

/-- A consecutive slice of an ordered partition of `Fin T` contains exactly
the corresponding half-open interval of natural-number times. -/
theorem groupsSlice_map_val_eq_range'_of_flatten_eq_finRange
    {T : Nat} {groups before middle after : List (List (Fin T))}
    (hflatten : groups.flatten = List.finRange T)
    (hsplit : groups = before ++ middle ++ after) :
    middle.flatten.map Fin.val =
      List.range' (timeGroupsLength before) (timeGroupsLength middle) := by
  let beforeLength := timeGroupsLength before
  let middleLength := timeGroupsLength middle
  let afterLength := timeGroupsLength after
  have hlength : beforeLength + (middleLength + afterLength) = T := by
    have h := congrArg List.length hflatten
    rw [hsplit] at h
    simp only [List.flatten_append, List.length_append,
      List.length_flatten, List.length_finRange] at h
    simpa [beforeLength, middleLength, afterLength, timeGroupsLength,
      Nat.add_assoc] using h
  have hvalues := congrArg (List.map Fin.val) hflatten
  rw [hsplit] at hvalues
  simp only [List.flatten_append, List.map_append,
    List.map_coe_finRange] at hvalues
  have hrange :
      List.range T =
        List.range' 0 beforeLength ++
          (List.range' beforeLength middleLength ++
            List.range' (beforeLength + middleLength) afterLength) := by
    calc
      List.range T = List.range' 0 T := List.range_eq_range'
      _ = List.range' 0 (beforeLength + (middleLength + afterLength)) := by
        rw [hlength]
      _ = List.range' 0 beforeLength ++
          List.range' beforeLength (middleLength + afterLength) := by
        symm
        simpa using
          (List.range'_append (s := 0) (m := beforeLength)
            (n := middleLength + afterLength) (step := 1))
      _ = List.range' 0 beforeLength ++
          (List.range' beforeLength middleLength ++
            List.range' (beforeLength + middleLength) afterLength) := by
        congr 1
        symm
        simpa only [Nat.one_mul] using
          (List.range'_append (s := beforeLength) (m := middleLength)
            (n := afterLength) (step := 1))
  have happend :
      before.flatten.map Fin.val ++
          (middle.flatten.map Fin.val ++ after.flatten.map Fin.val) =
        List.range' 0 beforeLength ++
          (List.range' beforeLength middleLength ++
            List.range' (beforeLength + middleLength) afterLength) := by
    calc
      before.flatten.map Fin.val ++
          (middle.flatten.map Fin.val ++ after.flatten.map Fin.val) =
          List.range T := by
        simpa [List.map_append, List.append_assoc] using hvalues
      _ = _ := hrange
  have hbeforeLength :
      (before.flatten.map Fin.val).length =
        (List.range' 0 beforeLength).length := by
    simp [beforeLength, timeGroupsLength, List.length_flatten,
      Function.comp_def]
  have hremainders := (List.append_inj happend hbeforeLength).2
  have hmiddleLength :
      (middle.flatten.map Fin.val).length =
        (List.range' beforeLength middleLength).length := by
    simp [middleLength, timeGroupsLength, List.length_flatten,
      Function.comp_def]
  exact (List.append_inj hremainders hmiddleLength).1

/-- Actual maximal groups specialize the generic consecutive-slice theorem. -/
theorem actualCanonicalWorkBlockGroupsSlice_map_val_eq_range'
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (before middle after : List (List (Fin T)))
    (hsplit : actualCanonicalWorkBlockRuns machine input T b hb =
      before ++ middle ++ after) :
    middle.flatten.map Fin.val =
      List.range' (timeGroupsLength before) (timeGroupsLength middle) := by
  exact groupsSlice_map_val_eq_range'_of_flatten_eq_finRange
    (flatten_actualCanonicalWorkBlockRuns machine input T b hb) hsplit

/-- Exact slab persistence from the exit of `firstVisit` to the entry of
`secondVisit`, provided every intervening transition time has a non-target
canonical block label. -/
theorem targetCanonicalSlab_eq_between_actualVisits
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
    restrictWorkSlab
        (canonicalBlockLower hb
          (actualWorkBoundaryCounts machine input T) target)
        (canonicalBlockWidth hb
          (actualWorkBoundaryCounts machine input T) target)
        (run machine input
          (timeGroupsLength before + firstVisit.length)).workTape =
      restrictWorkSlab
        (canonicalBlockLower hb
          (actualWorkBoundaryCounts machine input T) target)
        (canonicalBlockWidth hb
          (actualWorkBoundaryCounts machine input T) target)
        (run machine input
          (timeGroupsLength before + firstVisit.length +
            timeGroupsLength between)).workTape := by
  -- The endpoint labels identify the flanking groups as visits to `target`.
  -- Persistence across the open interval itself uses only `hbetween`.
  have hflankingVisitsIdentified :
      actualCanonicalWorkBlockAtTime machine input T b hb
          (timeGroupsLength before) = target ∧
        actualCanonicalWorkBlockAtTime machine input T b hb
          (timeGroupsLength before + firstVisit.length +
            timeGroupsLength between) = target :=
    ⟨hfirstTarget, hsecondTarget⟩
  clear hflankingVisitsIdentified hfirstTarget hsecondTarget
  let crossings := actualWorkBoundaryCounts machine input T
  let base := canonicalBlockLower hb crossings target
  let width := canonicalBlockWidth hb crossings target
  let firstExit := timeGroupsLength before + firstVisit.length
  let awaySteps := timeGroupsLength between
  have hsplitSlice : actualCanonicalWorkBlockRuns machine input T b hb =
      (before ++ [firstVisit]) ++ between ++ ([secondVisit] ++ after) := by
    simpa [List.append_assoc] using hsplit
  have hsliceRaw := actualCanonicalWorkBlockGroupsSlice_map_val_eq_range'
    machine input T b hb (before ++ [firstVisit]) between
      ([secondVisit] ++ after) hsplitSlice
  have hslice : between.flatten.map Fin.val =
      List.range' firstExit awaySteps := by
    simpa [firstExit, awaySteps, timeGroupsLength_append] using hsliceRaw
  have havoids : ∀ offset, offset < awaySteps →
      ¬ WorkCellInSlab base width
        (runFrom machine input
          (run machine input firstExit) offset).workHead := by
    intro offset hoffset hslab
    have hposition : firstExit + offset ∈
        List.range' firstExit awaySteps := by
      simp
      omega
    rw [← hslice] at hposition
    obtain ⟨time, htimeBetween, htimeValue⟩ :=
      List.mem_map.mp hposition
    have hrun : run machine input (firstExit + offset) =
        runFrom machine input (run machine input firstExit) offset := by
      simpa [run] using
        (runFrom_add_eq_runFrom_runFrom machine input
          (initialConfiguration machine) firstExit offset)
    have hglobalSlab : WorkCellInSlab base width
        (run machine input time.val).workHead := by
      have hglobalAtOffset : WorkCellInSlab base width
          (run machine input (firstExit + offset)).workHead := by
        rw [congrArg Configuration.workHead hrun]
        exact hslab
      simpa [htimeValue] using hglobalAtOffset
    have hheadLe : (run machine input time.val).workHead ≤ time.val := by
      simpa [workHeadTrajectory, workHeadTrajectoryFrom, run] using
        (workHeadTrajectory_le_time machine input time.val)
    let cell : Fin (T + 1) :=
      ⟨(run machine input time.val).workHead, by omega⟩
    have hlabel : workBlockAt hb crossings cell.val = target :=
      (workBlockAt_eq_iff_workCellInCanonicalSlab
        hb crossings cell target).mpr (by
          simpa [cell, base, width] using hglobalSlab)
    apply hbetween time htimeBetween
    simpa [actualCanonicalWorkBlockAtTime, crossings, cell,
      workHeadTrajectory, workHeadTrajectoryFrom, run] using hlabel
  have hpersistence := restrictWorkSlab_runFrom_eq_of_avoids
    machine input (run machine input firstExit) base width awaySteps havoids
  have hrunEnd : run machine input (firstExit + awaySteps) =
      runFrom machine input (run machine input firstExit) awaySteps := by
    simpa [run] using
      (runFrom_add_eq_runFrom_runFrom machine input
        (initialConfiguration machine) firstExit awaySteps)
  change restrictWorkSlab base width
      (run machine input firstExit).workTape =
    restrictWorkSlab base width
      (run machine input (firstExit + awaySteps)).workTape
  rw [hrunEnd]
  exact hpersistence.symm

end OneTapeMagnification
end Frontier
end Pnp4
