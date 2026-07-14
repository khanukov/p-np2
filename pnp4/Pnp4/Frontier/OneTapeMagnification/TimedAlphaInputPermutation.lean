import Pnp4.Frontier.OneTapeMagnification.TimedAlphaFixedQueryOrder

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Completing a fixed timed-alpha query order on a finite input

A timed-alpha schedule orders the fresh input coordinates below its advertised
terminal input head.  A branching program for inputs of a fixed length `n`
must instead have a query order over `Fin n`.  This file performs the purely
finite conversion:

* positions at least `n` are discarded and the remaining positions are cast
  to `Fin n`;
* the still-unread coordinates are appended in their canonical `finRange`
  order as dummy queries.

The construction is total when the advertised terminal head lies below or
above `n`, and also when `n = 0` or the timed-alpha schedule is empty.  Its
computational data is determined by the advertised query order and `n`; all
schedule-validity and replay-acceptance arguments occur only in proofs.
-/

/-- Cast a natural-number input position to `Fin n` exactly when it is a
genuine coordinate of an input of length `n`. -/
def finiteInputPosition? (n position : Nat) : Option (Fin n) :=
  if h : position < n then some (Fin.mk position h) else none

@[simp]
theorem finiteInputPosition?_eq_some_iff
    {n position : Nat} {coordinate : Fin n} :
    finiteInputPosition? n position = some coordinate ↔
      position = coordinate.val := by
  unfold finiteInputPosition?
  by_cases hposition : position < n
  · rw [dif_pos hposition]
    constructor
    · intro heq
      exact congrArg Fin.val (Option.some.inj heq)
    · intro hval
      exact congrArg some (Fin.ext hval)
  · rw [dif_neg hposition]
    constructor
    · intro heq
      cases heq
    · intro hval
      subst position
      exact (hposition coordinate.isLt).elim

/-- Keep precisely the genuine length-`n` coordinates from a natural-number
query order. -/
def finiteInputVariableQueryOrder
    (n : Nat) (queryOrder : List Nat) : List (Fin n) :=
  queryOrder.filterMap (finiteInputPosition? n)

/-- Canonical ascending suffix of coordinates not already queried by the
variable part. -/
def finiteInputUnreadSuffix
    (n : Nat) (queryOrder : List Nat) : List (Fin n) :=
  (List.finRange n).filter fun coordinate =>
    decide (coordinate ∉ finiteInputVariableQueryOrder n queryOrder)

/-- The complete finite query order: the schedule-fixed variable part followed
by deterministic dummy queries to every unread coordinate. -/
def finiteInputQueryOrderWithDummySuffix
    (n : Nat) (queryOrder : List Nat) : List (Fin n) :=
  finiteInputVariableQueryOrder n queryOrder ++
    finiteInputUnreadSuffix n queryOrder

/-- Partial casting preserves duplicate-freedom. -/
theorem finiteInputVariableQueryOrder_nodup
    {n : Nat} {queryOrder : List Nat}
    (hqueryOrder : queryOrder.Nodup) :
    (finiteInputVariableQueryOrder n queryOrder).Nodup := by
  unfold finiteInputVariableQueryOrder
  apply hqueryOrder.filterMap
  intro earlier later coordinate hearlier hlater
  have hearlier' :
      finiteInputPosition? n earlier = some coordinate := by
    simpa only [Option.mem_def] using hearlier
  have hlater' :
      finiteInputPosition? n later = some coordinate := by
    simpa only [Option.mem_def] using hlater
  exact (finiteInputPosition?_eq_some_iff.mp hearlier').trans
    (finiteInputPosition?_eq_some_iff.mp hlater').symm

/-- The dummy suffix is duplicate-free. -/
theorem finiteInputUnreadSuffix_nodup
    (n : Nat) (queryOrder : List Nat) :
    (finiteInputUnreadSuffix n queryOrder).Nodup := by
  exact (List.nodup_finRange n).filter _

/-- The variable prefix and unread suffix are disjoint. -/
theorem finiteInputVariableQueryOrder_disjoint_unreadSuffix
    (n : Nat) (queryOrder : List Nat) :
    (finiteInputVariableQueryOrder n queryOrder).Disjoint
      (finiteInputUnreadSuffix n queryOrder) := by
  rw [List.disjoint_left]
  intro coordinate hvariable hunread
  have hnotVariable :
      coordinate ∉ finiteInputVariableQueryOrder n queryOrder :=
    of_decide_eq_true (List.mem_filter.mp hunread).2
  exact hnotVariable hvariable

/-- A duplicate-free natural-number prefix, completed by the deterministic
unread suffix, is a permutation of all length-`n` input coordinates. -/
theorem finiteInputQueryOrderWithDummySuffix_perm_finRange_of_nodup
    (n : Nat) (queryOrder : List Nat)
    (hqueryOrder : queryOrder.Nodup) :
    List.Perm (finiteInputQueryOrderWithDummySuffix n queryOrder)
      (List.finRange n) := by
  have hvariable := finiteInputVariableQueryOrder_nodup
    (n := n) hqueryOrder
  have hunread := finiteInputUnreadSuffix_nodup n queryOrder
  have hdisjoint :=
    finiteInputVariableQueryOrder_disjoint_unreadSuffix n queryOrder
  have hcomplete :
      (finiteInputQueryOrderWithDummySuffix n queryOrder).Nodup := by
    exact hvariable.append hunread hdisjoint
  apply (List.perm_ext_iff_of_nodup hcomplete
    (List.nodup_finRange n)).2
  intro coordinate
  constructor
  · intro _
    exact List.mem_finRange coordinate
  · intro _
    by_cases hvariableMem :
        coordinate ∈ finiteInputVariableQueryOrder n queryOrder
    · exact List.mem_append_left _ hvariableMem
    · apply List.mem_append_right
      exact List.mem_filter.mpr ⟨List.mem_finRange coordinate, by
        exact decide_eq_true hvariableMem⟩

/-- The hypothesis naturally supplied by an accepted timed-alpha schedule is
that its natural-number query order permutes the initial range ending at the
advertised terminal input head. -/
theorem finiteInputQueryOrderWithDummySuffix_perm_finRange
    (n terminalHead : Nat) (queryOrder : List Nat)
    (hperm : List.Perm queryOrder (List.range terminalHead)) :
    List.Perm (finiteInputQueryOrderWithDummySuffix n queryOrder)
      (List.finRange n) := by
  exact finiteInputQueryOrderWithDummySuffix_perm_finRange_of_nodup
    n queryOrder (hperm.symm.nodup List.nodup_range)

/-- Exact membership in the variable prefix for a query order covering
`range terminalHead`. -/
theorem mem_finiteInputVariableQueryOrder_iff
    {n terminalHead : Nat} {queryOrder : List Nat}
    (hperm : List.Perm queryOrder (List.range terminalHead))
    (coordinate : Fin n) :
    coordinate ∈ finiteInputVariableQueryOrder n queryOrder ↔
      coordinate.val < terminalHead := by
  rw [finiteInputVariableQueryOrder, List.mem_filterMap]
  constructor
  · rintro ⟨position, hposition, hcast⟩
    have hval := finiteInputPosition?_eq_some_iff.mp hcast
    rw [← hval]
    exact List.mem_range.mp (hperm.mem_iff.mp hposition)
  · intro hcoordinate
    refine ⟨coordinate.val, ?_, ?_⟩
    · exact hperm.mem_iff.mpr (List.mem_range.mpr hcoordinate)
    · exact finiteInputPosition?_eq_some_iff.mpr rfl

/-- Under the accepted-range hypothesis, the deterministic suffix consists
exactly of coordinates at or beyond the advertised terminal head. -/
theorem mem_finiteInputUnreadSuffix_iff
    {n terminalHead : Nat} {queryOrder : List Nat}
    (hperm : List.Perm queryOrder (List.range terminalHead))
    (coordinate : Fin n) :
    coordinate ∈ finiteInputUnreadSuffix n queryOrder ↔
      terminalHead ≤ coordinate.val := by
  rw [finiteInputUnreadSuffix, List.mem_filter]
  simp only [List.mem_finRange, true_and, decide_eq_true_eq]
  rw [mem_finiteInputVariableQueryOrder_iff hperm]
  exact Nat.not_lt

/-- The completed finite query order is duplicate-free. -/
theorem finiteInputQueryOrderWithDummySuffix_nodup
    (n terminalHead : Nat) (queryOrder : List Nat)
    (hperm : List.Perm queryOrder (List.range terminalHead)) :
    (finiteInputQueryOrderWithDummySuffix n queryOrder).Nodup := by
  exact (finiteInputQueryOrderWithDummySuffix_perm_finRange
    n terminalHead queryOrder hperm).symm.nodup (List.nodup_finRange n)

/-- Finite variable query order extracted directly from advertised timed-alpha
visits.  The monotonicity proof is erased; no input word occurs in the data. -/
def timedAlphaFiniteInputVariableQueryOrder
    {State : Type} {T b : Nat} (n : Nat)
    (visits : List (TimedAlphaScheduledVisit State T b))
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone visits) :
    List (Fin n) :=
  finiteInputVariableQueryOrder n
    (timedAlphaStableGroupedQueryOrder visits hmonotone)

/-- Deterministic unread-coordinate suffix for advertised timed-alpha visits. -/
def timedAlphaFiniteInputUnreadSuffix
    {State : Type} {T b : Nat} (n : Nat)
    (visits : List (TimedAlphaScheduledVisit State T b))
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone visits) :
    List (Fin n) :=
  finiteInputUnreadSuffix n
    (timedAlphaStableGroupedQueryOrder visits hmonotone)

/-- Complete length-`n` query permutation determined by the advertised
timed-alpha visits. -/
def timedAlphaFiniteInputQueryOrder
    {State : Type} {T b : Nat} (n : Nat)
    (visits : List (TimedAlphaScheduledVisit State T b))
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone visits) :
    List (Fin n) :=
  finiteInputQueryOrderWithDummySuffix n
    (timedAlphaStableGroupedQueryOrder visits hmonotone)

/-- Successful global replay supplies a complete finite permutation for every
input length.  In particular, this includes `n = 0`, `T = 0`, and both sides
of the comparison between the terminal input head and `n`. -/
theorem acceptedTimedAlphaFiniteInputQueryOrder_perm_finRange
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (n : Nat)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha visits)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha visits) :
    List.Perm
      (timedAlphaFiniteInputQueryOrder n visits
        (allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
          machine input alpha visits haccepted))
      (List.finRange n) := by
  let hmonotone : TimedAlphaScheduledVisitsInputMonotone visits :=
    allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
      machine input alpha visits haccepted
  have hperm : List.Perm
      (timedAlphaStableGroupedQueryOrder visits hmonotone)
      (List.range alpha.terminal.inputHead.val) := by
    simpa [acceptedTimedAlphaStableGroupedQueryOrder, hmonotone] using
      (acceptedTimedAlphaStableGroupedQueryOrder_perm_range
        machine input alpha visits hschedule haccepted)
  simpa [timedAlphaFiniteInputQueryOrder, hmonotone] using
    (finiteInputQueryOrderWithDummySuffix_perm_finRange
      n alpha.terminal.inputHead.val
        (timedAlphaStableGroupedQueryOrder visits hmonotone) hperm)

/-- Accepted timed-alpha finite query orders are duplicate-free. -/
theorem acceptedTimedAlphaFiniteInputQueryOrder_nodup
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (n : Nat)
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha visits)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha visits) :
    (timedAlphaFiniteInputQueryOrder n visits
      (allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
        machine input alpha visits haccepted)).Nodup := by
  exact (acceptedTimedAlphaFiniteInputQueryOrder_perm_finRange
    machine input n alpha visits hschedule haccepted).symm.nodup
      (List.nodup_finRange n)

end OneTapeMagnification
end Frontier
end Pnp4
