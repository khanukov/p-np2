import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.TimedAlphaAdjacentCutFactorization

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Disjoint query supports for timed-alpha block and edge factors

The advertised query supports of arbitrary scheduled blocks are not disjoint
without schedule geometry.  For example, two visits carrying different block
labels may both advertise the input interval `[0, 1)`, so coordinate zero lies
in both supports.

The exact semantic ingredients used below are exposed separately:

* `TimedAlphaScheduledVisitsChained` prevents unrelated advertised endpoints;
* `TimedAlphaScheduledVisitsInputMonotone` prevents a chained schedule from
  moving the advertised input head backwards and later reusing a coordinate.

Neither ingredient alone suffices.  Chaining alone permits endpoint pattern
`0 -> 2 -> 0 -> 1`; the middle backwards visit has empty fresh support, while
the first and third visits reuse coordinate zero.  Monotonicity alone permits
two unrelated copies of `[0, 1)`.  Schedule validity supplies chaining and
accepted replay supplies monotonicity, yielding the semantic corollaries.

Once distinct block supports are disjoint, the union supports of two bucket
edges are disjoint whenever their two-element source-block sets are disjoint.
In particular, distinct edges of the same parity are separated by at least
one edge and therefore form a pairwise-disjoint parity layer.
-/

/-- Extract disjointness of two different fibers from a pairwise-disjoint
indexed list.  The two indices may occur in either order. -/
private theorem listDisjoint_of_pairwiseOn_mem_ne
    {Index Coordinate : Type}
    {indices : List Index} {coordinates : Index → List Coordinate}
    (hpairwise : indices.Pairwise
      (Function.onFun List.Disjoint coordinates))
    {left right : Index}
    (hleft : left ∈ indices) (hright : right ∈ indices)
    (hne : left ≠ right) :
    (coordinates left).Disjoint (coordinates right) := by
  induction indices generalizing left right with
  | nil => simp at hleft
  | cons head tail ih =>
      rw [List.pairwise_cons] at hpairwise
      simp only [List.mem_cons] at hleft hright
      rcases hleft with rfl | hleft
      · rcases hright with rfl | hright
        · exact False.elim (hne rfl)
        · exact hpairwise.1 right hright
      · rcases hright with rfl | hright
        · exact (hpairwise.1 left hleft).symm
        · exact ih hpairwise.2 hleft hright hne

/-- Distinct scheduled blocks have disjoint advertised finite query supports
under precisely the schedule geometry used by the fixed master-order proof:
global endpoint chaining and visit-wise input monotonicity. -/
theorem finiteCachedTimedScheduleBlockQuerySupport_disjoint_of_ne
    {State : Type} {n T b : Nat}
    (scheduled : List (TimedAlphaScheduledVisit State T b))
    (hchained : TimedAlphaScheduledVisitsChained scheduled)
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled)
    {left right : Fin (T / b + 1)} (hne : left ≠ right) :
    Disjoint
      (finiteCachedTimedScheduleBlockQuerySupport n scheduled left)
      (finiteCachedTimedScheduleBlockQuerySupport n scheduled right) := by
  let blockOrder : Fin (T / b + 1) → List (Fin n) := fun block =>
    finiteCachedBlockVisitListAdvertisedQueryOrder n
      (timedAlphaBlockVisits block scheduled)
  have hmasterNodup :
      (finiteCachedTimedAlphaScheduleMasterQueryOrder
        (n := n) scheduled hmonotone).Nodup :=
    finiteCachedTimedAlphaScheduleMasterQueryOrder_nodup
      scheduled hchained hmonotone
  have hflatNodup :
      ((List.finRange (T / b + 1)).flatMap blockOrder).Nodup := by
    rw [← finiteCachedTimedAlphaScheduleMasterQueryOrder_eq_blockVisits
      (n := n) scheduled hmonotone]
    exact hmasterNodup
  have hpairwise : (List.finRange (T / b + 1)).Pairwise
      (Function.onFun List.Disjoint blockOrder) :=
    (List.nodup_flatMap.mp hflatNodup).2
  have hlist : (blockOrder left).Disjoint (blockOrder right) :=
    listDisjoint_of_pairwiseOn_mem_ne hpairwise
      (List.mem_finRange left) (List.mem_finRange right) hne
  rw [Finset.disjoint_left]
  intro coordinate hleft hright
  exact (List.disjoint_left.mp hlist)
    (by
      simpa [blockOrder, finiteCachedTimedScheduleBlockQuerySupport] using
        hleft)
    (by
      simpa [blockOrder, finiteCachedTimedScheduleBlockQuerySupport] using
        hright)

/-- Valid schedule plus simultaneous accepted replay discharge the two
structural hypotheses of block-support disjointness. -/
theorem finiteCachedTimedScheduleBlockQuerySupport_disjoint_of_scheduleReplay
    (machine : DeterministicMachine) (input : List Bool)
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha scheduled)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha scheduled)
    {left right : Fin (T / b + 1)} (hne : left ≠ right) :
    Disjoint
      (finiteCachedTimedScheduleBlockQuerySupport n scheduled left)
      (finiteCachedTimedScheduleBlockQuerySupport n scheduled right) := by
  have hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled :=
    allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
      machine input alpha scheduled haccepted
  obtain ⟨_syntactic, _finalCursor, _visitsSoFar, _hfold, _hfinish,
    hchained⟩ := hschedule
  exact finiteCachedTimedScheduleBlockQuerySupport_disjoint_of_ne
    scheduled hchained hmonotone hne

/-- Exact graph-theoretic lifting condition: the union supports of two bucket
edges are disjoint when every source block of the first edge differs from
every source block of the second edge. -/
theorem
    finiteCachedTimedScheduleAdjacentCutQuerySupport_disjoint_of_sourceBlocks_ne
    {State : Type} {n T b : Nat}
    (scheduled : List (TimedAlphaScheduledVisit State T b))
    (hchained : TimedAlphaScheduledVisitsChained scheduled)
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled)
    (left right : Fin (T / b))
    (hLL : leftSourceBlockOfBucket left ≠ leftSourceBlockOfBucket right)
    (hLR : leftSourceBlockOfBucket left ≠ rightSourceBlockOfBucket right)
    (hRL : rightSourceBlockOfBucket left ≠ leftSourceBlockOfBucket right)
    (hRR : rightSourceBlockOfBucket left ≠ rightSourceBlockOfBucket right) :
    Disjoint
      (finiteCachedTimedScheduleAdjacentCutQuerySupport n scheduled left)
      (finiteCachedTimedScheduleAdjacentCutQuerySupport n scheduled right) := by
  rw [Finset.disjoint_left]
  intro coordinate hleft hright
  simp only [finiteCachedTimedScheduleAdjacentCutQuerySupport,
    Finset.mem_union] at hleft hright
  rcases hleft with hleft | hleft <;>
    rcases hright with hright | hright
  · exact (Finset.disjoint_left.mp
      (finiteCachedTimedScheduleBlockQuerySupport_disjoint_of_ne
        scheduled hchained hmonotone hLL)) hleft hright
  · exact (Finset.disjoint_left.mp
      (finiteCachedTimedScheduleBlockQuerySupport_disjoint_of_ne
        scheduled hchained hmonotone hLR)) hleft hright
  · exact (Finset.disjoint_left.mp
      (finiteCachedTimedScheduleBlockQuerySupport_disjoint_of_ne
        scheduled hchained hmonotone hRL)) hleft hright
  · exact (Finset.disjoint_left.mp
      (finiteCachedTimedScheduleBlockQuerySupport_disjoint_of_ne
        scheduled hchained hmonotone hRR)) hleft hright

/-- Numerical edge separation is a concise sufficient form of the exact
four-source-block condition. -/
theorem
    finiteCachedTimedScheduleAdjacentCutQuerySupport_disjoint_of_separated
    {State : Type} {n T b : Nat}
    (scheduled : List (TimedAlphaScheduledVisit State T b))
    (hchained : TimedAlphaScheduledVisitsChained scheduled)
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled)
    (left right : Fin (T / b))
    (hseparated : left.val + 1 < right.val ∨ right.val + 1 < left.val) :
    Disjoint
      (finiteCachedTimedScheduleAdjacentCutQuerySupport n scheduled left)
      (finiteCachedTimedScheduleAdjacentCutQuerySupport n scheduled right) := by
  apply
    finiteCachedTimedScheduleAdjacentCutQuerySupport_disjoint_of_sourceBlocks_ne
      scheduled hchained hmonotone left right
  · intro heq
    have hval := congrArg Fin.val heq
    simp [leftSourceBlockOfBucket] at hval
    omega
  · intro heq
    have hval := congrArg Fin.val heq
    simp [leftSourceBlockOfBucket, rightSourceBlockOfBucket] at hval
    omega
  · intro heq
    have hval := congrArg Fin.val heq
    simp [leftSourceBlockOfBucket, rightSourceBlockOfBucket] at hval
    omega
  · intro heq
    have hval := congrArg Fin.val heq
    simp [rightSourceBlockOfBucket] at hval
    omega

/-- **Parity-layer disjointness.** Distinct bucket edges of one parity have
pairwise-disjoint union query supports. -/
theorem
    finiteCachedTimedScheduleAdjacentCutQuerySupport_disjoint_of_sameParity
    {State : Type} {n T b : Nat}
    (scheduled : List (TimedAlphaScheduledVisit State T b))
    (hchained : TimedAlphaScheduledVisitsChained scheduled)
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled)
    (left right : Fin (T / b))
    (hne : left ≠ right)
    (hparity : left.val % 2 = right.val % 2) :
    Disjoint
      (finiteCachedTimedScheduleAdjacentCutQuerySupport n scheduled left)
      (finiteCachedTimedScheduleAdjacentCutQuerySupport n scheduled right) := by
  have hvalNe : left.val ≠ right.val := by
    intro hval
    exact hne (Fin.ext hval)
  apply finiteCachedTimedScheduleAdjacentCutQuerySupport_disjoint_of_separated
    scheduled hchained hmonotone left right
  omega

/-- Valid schedule and accepted replay specialize parity-layer disjointness
without exposing either structural proof obligation to downstream users. -/
theorem
    finiteCachedTimedScheduleAdjacentCutQuerySupport_disjoint_of_scheduleReplay_sameParity
    (machine : DeterministicMachine) (input : List Bool)
    {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha scheduled)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha scheduled)
    (left right : Fin (T / b))
    (hne : left ≠ right)
    (hparity : left.val % 2 = right.val % 2) :
    Disjoint
      (finiteCachedTimedScheduleAdjacentCutQuerySupport n scheduled left)
      (finiteCachedTimedScheduleAdjacentCutQuerySupport n scheduled right) := by
  have hmonotone : TimedAlphaScheduledVisitsInputMonotone scheduled :=
    allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
      machine input alpha scheduled haccepted
  obtain ⟨_syntactic, _finalCursor, _visitsSoFar, _hfold, _hfinish,
    hchained⟩ := hschedule
  exact
    finiteCachedTimedScheduleAdjacentCutQuerySupport_disjoint_of_sameParity
      scheduled hchained hmonotone left right hne hparity

end OneTapeMagnification
end Frontier
end Pnp4
