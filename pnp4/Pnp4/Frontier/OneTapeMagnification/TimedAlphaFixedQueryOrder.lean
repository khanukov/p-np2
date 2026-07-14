import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.ArbitraryAlphaGlobalGlue
import Pnp4.Frontier.OneTapeMagnification.CrossingScheduleInputOrder

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# A fixed timed-alpha schedule determines a fixed query order

The advertised visit chain already fixes the work-block label and the input
endpoint of every chronological visit.  To turn those endpoints into genuine
half-open input intervals, one additional fact is indispensable: the input
head must not move left inside a visit.  This is not a syntactic consequence
of an arbitrary ambient alpha, whose endpoint fields may contain garbage.

This file therefore separates the construction into two layers.  The generic
conversion takes explicit visit-wise input monotonicity.  The accepted layer
derives that monotonicity from the exact local replay predicates, using the
one-way input-head semantics.  The resulting stable work-block grouping is a
permutation of one half-open interval and is duplicate-free.  Its data fields
are determined by the fixed advertised schedule; the machine and input occur
only in proofs that the advertised endpoint intervals are well formed.

No branching-program simulation or width bound is claimed here.
-/

/-- The exact extra condition needed to interpret one advertised visit as a
half-open interval of fresh input coordinates. -/
def TimedAlphaScheduledVisitInputMonotone
    {State : Type} {T b : Nat}
    (scheduled : TimedAlphaScheduledVisit State T b) : Prop :=
  scheduled.visit.entry.inputHead.val <=
    scheduled.visit.exit.inputHead.val

/-- Every visit in a chronological timed-alpha schedule has monotone input
endpoints. -/
def TimedAlphaScheduledVisitsInputMonotone
    {State : Type} {T b : Nat}
    (visits : List (TimedAlphaScheduledVisit State T b)) : Prop :=
  forall scheduled, scheduled ∈ visits ->
    TimedAlphaScheduledVisitInputMonotone scheduled

/-- One input-monotone timed-alpha visit as an ordinary crossing-schedule
segment.  All computational fields come directly from the advertised visit. -/
def timedAlphaScheduledVisitCrossingSegment
    {State : Type} {T b : Nat}
    (scheduled : TimedAlphaScheduledVisit State T b)
    (hmonotone : TimedAlphaScheduledVisitInputMonotone scheduled) :
    CrossingScheduleSegment (T / b + 1) where
  workBlock := scheduled.block
  startPosition := scheduled.visit.entry.inputHead.val
  stopPosition := scheduled.visit.exit.inputHead.val
  start_le_stop := hmonotone

@[simp]
theorem timedAlphaScheduledVisitCrossingSegment_workBlock
    {State : Type} {T b : Nat}
    (scheduled : TimedAlphaScheduledVisit State T b)
    (hmonotone : TimedAlphaScheduledVisitInputMonotone scheduled) :
    (timedAlphaScheduledVisitCrossingSegment scheduled hmonotone).workBlock =
      scheduled.block :=
  rfl

@[simp]
theorem timedAlphaScheduledVisitCrossingSegment_startPosition
    {State : Type} {T b : Nat}
    (scheduled : TimedAlphaScheduledVisit State T b)
    (hmonotone : TimedAlphaScheduledVisitInputMonotone scheduled) :
    (timedAlphaScheduledVisitCrossingSegment
      scheduled hmonotone).startPosition =
        scheduled.visit.entry.inputHead.val :=
  rfl

@[simp]
theorem timedAlphaScheduledVisitCrossingSegment_stopPosition
    {State : Type} {T b : Nat}
    (scheduled : TimedAlphaScheduledVisit State T b)
    (hmonotone : TimedAlphaScheduledVisitInputMonotone scheduled) :
    (timedAlphaScheduledVisitCrossingSegment
      scheduled hmonotone).stopPosition =
        scheduled.visit.exit.inputHead.val :=
  rfl

/-- Convert a whole advertised visit list to input intervals.  The recursive
definition ensures that only membership proofs for visits actually present in
the list are required. -/
def timedAlphaCrossingScheduleSegments
    {State : Type} {T b : Nat} :
    (visits : List (TimedAlphaScheduledVisit State T b)) ->
      TimedAlphaScheduledVisitsInputMonotone visits ->
        List (CrossingScheduleSegment (T / b + 1))
  | [], _ => []
  | scheduled :: rest, hmonotone =>
      timedAlphaScheduledVisitCrossingSegment scheduled
          (hmonotone scheduled (by simp)) ::
        timedAlphaCrossingScheduleSegments rest (by
          intro later hlater
          exact hmonotone later (by simp [hlater]))

@[simp]
theorem timedAlphaCrossingScheduleSegments_nil
    {State : Type} {T b : Nat}
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone
      ([] : List (TimedAlphaScheduledVisit State T b))) :
    timedAlphaCrossingScheduleSegments [] hmonotone = [] :=
  rfl

@[simp]
theorem timedAlphaCrossingScheduleSegments_length
    {State : Type} {T b : Nat}
    (visits : List (TimedAlphaScheduledVisit State T b))
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone visits) :
    (timedAlphaCrossingScheduleSegments visits hmonotone).length =
      visits.length := by
  induction visits with
  | nil => rfl
  | cons scheduled rest ih =>
      simp only [timedAlphaCrossingScheduleSegments, List.length_cons]
      exact congrArg Nat.succ (ih _)

/-- Stable work-block grouping of the advertised input intervals.  This is
the query-order data needed by a later read-once branching-program compiler;
the chaining proof is used only to establish its global properties. -/
def timedAlphaStableGroupedQueryOrder
    {State : Type} {T b : Nat}
    (visits : List (TimedAlphaScheduledVisit State T b))
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone visits) : List Nat :=
  stableGroupedCrossingScheduleInputOrder
    (timedAlphaCrossingScheduleSegments visits hmonotone)

/-- Input-head endpoint of the final visit of a nonempty advertised list. -/
def timedAlphaScheduledVisitsFinalInputHead
    {State : Type} {T b : Nat}
    (first : TimedAlphaScheduledVisit State T b) :
    List (TimedAlphaScheduledVisit State T b) -> Nat
  | [] => first.visit.exit.inputHead.val
  | next :: rest => timedAlphaScheduledVisitsFinalInputHead next rest

/-- Exact input-head endpoint link obtained from the advertised endpoint link. -/
theorem timedAlphaScheduledVisitLink_inputHead
    {State : Type} {T b : Nat}
    {earlier later : TimedAlphaScheduledVisit State T b}
    (hlink : TimedAlphaScheduledVisitLink earlier later) :
    earlier.visit.exit.inputHead.val =
      later.visit.entry.inputHead.val := by
  exact congrArg (fun endpoint => endpoint.inputHead.val) hlink.2.1

/-- Chained advertised endpoints become chained half-open input intervals. -/
theorem timedAlphaCrossingScheduleSegments_chained
    {State : Type} {T b : Nat}
    (first : TimedAlphaScheduledVisit State T b)
    (rest : List (TimedAlphaScheduledVisit State T b))
    (hchained : TimedAlphaScheduledVisitsChained (first :: rest))
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone (first :: rest)) :
    ChainedCrossingSchedule first.visit.entry.inputHead.val
      (timedAlphaScheduledVisitsFinalInputHead first rest)
      (timedAlphaCrossingScheduleSegments (first :: rest) hmonotone) := by
  induction rest generalizing first with
  | nil =>
      simp only [timedAlphaCrossingScheduleSegments,
        timedAlphaScheduledVisitsFinalInputHead]
      refine ChainedCrossingSchedule.cons
        (timedAlphaScheduledVisitCrossingSegment first _) ?_
      exact ChainedCrossingSchedule.nil first.visit.exit.inputHead.val
  | cons next rest ih =>
      unfold TimedAlphaScheduledVisitsChained at hchained
      rw [List.chain'_cons] at hchained
      let htailMonotone :
          TimedAlphaScheduledVisitsInputMonotone (next :: rest) := by
        intro scheduled hscheduled
        exact hmonotone scheduled (by simp [hscheduled])
      have htail := ih next hchained.2 htailMonotone
      have hinput := timedAlphaScheduledVisitLink_inputHead hchained.1
      simp only [timedAlphaCrossingScheduleSegments,
        timedAlphaScheduledVisitsFinalInputHead]
      refine ChainedCrossingSchedule.cons
        (timedAlphaScheduledVisitCrossingSegment first _) ?_
      simpa [hinput] using htail

/-- The fixed crossing schedule extracted from a nonempty timed-alpha visit
schedule. -/
def timedAlphaFixedCrossingSchedule
    {State : Type} {T b : Nat}
    (first : TimedAlphaScheduledVisit State T b)
    (rest : List (TimedAlphaScheduledVisit State T b))
    (hchained : TimedAlphaScheduledVisitsChained (first :: rest))
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone (first :: rest)) :
    FixedCrossingSchedule (T / b + 1) where
  startPosition := first.visit.entry.inputHead.val
  stopPosition := timedAlphaScheduledVisitsFinalInputHead first rest
  segments := timedAlphaCrossingScheduleSegments (first :: rest) hmonotone
  chained := timedAlphaCrossingScheduleSegments_chained
    first rest hchained hmonotone

@[simp]
theorem timedAlphaFixedCrossingSchedule_startPosition
    {State : Type} {T b : Nat}
    (first : TimedAlphaScheduledVisit State T b)
    (rest : List (TimedAlphaScheduledVisit State T b))
    (hchained : TimedAlphaScheduledVisitsChained (first :: rest))
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone (first :: rest)) :
    (timedAlphaFixedCrossingSchedule
      first rest hchained hmonotone).startPosition =
        first.visit.entry.inputHead.val :=
  rfl

@[simp]
theorem timedAlphaFixedCrossingSchedule_stopPosition
    {State : Type} {T b : Nat}
    (first : TimedAlphaScheduledVisit State T b)
    (rest : List (TimedAlphaScheduledVisit State T b))
    (hchained : TimedAlphaScheduledVisitsChained (first :: rest))
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone (first :: rest)) :
    (timedAlphaFixedCrossingSchedule
      first rest hchained hmonotone).stopPosition =
        timedAlphaScheduledVisitsFinalInputHead first rest :=
  rfl

/-- The fixed grouped query order is duplicate-free. -/
theorem timedAlphaFixedCrossingSchedule_readOnceInputOrder_nodup
    {State : Type} {T b : Nat}
    (first : TimedAlphaScheduledVisit State T b)
    (rest : List (TimedAlphaScheduledVisit State T b))
    (hchained : TimedAlphaScheduledVisitsChained (first :: rest))
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone (first :: rest)) :
    (FixedCrossingSchedule.readOnceInputOrder
      (timedAlphaFixedCrossingSchedule
        first rest hchained hmonotone)).Nodup :=
  FixedCrossingSchedule.readOnceInputOrder_nodup _

/-- The fixed grouped query order is a permutation of the single chronological
input interval exposed by the first and final advertised endpoints. -/
theorem timedAlphaFixedCrossingSchedule_readOnceInputOrder_perm_range'
    {State : Type} {T b : Nat}
    (first : TimedAlphaScheduledVisit State T b)
    (rest : List (TimedAlphaScheduledVisit State T b))
    (hchained : TimedAlphaScheduledVisitsChained (first :: rest))
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone (first :: rest)) :
    List.Perm (FixedCrossingSchedule.readOnceInputOrder
      (timedAlphaFixedCrossingSchedule first rest hchained hmonotone))
      (List.range' first.visit.entry.inputHead.val
        (timedAlphaScheduledVisitsFinalInputHead first rest -
          first.visit.entry.inputHead.val)) := by
  exact FixedCrossingSchedule.readOnceInputOrder_perm_range' _

/-- Direct query-order form of the duplicate-freedom theorem. -/
theorem timedAlphaStableGroupedQueryOrder_nodup
    {State : Type} {T b : Nat}
    (first : TimedAlphaScheduledVisit State T b)
    (rest : List (TimedAlphaScheduledVisit State T b))
    (hchained : TimedAlphaScheduledVisitsChained (first :: rest))
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone (first :: rest)) :
    (timedAlphaStableGroupedQueryOrder
      (first :: rest) hmonotone).Nodup := by
  exact stableGroupedCrossingScheduleInputOrder_nodup
    (timedAlphaCrossingScheduleSegments_chained
      first rest hchained hmonotone)

/-- Direct query-order form of the exact permutation theorem. -/
theorem timedAlphaStableGroupedQueryOrder_perm_range'
    {State : Type} {T b : Nat}
    (first : TimedAlphaScheduledVisit State T b)
    (rest : List (TimedAlphaScheduledVisit State T b))
    (hchained : TimedAlphaScheduledVisitsChained (first :: rest))
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone (first :: rest)) :
    List.Perm
      (timedAlphaStableGroupedQueryOrder (first :: rest) hmonotone)
      (List.range' first.visit.entry.inputHead.val
        (timedAlphaScheduledVisitsFinalInputHead first rest -
          first.visit.entry.inputHead.val)) := by
  exact (stableGroupedCrossingScheduleInputOrder_perm
      (timedAlphaCrossingScheduleSegments (first :: rest) hmonotone)).trans
    (List.Perm.of_eq
      (chronologicalCrossingScheduleInputOrder_eq_range'
        (timedAlphaCrossingScheduleSegments_chained
          first rest hchained hmonotone)))

/-- Exact local replay validity proves that an advertised visit's input
endpoint cannot move left. -/
theorem fixedAlphaBlockVisitValid_inputMonotone
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (block : Fin (T / b + 1))
    (visit : FixedAlphaBlockVisit machine.State T)
    (carried : WorkSlab
      (advertisedBlockWidth alpha.offsets block))
    (hvalid : FixedAlphaBlockVisitValid
      machine input alpha block visit carried) :
    visit.entry.inputHead.val <= visit.exit.inputHead.val := by
  calc
    visit.entry.inputHead.val =
        (fixedAlphaBlockVisitEntryConfiguration
          alpha block visit carried).inputHead := rfl
    _ <= (fixedAlphaBlockVisitRun
          machine input alpha block visit carried).inputHead :=
      inputHead_le_runFrom machine input _ _
    _ = visit.exit.inputHead.val := hvalid.2.2.1.symm

/-- A successful chronological interleaving of all local replay checks proves
input monotonicity for every scheduled visit. -/
theorem allScheduledVisitsReplayAccepted_inputMonotone
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (store : FixedAlphaSlabStore alpha)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (haccepted : AllScheduledVisitsReplayAccepted
      machine input alpha store visits) :
    TimedAlphaScheduledVisitsInputMonotone visits := by
  induction visits generalizing store with
  | nil =>
      intro scheduled hscheduled
      simp at hscheduled
  | cons first rest ih =>
      intro scheduled hscheduled
      rcases List.mem_cons.mp hscheduled with hfirst | hrest
      · subst scheduled
        exact fixedAlphaBlockVisitValid_inputMonotone
          machine input alpha first.block first.visit (store first.block)
            haccepted.1
      · exact ih
          (updateFixedAlphaSlabStore machine input alpha store first)
          haccepted.2 scheduled hrest

/-- Simultaneous per-block acceptance from blank therefore supplies the exact
monotonicity premise needed by the fixed-query-order construction. -/
theorem allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha visits) :
    TimedAlphaScheduledVisitsInputMonotone visits := by
  exact allScheduledVisitsReplayAccepted_inputMonotone
    machine input alpha (blankFixedAlphaSlabStore alpha) visits
      (allScheduledVisitsReplayAccepted_fromBlank_of_allBlockLists
        machine input alpha visits haccepted)

/-- Stable grouped query order certified by simultaneous local replay
acceptance.  The resulting list is computed from the advertised visits; the
acceptance proof only supplies the erased interval inequalities. -/
def acceptedTimedAlphaStableGroupedQueryOrder
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha visits) : List Nat :=
  timedAlphaStableGroupedQueryOrder visits
    (allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
      machine input alpha visits haccepted)

/-- The endpoint helper is the input-head projection of the existing final
endpoint helper. -/
theorem timedAlphaScheduledVisitsFinalInputHead_eq_finalExit
    {State : Type} {T b : Nat}
    (first : TimedAlphaScheduledVisit State T b)
    (rest : List (TimedAlphaScheduledVisit State T b)) :
    timedAlphaScheduledVisitsFinalInputHead first rest =
      (timedAlphaScheduledVisitsFinalExit first rest).inputHead.val := by
  induction rest generalizing first with
  | nil => rfl
  | cons next rest ih => exact ih next

/-- For a valid complete schedule, the first and final input endpoints are
exactly zero and the alpha terminal input head. -/
theorem timedAlphaVisitScheduleValid_inputEndpoints
    (machine : DeterministicMachine)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (first : TimedAlphaScheduledVisit machine.State T b)
    (rest : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha (first :: rest)) :
    first.visit.entry.inputHead.val = 0 /\
      timedAlphaScheduledVisitsFinalInputHead first rest =
        alpha.terminal.inputHead.val := by
  have hcover := hschedule.coversHorizon machine
  change first.visit.entryTime.val = 0 /\
      first.visit.entry = initialFixedAlphaVisitEndpoint machine T /\
      (timedAlphaScheduledVisitsFinalExitTime first rest).val = T /\
      timedAlphaScheduledVisitsFinalExit first rest = alpha.terminal at hcover
  constructor
  · have hentry := congrArg (fun endpoint => endpoint.inputHead.val) hcover.2.1
    simpa [initialFixedAlphaVisitEndpoint] using hentry
  · rw [timedAlphaScheduledVisitsFinalInputHead_eq_finalExit,
      hcover.2.2.2]

/-- Full accepted-schedule theorem, including the empty `T = 0` schedule:
the stable grouped query order is a permutation of every fresh coordinate
from zero to the advertised terminal input head. -/
theorem acceptedTimedAlphaStableGroupedQueryOrder_perm_range
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha visits)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha visits) :
    List.Perm
      (acceptedTimedAlphaStableGroupedQueryOrder
        machine input alpha visits haccepted)
      (List.range alpha.terminal.inputHead.val) := by
  cases visits with
  | nil =>
      have hcover := hschedule.coversHorizon machine
      change T = 0 /\
        alpha.terminal = initialFixedAlphaVisitEndpoint machine T at hcover
      have hterminal : alpha.terminal.inputHead.val = 0 := by
        rw [hcover.2]
        rfl
      simp [acceptedTimedAlphaStableGroupedQueryOrder,
        timedAlphaStableGroupedQueryOrder,
        timedAlphaCrossingScheduleSegments,
        stableGroupedCrossingScheduleInputOrder,
        stableGroupedCrossingScheduleSegments, hterminal]
  | cons first rest =>
      have hendpoints := timedAlphaVisitScheduleValid_inputEndpoints
        machine alpha first rest hschedule
      obtain ⟨finalCursor, visitsSoFar, hfold, hfinish, hchained⟩ :=
        hschedule.2
      let hmonotone :
          TimedAlphaScheduledVisitsInputMonotone (first :: rest) :=
        allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
          machine input alpha (first :: rest) haccepted
      have hperm := timedAlphaStableGroupedQueryOrder_perm_range'
        first rest hchained hmonotone
      simpa [acceptedTimedAlphaStableGroupedQueryOrder, hmonotone,
        hendpoints.1, hendpoints.2, List.range_eq_range'] using hperm

/-- The full accepted alpha-fixed grouped query order is duplicate-free,
including the empty schedule. -/
theorem acceptedTimedAlphaStableGroupedQueryOrder_nodup
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat} (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha visits)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha visits) :
    (acceptedTimedAlphaStableGroupedQueryOrder
      machine input alpha visits haccepted).Nodup := by
  have hperm := acceptedTimedAlphaStableGroupedQueryOrder_perm_range
    machine input alpha visits hschedule haccepted
  exact hperm.symm.nodup List.nodup_range

end OneTapeMagnification
end Frontier
end Pnp4
