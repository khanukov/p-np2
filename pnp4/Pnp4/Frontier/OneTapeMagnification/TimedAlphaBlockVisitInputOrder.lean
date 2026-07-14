import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.AdaptiveCachedBlockVisitListReadOnce
import Pnp4.Frontier.OneTapeMagnification.TimedAlphaFixedQueryOrder

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Cross-visit input order for a fixed timed-alpha block

The adaptive verifier for a list of visits needs one static fact at each
carry boundary: the next advertised entry input head is not left of the
previous advertised exit input head.  This file derives that fact for every
stable fixed-block sublist of a globally chained, visit-wise input-monotone
timed-alpha schedule.

Chaining gives equality at adjacent global visit endpoints.  Monotonicity
inside the intervening visits then telescopes across visits of other blocks.
Stable filtering and erasing the repeated block label preserve the resulting
pairwise order.  Thus the explicit premise of the multi-visit read-once
compiler is supplied by the already established timed-alpha acceptance
surface; it is not an additional machine assumption.
-/

/-- An earlier scheduled visit finishes no later on the one-way input tape
than a later scheduled visit starts. -/
def TimedAlphaScheduledVisitInputPrecedes
    {State : Type} {T b : Nat}
    (earlier later : TimedAlphaScheduledVisit State T b) : Prop :=
  earlier.visit.exit.inputHead.val ≤ later.visit.entry.inputHead.val

/-- In a chained, visit-wise monotone schedule, the first visit input-
precedes every later visit. -/
theorem timedAlphaScheduledVisits_head_inputPrecedes
    {State : Type} {T b : Nat}
    (first : TimedAlphaScheduledVisit State T b)
    (rest : List (TimedAlphaScheduledVisit State T b))
    (hchained : TimedAlphaScheduledVisitsChained (first :: rest))
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone (first :: rest)) :
    ∀ later, later ∈ rest ->
      TimedAlphaScheduledVisitInputPrecedes first later := by
  induction rest generalizing first with
  | nil =>
      intro later hmem
      simp at hmem
  | cons next rest ih =>
      unfold TimedAlphaScheduledVisitsChained at hchained
      rw [List.chain'_cons] at hchained
      have hnextMonotone :
          TimedAlphaScheduledVisitInputMonotone next :=
        hmonotone next (by simp)
      have htailMonotone :
          TimedAlphaScheduledVisitsInputMonotone (next :: rest) := by
        intro scheduled hscheduled
        exact hmonotone scheduled (by simp [hscheduled])
      intro later hmem
      rw [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact Nat.le_of_eq
          (timedAlphaScheduledVisitLink_inputHead hchained.1)
      · have htail := ih next hchained.2 htailMonotone later hmem
        calc
          first.visit.exit.inputHead.val =
              next.visit.entry.inputHead.val :=
            timedAlphaScheduledVisitLink_inputHead hchained.1
          _ ≤ next.visit.exit.inputHead.val := hnextMonotone
          _ ≤ later.visit.entry.inputHead.val := htail

/-- The full globally chained schedule is pairwise ordered at input
boundaries. -/
theorem timedAlphaScheduledVisits_pairwise_inputPrecedes
    {State : Type} {T b : Nat}
    (visits : List (TimedAlphaScheduledVisit State T b))
    (hchained : TimedAlphaScheduledVisitsChained visits)
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone visits) :
    visits.Pairwise TimedAlphaScheduledVisitInputPrecedes := by
  induction visits with
  | nil => simp
  | cons first rest ih =>
      rw [List.pairwise_cons]
      constructor
      · exact timedAlphaScheduledVisits_head_inputPrecedes
          first rest hchained hmonotone
      · have htailChained : TimedAlphaScheduledVisitsChained rest := by
          cases rest with
          | nil => simp [TimedAlphaScheduledVisitsChained]
          | cons next tail =>
              unfold TimedAlphaScheduledVisitsChained at hchained ⊢
              rw [List.chain'_cons] at hchained
              exact hchained.2
        have htailMonotone :
            TimedAlphaScheduledVisitsInputMonotone rest := by
          intro scheduled hscheduled
          exact hmonotone scheduled (by simp [hscheduled])
        exact ih htailChained htailMonotone

/-- Erasing block labels preserves pairwise input-boundary order. -/
theorem timedAlphaScheduledVisits_map_visit_pairwise_inputPrecedes
    {State : Type} {T b : Nat}
    (visits : List (TimedAlphaScheduledVisit State T b))
    (hpairwise : visits.Pairwise TimedAlphaScheduledVisitInputPrecedes) :
    (visits.map TimedAlphaScheduledVisit.visit).Pairwise
      (fun earlier later =>
        earlier.exit.inputHead.val ≤ later.entry.inputHead.val) := by
  induction visits with
  | nil => simp
  | cons first rest ih =>
      rw [List.pairwise_cons] at hpairwise
      simp only [List.map_cons, List.pairwise_cons]
      constructor
      · intro later hlater
        obtain ⟨scheduled, hscheduled, rfl⟩ := List.mem_map.mp hlater
        exact hpairwise.1 scheduled hscheduled
      · exact ih hpairwise.2

/-- Stable filtering by one block retains pairwise input-boundary order. -/
theorem timedAlphaBlockVisits_pairwise_inputPrecedes
    {State : Type} {T b : Nat}
    (target : Fin (T / b + 1))
    (visits : List (TimedAlphaScheduledVisit State T b))
    (hchained : TimedAlphaScheduledVisitsChained visits)
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone visits) :
    (timedAlphaBlockVisits target visits).Pairwise
      (fun earlier later =>
        earlier.exit.inputHead.val ≤ later.entry.inputHead.val) := by
  let selected := timedAlphaScheduledVisitsForBlock target visits
  have hglobal := timedAlphaScheduledVisits_pairwise_inputPrecedes
    visits hchained hmonotone
  have hselected :
      selected.Pairwise TimedAlphaScheduledVisitInputPrecedes :=
    hglobal.filter _
  simpa [timedAlphaBlockVisits, selected] using
    timedAlphaScheduledVisits_map_visit_pairwise_inputPrecedes
      selected hselected

/-- Pairwise order implies the exact adjacent-index premise used by the
multi-visit adaptive compiler. -/
theorem fixedAlphaBlockVisitInputHeadsOrdered_of_pairwise
    {State : Type} {T : Nat}
    (visits : List (FixedAlphaBlockVisit State T))
    (hpairwise : visits.Pairwise (fun earlier later =>
      earlier.exit.inputHead.val ≤ later.entry.inputHead.val)) :
    FixedAlphaBlockVisitInputHeadsOrdered visits := by
  intro cursor hnext
  have hordered := (List.pairwise_iff_getElem.mp hpairwise)
    cursor.val (cursor.val + 1) cursor.isLt hnext (by omega)
  simpa [List.get_eq_getElem] using hordered

/-- Every fixed-block sublist of a chained, visit-wise monotone schedule
satisfies the cross-visit input order required by its adaptive compiler. -/
theorem timedAlphaBlockVisits_inputHeadsOrdered
    {State : Type} {T b : Nat}
    (target : Fin (T / b + 1))
    (visits : List (TimedAlphaScheduledVisit State T b))
    (hchained : TimedAlphaScheduledVisitsChained visits)
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone visits) :
    FixedAlphaBlockVisitInputHeadsOrdered
      (timedAlphaBlockVisits target visits) := by
  exact fixedAlphaBlockVisitInputHeadsOrdered_of_pairwise _
    (timedAlphaBlockVisits_pairwise_inputPrecedes
      target visits hchained hmonotone)

/-- Schedule validity supplies global chaining; only the already isolated
visit-wise input monotonicity premise remains. -/
theorem TimedAlphaVisitScheduleValid.blockVisitsInputHeadsOrdered
    (machine : DeterministicMachine)
    {T b : Nat}
    {alpha : AmbientTimedCanonicalAlpha machine.State T b}
    {visits : List (TimedAlphaScheduledVisit machine.State T b)}
    (hschedule : TimedAlphaVisitScheduleValid machine alpha visits)
    (hmonotone : TimedAlphaScheduledVisitsInputMonotone visits)
    (target : Fin (T / b + 1)) :
    FixedAlphaBlockVisitInputHeadsOrdered
      (timedAlphaBlockVisits target visits) := by
  obtain ⟨_, finalCursor, visitsSoFar, _, _, hchained⟩ := hschedule
  exact timedAlphaBlockVisits_inputHeadsOrdered
    target visits hchained hmonotone

/-- Simultaneous local acceptance discharges visit-wise monotonicity, so a
valid accepted timed-alpha schedule supplies the compiler premise without
any extra assumption. -/
theorem timedAlphaBlockVisits_inputHeadsOrdered_of_allBlockListsAccepted
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b))
    (hschedule : TimedAlphaVisitScheduleValid machine alpha visits)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      machine input alpha visits)
    (target : Fin (T / b + 1)) :
    FixedAlphaBlockVisitInputHeadsOrdered
      (timedAlphaBlockVisits target visits) := by
  exact hschedule.blockVisitsInputHeadsOrdered machine
    (allFixedAlphaBlockVisitListsAcceptedFromBlank_inputMonotone
      machine input alpha visits haccepted) target

/-- Simultaneous block acceptance also supplies all proof-only entry-inside
facts needed to instantiate the finite cached list verifier. -/
def acceptedTimedAlphaBlockVisitEntriesInside
    (machine : DeterministicMachine) (input : List Bool)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      (cachedInputMachine machine) input alpha scheduled)
    (block : Fin (T / b + 1)) :
    FixedAlphaBlockVisitEntriesInside alpha block
      (timedAlphaBlockVisits block scheduled) := by
  have hblock := haccepted block
  change FixedAlphaBlockVisitListAccepted
    (cachedInputMachine machine) input alpha block
      (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
      (timedAlphaBlockVisits block scheduled) at hblock
  exact fixedAlphaBlockVisitEntriesInside_of_replayAccepted
    (cachedInputMachine machine) input alpha block
      (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
      (timedAlphaBlockVisits block scheduled) hblock.2

/-- The actual per-block adaptive program selected by an accepted timed-alpha
schedule.  Acceptance proofs only initialize erased entry-inside evidence;
all executable fields are the advertised block list and finite verifier. -/
def compileAdaptiveAcceptedTimedAlphaBlockVisitList
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      (cachedInputMachine machine) input alpha scheduled)
    (block : Fin (T / b + 1)) :
    LayeredQueryProgram n
      (finiteCachedBlockVisitListFuel
        (timedAlphaBlockVisits block scheduled)) :=
  compileAdaptiveFiniteCachedFixedAlphaBlockVisitList machine alpha block
    (blankWorkSlab (advertisedBlockWidth alpha.offsets block))
    (timedAlphaBlockVisits block scheduled)
    (acceptedTimedAlphaBlockVisitEntriesInside machine input alpha scheduled
      haccepted block)

/-- For every valid and locally accepted timed-alpha schedule, each compiled
fixed-block list program is read-once.  The cross-visit order premise is now
fully discharged by global chaining and one-way input monotonicity. -/
theorem compileAdaptiveAcceptedTimedAlphaBlockVisitList_isReadOnce
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {n T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hschedule : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha scheduled)
    (haccepted : AllFixedAlphaBlockVisitListsAcceptedFromBlank
      (cachedInputMachine machine) input alpha scheduled)
    (block : Fin (T / b + 1)) :
    (compileAdaptiveAcceptedTimedAlphaBlockVisitList (n := n) machine input
      alpha scheduled haccepted block).IsReadOnce := by
  apply compileAdaptiveFiniteCachedFixedAlphaBlockVisitList_isReadOnce
  exact timedAlphaBlockVisits_inputHeadsOrdered_of_allBlockListsAccepted
    (cachedInputMachine machine) input alpha scheduled hschedule haccepted
      block

end OneTapeMagnification
end Frontier
end Pnp4
