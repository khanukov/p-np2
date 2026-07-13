import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.AdvertisedCrossingEndpoints
import Pnp4.Frontier.OneTapeMagnification.TimedAlphaWordValidity

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Visit schedules advertised by a timed alpha word

This file turns the decoded chronological crossing tokens of one fixed ambient
timed alpha into an advertised visit schedule.  The construction is entirely
advertised-side: it uses the alpha's offsets, tokens, terminal endpoint, and a
machine's initial control state, but no actual run or maximal-group
decomposition.

A cursor stores the current post-time, bounded endpoint, and work-block label.
Folding one token requires that the cursor block equal the token's source
block and that the cursor time precede the crossing transition.  The emitted
visit ends at the crossing post-time and at the token-forced post endpoint;
the next cursor is the token's destination block and post endpoint.  Finishing
at time `T` checks exact terminal-endpoint equality and emits no zero-length
visit.  Finishing before `T` emits one final positive visit and requires the
terminal work head to remain in its advertised block.

The public schedule predicate also requires the padded word to be prefix
shaped with strictly increasing token times and records exact adjacent
time/endpoint chaining with distinct adjacent blocks.  Stable filtering by one
block then gives the strict visit separation consumed by
`FixedAlphaBlockVisitListAccepted`.

This module does not assert local machine replay validity, cut minimality, or
completeness for the actual extracted alpha.  The remaining actual-completeness
invariant is an ordered correspondence between decoded timed tokens and the
actual maximal groups, including the terminal-crossing convention; no such
list-level correspondence is assumed here.
-/

/-- Advertised state carried while folding chronological crossing tokens. -/
structure TimedAlphaVisitCursor (State : Type) (T b : Nat) where
  time : Fin (T + 1)
  endpoint : FixedAlphaVisitEndpoint State T
  block : Fin (T / b + 1)

/-- One chronological visit together with the advertised work block that owns
all of its pre-transition steps. -/
structure TimedAlphaScheduledVisit (State : Type) (T b : Nat) where
  block : Fin (T / b + 1)
  visit : FixedAlphaBlockVisit State T

/-- Initial advertised cursor: time zero, the machine's blank-start finite
endpoint, and block zero. -/
def initialTimedAlphaVisitCursor
    (machine : DeterministicMachine) (T b : Nat) :
    TimedAlphaVisitCursor machine.State T b :=
  { time := ⟨0, by omega⟩
    endpoint := initialFixedAlphaVisitEndpoint machine T
    block := ⟨0, Nat.succ_pos _⟩ }

/-- Post-time of the transition named by one timed crossing token. -/
def advertisedTimedCrossingPostTime
    {State : Type} {T b : Nat}
    (crossing : TimedCanonicalCrossingToken State T b) : Fin (T + 1) :=
  ⟨crossing.sourceTime.val + 1, by omega⟩

@[simp]
theorem advertisedTimedCrossingPostTime_val
    {State : Type} {T b : Nat}
    (crossing : TimedCanonicalCrossingToken State T b) :
    (advertisedTimedCrossingPostTime crossing).val =
      crossing.sourceTime.val + 1 :=
  rfl

/-- Cursor forced immediately after one advertised crossing. -/
def timedAlphaVisitCursorAfterCrossing
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (crossing : TimedCanonicalCrossingToken State T b) :
    TimedAlphaVisitCursor State T b :=
  { time := advertisedTimedCrossingPostTime crossing
    endpoint := advertisedTimedCrossingPostEndpoint alpha crossing
    block := advertisedTimedCrossingDestinationBlock crossing }

/-- Visit emitted from a cursor by one later advertised crossing. -/
def timedAlphaScheduledVisitAtCrossing
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (cursor : TimedAlphaVisitCursor State T b)
    (crossing : TimedCanonicalCrossingToken State T b)
    (htime : cursor.time.val ≤ crossing.sourceTime.val) :
    TimedAlphaScheduledVisit State T b :=
  { block := cursor.block
    visit :=
      { entryTime := cursor.time
        exitTime := advertisedTimedCrossingPostTime crossing
        entryTime_lt_exitTime := by
          change cursor.time.val < crossing.sourceTime.val + 1
          omega
        entry := cursor.endpoint
        exit := advertisedTimedCrossingPostEndpoint alpha crossing } }

/-- Final positive visit when the token fold stops strictly before `T`. -/
def timedAlphaFinalScheduledVisit
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (cursor : TimedAlphaVisitCursor State T b)
    (htime : cursor.time.val < T) :
    TimedAlphaScheduledVisit State T b :=
  { block := cursor.block
    visit :=
      { entryTime := cursor.time
        exitTime := ⟨T, by omega⟩
        entryTime_lt_exitTime := by
          change cursor.time.val < T
          exact htime
        entry := cursor.endpoint
        exit := alpha.terminal } }

/-- Exact advertised fold of a token list.

The two premises on `cons` are the non-negotiable chronology and block-chain
checks.  The emitted visit and next cursor are deterministic once they hold. -/
inductive TimedAlphaTokenVisitFold
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b) :
    TimedAlphaVisitCursor State T b →
      List (TimedCanonicalCrossingToken State T b) →
      List (TimedAlphaScheduledVisit State T b) →
      TimedAlphaVisitCursor State T b → Prop
  | nil (cursor : TimedAlphaVisitCursor State T b) :
      TimedAlphaTokenVisitFold alpha cursor [] [] cursor
  | cons
      (cursor : TimedAlphaVisitCursor State T b)
      (crossing : TimedCanonicalCrossingToken State T b)
      (rest : List (TimedCanonicalCrossingToken State T b))
      (visits : List (TimedAlphaScheduledVisit State T b))
      (finalCursor : TimedAlphaVisitCursor State T b)
      (htime : cursor.time.val ≤ crossing.sourceTime.val)
      (hsource : cursor.block =
        advertisedTimedCrossingSourceBlock crossing)
      (htail : TimedAlphaTokenVisitFold alpha
        (timedAlphaVisitCursorAfterCrossing alpha crossing)
        rest visits finalCursor) :
      TimedAlphaTokenVisitFold alpha cursor (crossing :: rest)
        (timedAlphaScheduledVisitAtCrossing
          alpha cursor crossing htime :: visits) finalCursor

/-- Exact link required between adjacent chronological scheduled visits. -/
def TimedAlphaScheduledVisitLink
    {State : Type} {T b : Nat}
    (earlier later : TimedAlphaScheduledVisit State T b) : Prop :=
  earlier.visit.exitTime = later.visit.entryTime ∧
    earlier.visit.exit = later.visit.entry ∧
    earlier.block ≠ later.block

/-- A complete chronological list records every adjacent endpoint and block
change exactly. -/
def TimedAlphaScheduledVisitsChained
    {State : Type} {T b : Nat}
    (visits : List (TimedAlphaScheduledVisit State T b)) : Prop :=
  visits.Chain' TimedAlphaScheduledVisitLink

/-- Terminal completion of a token-fold prefix.

If the cursor already equals time `T`, exact endpoint equality is required and
no zero-length visit is emitted.  Otherwise one positive final visit is added;
the terminal head must lie in the cursor block.  This membership is the local
ownership condition for the final visit; for an actual transcript, absence of
an omitted final crossing is proved separately. -/
inductive TimedAlphaVisitScheduleFinish
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (cursor : TimedAlphaVisitCursor State T b)
    (visitsSoFar : List (TimedAlphaScheduledVisit State T b)) :
    List (TimedAlphaScheduledVisit State T b) → Prop
  | atTerminal
      (htime : cursor.time.val = T)
      (hendpoint : cursor.endpoint = alpha.terminal) :
      TimedAlphaVisitScheduleFinish alpha cursor visitsSoFar visitsSoFar
  | finalVisit
      (htime : cursor.time.val < T)
      (hterminalHead : WorkCellInSlab
        (advertisedBlockLower alpha.offsets cursor.block)
        (advertisedBlockWidth alpha.offsets cursor.block)
        alpha.terminal.workHead.val) :
      TimedAlphaVisitScheduleFinish alpha cursor visitsSoFar
        (visitsSoFar ++ [timedAlphaFinalScheduledVisit alpha cursor htime])

/-- Full advertised-only visit-schedule specification for one timed alpha. -/
def TimedAlphaVisitScheduleValid
    (machine : DeterministicMachine)
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b)) : Prop :=
  TimedAlphaWordSyntacticallyValid alpha ∧
    ∃ finalCursor visitsSoFar,
      TimedAlphaTokenVisitFold alpha
          (initialTimedAlphaVisitCursor machine T b)
          (decodePaddedWord (T / b) alpha.word) visitsSoFar finalCursor ∧
        TimedAlphaVisitScheduleFinish alpha finalCursor visitsSoFar visits ∧
        TimedAlphaScheduledVisitsChained visits

/-- Stable chronological sublist of visits advertised for one work block. -/
def timedAlphaScheduledVisitsForBlock
    {State : Type} {T b : Nat}
    (target : Fin (T / b + 1))
    (visits : List (TimedAlphaScheduledVisit State T b)) :
    List (TimedAlphaScheduledVisit State T b) :=
  visits.filter fun scheduled => scheduled.block = target

/-- Drop the repeated block label after stable filtering. -/
def timedAlphaBlockVisits
    {State : Type} {T b : Nat}
    (target : Fin (T / b + 1))
    (visits : List (TimedAlphaScheduledVisit State T b)) :
    List (FixedAlphaBlockVisit State T) :=
  (timedAlphaScheduledVisitsForBlock target visits).map
    TimedAlphaScheduledVisit.visit

/-- Global pairwise order relation strong enough to imply strict separation
whenever two visits carry the same block label. -/
def TimedAlphaScheduledVisitPrecedes
    {State : Type} {T b : Nat}
    (earlier later : TimedAlphaScheduledVisit State T b) : Prop :=
  earlier.visit.exitTime.val ≤ later.visit.entryTime.val ∧
    (earlier.block = later.block →
      earlier.visit.exitTime.val < later.visit.entryTime.val)

instance instIsTransTimedAlphaScheduledVisitPrecedes
    {State : Type} {T b : Nat} :
    IsTrans (TimedAlphaScheduledVisit State T b)
      TimedAlphaScheduledVisitPrecedes := by
  constructor
  intro first middle third hfirstMiddle hmiddleThird
  unfold TimedAlphaScheduledVisitPrecedes at hfirstMiddle hmiddleThird ⊢
  rcases hfirstMiddle with ⟨hfirstMiddle, _⟩
  rcases hmiddleThird with ⟨hmiddleThird, _⟩
  have hmiddlePositive :
      middle.visit.entryTime.val < middle.visit.exitTime.val := by
    exact middle.visit.entryTime_lt_exitTime
  constructor
  · omega
  · intro _
    omega

/-- One exact adjacent link implies the global precedence relation. -/
theorem timedAlphaScheduledVisitPrecedes_of_link
    {State : Type} {T b : Nat}
    {earlier later : TimedAlphaScheduledVisit State T b}
    (hlink : TimedAlphaScheduledVisitLink earlier later) :
    TimedAlphaScheduledVisitPrecedes earlier later := by
  rcases hlink with ⟨htime, _, hblock⟩
  constructor
  · rw [htime]
  · intro hsame
    exact False.elim (hblock hsame)

/-- Exact endpoint chaining implies pairwise global precedence. -/
theorem timedAlphaScheduledVisits_pairwise_precedes
    {State : Type} {T b : Nat}
    {visits : List (TimedAlphaScheduledVisit State T b)}
    (hchained : TimedAlphaScheduledVisitsChained visits) :
    visits.Pairwise TimedAlphaScheduledVisitPrecedes := by
  have hchain : visits.Chain' TimedAlphaScheduledVisitPrecedes := by
    induction visits with
    | nil => simp
    | cons head tail ih =>
        cases tail with
        | nil => simp
        | cons next rest =>
            unfold TimedAlphaScheduledVisitsChained at hchained
            rw [List.chain'_cons] at hchained
            rw [List.chain'_cons]
            exact ⟨timedAlphaScheduledVisitPrecedes_of_link hchained.1,
              ih hchained.2⟩
  exact List.chain'_iff_pairwise.mp hchain

/-- Erasing constant block labels from a pairwise-preceding list leaves
strictly ordered visit intervals. -/
theorem timedAlphaScheduledVisits_map_visit_pairwise_lt
    {State : Type} {T b : Nat}
    (target : Fin (T / b + 1))
    (selected : List (TimedAlphaScheduledVisit State T b))
    (hpairwise : selected.Pairwise TimedAlphaScheduledVisitPrecedes)
    (hselected : ∀ scheduled, scheduled ∈ selected →
      scheduled.block = target) :
    (selected.map TimedAlphaScheduledVisit.visit).Pairwise
        (fun earlier later =>
          earlier.exitTime.val < later.entryTime.val) := by
  revert hpairwise hselected
  induction selected with
  | nil => simp
  | cons head tail ih =>
      intro hpairwise hselected
      rw [List.pairwise_cons] at hpairwise
      simp only [List.map_cons, List.pairwise_cons]
      constructor
      · intro later hlater
        obtain ⟨scheduled, hscheduled, rfl⟩ := List.mem_map.mp hlater
        have hprecedes := hpairwise.1 scheduled hscheduled
        exact hprecedes.2
          ((hselected head (by simp)).trans
            (hselected scheduled (by simp [hscheduled])).symm)
      · apply ih hpairwise.2
        intro scheduled hscheduled
        exact hselected scheduled (by simp [hscheduled])

/-- A same-block sublist of a pairwise-preceding schedule has strictly ordered
visit intervals after erasing its repeated block labels. -/
theorem timedAlphaBlockVisits_chronological_of_chained
    {State : Type} {T b : Nat}
    (target : Fin (T / b + 1))
    (visits : List (TimedAlphaScheduledVisit State T b))
    (hchained : TimedAlphaScheduledVisitsChained visits) :
    FixedAlphaBlockVisitsChronological
      (timedAlphaBlockVisits target visits) := by
  let selected := timedAlphaScheduledVisitsForBlock target visits
  have hpairwise : selected.Pairwise TimedAlphaScheduledVisitPrecedes := by
    exact (timedAlphaScheduledVisits_pairwise_precedes hchained).filter _
  have hselected : ∀ scheduled, scheduled ∈ selected →
      scheduled.block = target := by
    intro scheduled hscheduled
    exact of_decide_eq_true (List.mem_filter.mp hscheduled).2
  exact timedAlphaScheduledVisits_map_visit_pairwise_lt
    target selected hpairwise hselected

/-- Every valid advertised schedule supplies strict per-block visit lists. -/
theorem TimedAlphaVisitScheduleValid.blockVisitsChronological
    (machine : DeterministicMachine)
    {T b : Nat}
    {alpha : AmbientTimedCanonicalAlpha machine.State T b}
    {visits : List (TimedAlphaScheduledVisit machine.State T b)}
    (hvalid : TimedAlphaVisitScheduleValid machine alpha visits)
    (target : Fin (T / b + 1)) :
    FixedAlphaBlockVisitsChronological
      (timedAlphaBlockVisits target visits) := by
  obtain ⟨_, finalCursor, visitsSoFar, _, _, hchained⟩ := hvalid
  exact timedAlphaBlockVisits_chronological_of_chained
    target visits hchained

end OneTapeMagnification
end Frontier
end Pnp4
