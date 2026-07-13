import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.ActualAllFixedAlphaBlockVisits

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Executable checker for a timed-alpha visit schedule

The advertised schedule specification is relational because it exposes the
intermediate cursor and token-emitted prefix.  Nevertheless, both objects are
uniquely computed from a fixed alpha.  This module makes that computation
explicit, reflects it exactly into `TimedAlphaVisitScheduleValid`, and combines
it with the already executable fixed-block replay checks for every block.

The final checker certifies exactly the existing advertised-side predicates.
It does not assert that an arbitrary accepted alpha was extracted from one
global run: that converse still needs cross-block/global-run glue beyond the
independent blank-start slab checks formalized here.
-/

/-- Decidable equality needed only to compare the computed schedule with the
supplied one.  The proof field in a visit is irrelevant by extensionality. -/
private instance instDecidableEqFixedAlphaBlockVisitForChecker
    {State : Type} [DecidableEq State] {T : Nat} :
    DecidableEq (FixedAlphaBlockVisit State T) := fun left right =>
  decidable_of_iff
    (left.entryTime = right.entryTime ∧
      left.exitTime = right.exitTime ∧
      left.entry = right.entry ∧
      left.exit = right.exit)
    (by
      constructor
      · rintro ⟨hentryTime, hexitTime, hentry, hexit⟩
        exact fixedAlphaBlockVisit_ext
          hentryTime hexitTime hentry hexit
      · intro heq
        subst right
        exact ⟨rfl, rfl, rfl, rfl⟩)

private instance instDecidableEqTimedAlphaScheduledVisitForChecker
    {State : Type} [DecidableEq State] {T b : Nat} :
    DecidableEq (TimedAlphaScheduledVisit State T b) := fun left right =>
  decidable_of_iff
    (left.block = right.block ∧ left.visit = right.visit)
    (by
      constructor
      · rintro ⟨hblock, hvisit⟩
        exact timedAlphaScheduledVisit_ext hblock hvisit
      · intro heq
        subst right
        exact ⟨rfl, rfl⟩)

/-- Deterministically execute the token-to-visit fold.  `none` is returned at
the first bad time order or source-block link. -/
def executeTimedAlphaTokenVisitFold
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b) :
    TimedAlphaVisitCursor State T b →
      List (TimedCanonicalCrossingToken State T b) →
      Option
        (List (TimedAlphaScheduledVisit State T b) ×
          TimedAlphaVisitCursor State T b)
  | cursor, [] => some ([], cursor)
  | cursor, crossing :: rest =>
      if htime : cursor.time.val ≤ crossing.sourceTime.val then
        if _hsource : cursor.block =
            advertisedTimedCrossingSourceBlock crossing then
          match executeTimedAlphaTokenVisitFold alpha
              (timedAlphaVisitCursorAfterCrossing alpha crossing) rest with
          | none => none
          | some (visits, finalCursor) =>
              some
                (timedAlphaScheduledVisitAtCrossing
                    alpha cursor crossing htime :: visits,
                  finalCursor)
        else
          none
      else
        none

/-- The executor succeeds with exactly the witnesses of the relational token
fold. -/
theorem executeTimedAlphaTokenVisitFold_eq_some_iff
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (cursor : TimedAlphaVisitCursor State T b)
    (tokens : List (TimedCanonicalCrossingToken State T b))
    (visits : List (TimedAlphaScheduledVisit State T b))
    (finalCursor : TimedAlphaVisitCursor State T b) :
    executeTimedAlphaTokenVisitFold alpha cursor tokens =
        some (visits, finalCursor) ↔
      TimedAlphaTokenVisitFold alpha cursor tokens visits finalCursor := by
  induction tokens generalizing cursor visits finalCursor with
  | nil =>
      constructor
      · intro hexec
        simp only [executeTimedAlphaTokenVisitFold, Option.some.injEq,
          Prod.mk.injEq] at hexec
        rcases hexec with ⟨rfl, rfl⟩
        exact TimedAlphaTokenVisitFold.nil cursor
      · intro hfold
        cases hfold
        rfl
  | cons crossing rest ih =>
      by_cases htime : cursor.time.val ≤ crossing.sourceTime.val
      · by_cases hsource : cursor.block =
          advertisedTimedCrossingSourceBlock crossing
        · cases htailExec : executeTimedAlphaTokenVisitFold alpha
            (timedAlphaVisitCursorAfterCrossing alpha crossing) rest with
          | none =>
              constructor
              · simp [executeTimedAlphaTokenVisitFold, htime, hsource,
                  htailExec]
              · intro hfold
                cases hfold with
                | cons cursor crossing rest tailVisits tailCursor
                    htime' hsource' htail =>
                    have htailSome := (ih _ _ _).2 htail
                    rw [htailExec] at htailSome
                    contradiction
          | some result =>
              rcases result with ⟨tailVisits, tailCursor⟩
              constructor
              · intro hexec
                simp only [executeTimedAlphaTokenVisitFold, htime,
                  hsource, ↓reduceDIte, htailExec, Option.some.injEq,
                  Prod.mk.injEq] at hexec
                rcases hexec with ⟨hvisits, hcursor⟩
                subst visits
                subst finalCursor
                exact TimedAlphaTokenVisitFold.cons cursor crossing rest
                  tailVisits tailCursor htime hsource
                  ((ih _ _ _).1 htailExec)
              · intro hfold
                cases hfold with
                | cons cursor crossing rest visits finalCursor
                    htime' hsource' htail =>
                    have htailExec' :
                        executeTimedAlphaTokenVisitFold alpha
                            (timedAlphaVisitCursorAfterCrossing alpha crossing)
                            rest = some (visits, finalCursor) :=
                      (ih _ _ _).2 htail
                    rw [htailExec] at htailExec'
                    have hpair : (tailVisits, tailCursor) =
                        (visits, finalCursor) :=
                      Option.some.inj htailExec'
                    have hvisits : tailVisits = visits :=
                      congrArg Prod.fst hpair
                    have hcursor : tailCursor = finalCursor :=
                      congrArg Prod.snd hpair
                    subst visits
                    subst finalCursor
                    simp [executeTimedAlphaTokenVisitFold, htime, hsource,
                      htailExec]
        · constructor
          · simp [executeTimedAlphaTokenVisitFold, htime, hsource]
          · intro hfold
            cases hfold with
            | cons cursor crossing rest visits finalCursor
                htime' hsource' htail =>
                exact False.elim (hsource hsource')
      · constructor
        · simp [executeTimedAlphaTokenVisitFold, htime]
        · intro hfold
          cases hfold with
          | cons cursor crossing rest visits finalCursor
              htime' hsource' htail =>
              exact False.elim (htime htime')

/-- Complete the deterministic token fold using the exact terminal convention
of `TimedAlphaVisitScheduleFinish`. -/
def finishTimedAlphaVisitSchedule
    {State : Type} [DecidableEq State] {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (visitsSoFar : List (TimedAlphaScheduledVisit State T b))
    (cursor : TimedAlphaVisitCursor State T b) :
    Option (List (TimedAlphaScheduledVisit State T b)) :=
  if htime : cursor.time.val = T then
    if cursor.endpoint = alpha.terminal then
      some visitsSoFar
    else
      none
  else
    have hlt : cursor.time.val < T := by omega
    if WorkCellInSlab
        (advertisedBlockLower alpha.offsets cursor.block)
        (advertisedBlockWidth alpha.offsets cursor.block)
        alpha.terminal.workHead.val then
      some (visitsSoFar ++
        [timedAlphaFinalScheduledVisit alpha cursor hlt])
    else
      none

/-- Terminal execution reflects exactly the relational finish predicate. -/
theorem finishTimedAlphaVisitSchedule_eq_some_iff
    {State : Type} [DecidableEq State] {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (visitsSoFar visits : List (TimedAlphaScheduledVisit State T b))
    (cursor : TimedAlphaVisitCursor State T b) :
    finishTimedAlphaVisitSchedule alpha visitsSoFar cursor = some visits ↔
      TimedAlphaVisitScheduleFinish alpha cursor visitsSoFar visits := by
  by_cases htime : cursor.time.val = T
  · by_cases hendpoint : cursor.endpoint = alpha.terminal
    · constructor
      · intro hexec
        simp [finishTimedAlphaVisitSchedule, htime, hendpoint] at hexec
        subst visits
        exact TimedAlphaVisitScheduleFinish.atTerminal htime hendpoint
      · intro hfinish
        cases hfinish with
        | atTerminal htime' hendpoint' =>
            simp [finishTimedAlphaVisitSchedule, htime, hendpoint]
        | finalVisit htime' hterminalHead => omega
    · constructor
      · simp [finishTimedAlphaVisitSchedule, htime, hendpoint]
      · intro hfinish
        cases hfinish with
        | atTerminal htime' hendpoint' =>
            exact False.elim (hendpoint hendpoint')
        | finalVisit htime' hterminalHead => omega
  · have hlt : cursor.time.val < T := by omega
    by_cases hterminalHead : WorkCellInSlab
        (advertisedBlockLower alpha.offsets cursor.block)
        (advertisedBlockWidth alpha.offsets cursor.block)
        alpha.terminal.workHead.val
    · constructor
      · intro hexec
        simp [finishTimedAlphaVisitSchedule, htime, hterminalHead] at hexec
        subst visits
        exact TimedAlphaVisitScheduleFinish.finalVisit hlt hterminalHead
      · intro hfinish
        cases hfinish with
        | atTerminal htime' hendpoint' =>
            exact False.elim (htime htime')
        | finalVisit htime' hterminalHead' =>
            simp [finishTimedAlphaVisitSchedule, htime, hterminalHead]
    · constructor
      · simp [finishTimedAlphaVisitSchedule, htime, hterminalHead]
      · intro hfinish
        cases hfinish with
        | atTerminal htime' hendpoint' =>
            exact False.elim (htime htime')
        | finalVisit htime' hterminalHead' =>
            exact False.elim (hterminalHead hterminalHead')

/-- Canonical advertised schedule computed from one fixed timed alpha. -/
def buildTimedAlphaVisitSchedule
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b) :
    Option (List (TimedAlphaScheduledVisit machine.State T b)) :=
  match executeTimedAlphaTokenVisitFold alpha
      (initialTimedAlphaVisitCursor machine T b)
      (decodePaddedWord (T / b) alpha.word) with
  | none => none
  | some (visitsSoFar, finalCursor) =>
      finishTimedAlphaVisitSchedule alpha visitsSoFar finalCursor

/-- Builder success is exactly the fold-and-finish witness pair hidden inside
the public schedule relation. -/
theorem buildTimedAlphaVisitSchedule_eq_some_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b)) :
    buildTimedAlphaVisitSchedule machine alpha = some visits ↔
      ∃ finalCursor visitsSoFar,
        TimedAlphaTokenVisitFold alpha
            (initialTimedAlphaVisitCursor machine T b)
            (decodePaddedWord (T / b) alpha.word)
            visitsSoFar finalCursor ∧
          TimedAlphaVisitScheduleFinish alpha finalCursor
            visitsSoFar visits := by
  unfold buildTimedAlphaVisitSchedule
  cases hfoldExec : executeTimedAlphaTokenVisitFold alpha
      (initialTimedAlphaVisitCursor machine T b)
      (decodePaddedWord (T / b) alpha.word) with
  | none =>
      constructor
      · simp
      · rintro ⟨finalCursor, visitsSoFar, hfold, hfinish⟩
        have := (executeTimedAlphaTokenVisitFold_eq_some_iff
          alpha (initialTimedAlphaVisitCursor machine T b)
          (decodePaddedWord (T / b) alpha.word)
          visitsSoFar finalCursor).2 hfold
        rw [hfoldExec] at this
        contradiction
  | some result =>
      rcases result with ⟨visitsSoFar, finalCursor⟩
      change finishTimedAlphaVisitSchedule alpha visitsSoFar finalCursor =
          some visits ↔ _
      constructor
      · intro hfinishExec
        exact ⟨finalCursor, visitsSoFar,
          (executeTimedAlphaTokenVisitFold_eq_some_iff
            alpha (initialTimedAlphaVisitCursor machine T b)
            (decodePaddedWord (T / b) alpha.word)
            visitsSoFar finalCursor).1 hfoldExec,
          (finishTimedAlphaVisitSchedule_eq_some_iff
            alpha visitsSoFar visits finalCursor).1 hfinishExec⟩
      · rintro ⟨otherCursor, otherPrefix, hfold, hfinish⟩
        have hotherExec := (executeTimedAlphaTokenVisitFold_eq_some_iff
          alpha (initialTimedAlphaVisitCursor machine T b)
          (decodePaddedWord (T / b) alpha.word)
          otherPrefix otherCursor).2 hfold
        rw [hfoldExec] at hotherExec
        have hpair : (visitsSoFar, finalCursor) =
            (otherPrefix, otherCursor) :=
          Option.some.inj hotherExec
        have hprefix : visitsSoFar = otherPrefix :=
          congrArg Prod.fst hpair
        have hcursor : finalCursor = otherCursor :=
          congrArg Prod.snd hpair
        subst otherPrefix
        subst otherCursor
        exact (finishTimedAlphaVisitSchedule_eq_some_iff
          alpha visitsSoFar visits finalCursor).2 hfinish

/-- Boolean schedule checker: syntactic word validity plus equality with the
unique schedule computed by the advertised fold and finish. -/
def timedAlphaVisitScheduleCheck
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b)) : Bool :=
  timedAlphaWordSyntacticCheck alpha &&
    decide (buildTimedAlphaVisitSchedule machine alpha = some visits)

/-- Exact reflection of the full public advertised schedule predicate.  The
apparently additional chaining clause follows from fold plus finish. -/
theorem timedAlphaVisitScheduleCheck_eq_true_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (visits : List (TimedAlphaScheduledVisit machine.State T b)) :
    timedAlphaVisitScheduleCheck machine alpha visits = true ↔
      TimedAlphaVisitScheduleValid machine alpha visits := by
  constructor
  · intro hcheck
    rw [timedAlphaVisitScheduleCheck, Bool.and_eq_true] at hcheck
    have hword :=
      (timedAlphaWordSyntacticCheck_eq_true_iff alpha).1 hcheck.1
    have hbuild : buildTimedAlphaVisitSchedule machine alpha = some visits :=
      of_decide_eq_true hcheck.2
    obtain ⟨finalCursor, visitsSoFar, hfold, hfinish⟩ :=
      (buildTimedAlphaVisitSchedule_eq_some_iff
        machine alpha visits).1 hbuild
    exact ⟨hword, finalCursor, visitsSoFar, hfold, hfinish,
      timedAlphaTokenVisitFold_finish_chained hfold hfinish⟩
  · rintro ⟨hword, finalCursor, visitsSoFar, hfold, hfinish, hchained⟩
    rw [timedAlphaVisitScheduleCheck, Bool.and_eq_true]
    constructor
    · exact (timedAlphaWordSyntacticCheck_eq_true_iff alpha).2 hword
    · apply decide_eq_true
      exact (buildTimedAlphaVisitSchedule_eq_some_iff
        machine alpha visits).2
          ⟨finalCursor, visitsSoFar, hfold, hfinish⟩

/-- Execute every fixed-block validator on the stable per-block sublists of
one supplied schedule, always from the literal blank slab. -/
def timedAlphaAllBlockVisitsCheckFromBlank
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b)) : Bool :=
  decide (∀ target : Fin (T / b + 1),
    fixedAlphaBlockVisitListCheck machine input alpha target
      (blankWorkSlab (advertisedBlockWidth alpha.offsets target))
      (timedAlphaBlockVisits target scheduled) = true)

/-- Exact finite reflection of simultaneous fixed-block list acceptance. -/
theorem timedAlphaAllBlockVisitsCheckFromBlank_eq_true_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b)) :
    timedAlphaAllBlockVisitsCheckFromBlank
        machine input alpha scheduled = true ↔
      ∀ target : Fin (T / b + 1),
        FixedAlphaBlockVisitListAcceptedFromBlank
          machine input alpha target
          (timedAlphaBlockVisits target scheduled) := by
  rw [timedAlphaAllBlockVisitsCheckFromBlank]
  simp only [decide_eq_true_eq]
  constructor
  · intro hall target
    unfold FixedAlphaBlockVisitListAcceptedFromBlank
    exact (fixedAlphaBlockVisitListCheck_eq_true_iff
      machine input alpha target
      (blankWorkSlab (advertisedBlockWidth alpha.offsets target))
      (timedAlphaBlockVisits target scheduled)).1 (hall target)
  · intro hall target
    apply (fixedAlphaBlockVisitListCheck_eq_true_iff
      machine input alpha target
      (blankWorkSlab (advertisedBlockWidth alpha.offsets target))
      (timedAlphaBlockVisits target scheduled)).2
    exact hall target

/-- One executable Boolean checkpoint for the fixed alpha, its complete
schedule, and all stable per-block replay lists. -/
def timedAlphaVisitScheduleAllBlockVisitsCheck
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b)) : Bool :=
  timedAlphaVisitScheduleCheck machine alpha scheduled &&
    timedAlphaAllBlockVisitsCheckFromBlank
      machine input alpha scheduled

/-- The combined Boolean checkpoint is equivalent to exactly the two existing
relational layers, with no hidden reachability or glue hypothesis. -/
theorem timedAlphaVisitScheduleAllBlockVisitsCheck_eq_true_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b)) :
    timedAlphaVisitScheduleAllBlockVisitsCheck
        machine input alpha scheduled = true ↔
      TimedAlphaVisitScheduleValid machine alpha scheduled ∧
        ∀ target : Fin (T / b + 1),
          FixedAlphaBlockVisitListAcceptedFromBlank
            machine input alpha target
            (timedAlphaBlockVisits target scheduled) := by
  simp [timedAlphaVisitScheduleAllBlockVisitsCheck,
    timedAlphaVisitScheduleCheck_eq_true_iff,
    timedAlphaAllBlockVisitsCheckFromBlank_eq_true_iff]

/-- The actual extracted alpha has one common schedule accepted by the fully
executable checker; the same witness retains the exact all-group scan and the
proved final slab for every block. -/
theorem exists_actualTimedAlphaVisitScheduleAllBlockVisitsCheck_eq_true
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b) :
    ∃ scheduled : List (TimedAlphaScheduledVisit machine.State T b),
      timedAlphaVisitScheduleAllBlockVisitsCheck machine input
          (chronologicalTimedCanonicalAlpha machine input T b hb)
          scheduled = true ∧
        ActualTimedAlphaScheduledVisitsFromGroups
          machine input T b hb []
          (actualCanonicalWorkBlockRuns machine input T b hb) scheduled ∧
        ∀ target : Fin (T / b + 1),
          replayFixedAlphaBlockVisits machine input
              (chronologicalTimedCanonicalAlpha machine input T b hb) target
              (blankWorkSlab
                (advertisedBlockWidth
                  (chronologicalTimedCanonicalAlpha
                    machine input T b hb).offsets target))
              (timedAlphaBlockVisits target scheduled) =
            actualFixedAlphaBlockSlabAtTime
              machine input T b hb target T := by
  obtain ⟨scheduled, hschedule, hgroups, hall⟩ :=
    exists_actualTimedAlphaVisitScheduleValid_allBlockVisitsAccepted
      machine input T b hb
  refine ⟨scheduled, ?_, hgroups, ?_⟩
  · apply (timedAlphaVisitScheduleAllBlockVisitsCheck_eq_true_iff
      machine input
      (chronologicalTimedCanonicalAlpha machine input T b hb)
      scheduled).2
    exact ⟨hschedule, fun target => (hall target).1⟩
  · intro target
    exact (hall target).2

end OneTapeMagnification
end Frontier
end Pnp4
