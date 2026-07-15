import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.ExactMasterGuardedCanonicalComponent

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Rejecting-guarded canonical aggregate endpoint

The strict total fixed-`(alpha, schedule)` compiler has an absorbing reject
sink and is extensionally equal to the executable in-place canonical-cut
check.  Consequently its accepting certificate no longer needs external
schedule-validity or replay fields: both are recovered from the compiled
program's own acceptance.

The existential aggregate is exactly cached bounded acceptance.  In fact its
certificate is unambiguous as the full pair `(alpha, schedule)`, since the
canonical alpha is forced by the rolling cut check and the advertised
schedule is the output of a deterministic builder.

Under the repository route policy this remains a restricted lower-bound side
track.  It supplies an exact read-once representation of each fixed component
but does not construct the missing aggregate-class PRG/HSG or reduce
`SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`.
-/

local instance cachedInputMachineStateDecidableEqForRejectingAggregate
    (machine : DeterministicMachine) [DecidableEq machine.State] :
    DecidableEq (cachedInputMachine machine).State :=
  cachedInputStateDecidableEq machine

/-! ## Exact strict certificates -/

/-- The minimal strict accepting certificate for one fixed alpha and
advertised schedule.  Acceptance of the total rejecting compiler internally
certifies schedule validity, every blank-slab replay, and the canonical cut;
only the accepting terminal state remains as the semantic acceptance gate. -/
def RejectingMasterGuardedFusedAcceptingComponentCertificate
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b)) : Prop :=
  (compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
      (n := input.length) machine alpha scheduled).eval
        (fun index => input.get index) = true /\
    (cachedInputMachine machine).halt alpha.terminal.state = some .accept

/-- The certificate's compiled part is exactly the executable in-place
canonical schedule checkpoint; there is no residual replay or
follows-master premise. -/
theorem rejectingMasterGuardedFusedAcceptingComponentCertificate_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b)) :
    RejectingMasterGuardedFusedAcceptingComponentCertificate
        machine input alpha scheduled <->
      timedAlphaVisitScheduleInPlaceCanonicalCutCheck
          (cachedInputMachine machine) input alpha scheduled = true /\
        (cachedInputMachine machine).halt alpha.terminal.state =
          some .accept := by
  unfold RejectingMasterGuardedFusedAcceptingComponentCertificate
  rw [compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_eval_eq_inPlaceCanonicalCutCheck]

/-- Strict compiler acceptance forces the advertised alpha to be the unique
chronological canonical alpha. -/
theorem rejectingMasterGuardedFusedAcceptingComponentCertificate_alpha_eq
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    (scheduled : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b))
    (hcertificate : RejectingMasterGuardedFusedAcceptingComponentCertificate
      machine input alpha scheduled) :
    alpha = chronologicalTimedCanonicalAlpha
      (cachedInputMachine machine) input T b hb := by
  have hcheck : timedAlphaVisitScheduleInPlaceCanonicalCutCheck
      (cachedInputMachine machine) input alpha scheduled = true :=
    (rejectingMasterGuardedFusedAcceptingComponentCertificate_iff
      machine input alpha scheduled).1 hcertificate |>.1
  have hreplayed : timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck
      (cachedInputMachine machine) input alpha scheduled = true :=
    (timedAlphaVisitScheduleInPlaceCanonicalCutCheck_iff_replayed
      (cachedInputMachine machine) input T b hb alpha scheduled).1 hcheck
  exact
    timedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck_eq_chronologicalAlpha
      (cachedInputMachine machine) input T b hb alpha scheduled hreplayed

/-- The strict rejecting certificate exists exactly when the cached machine
accepts at the fixed horizon. -/
theorem exists_rejectingMasterGuardedFusedAcceptingComponentCertificate_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b) :
    (exists alpha : AmbientTimedCanonicalAlpha
        (cachedInputMachine machine).State T b,
      exists scheduled : List (TimedAlphaScheduledVisit
        (cachedInputMachine machine).State T b),
        RejectingMasterGuardedFusedAcceptingComponentCertificate
          machine input alpha scheduled) <->
      IsAccepting (cachedInputMachine machine)
        (run (cachedInputMachine machine) input T) := by
  constructor
  . rintro ⟨alpha, scheduled, hcertificate⟩
    have halpha :=
      rejectingMasterGuardedFusedAcceptingComponentCertificate_alpha_eq
        machine input T b hb alpha scheduled hcertificate
    have hterminal := hcertificate.2
    subst alpha
    simpa [IsAccepting, outcome, chronologicalTimedCanonicalAlpha] using
      hterminal
  . intro haccept
    let cached := cachedInputMachine machine
    let alpha : AmbientTimedCanonicalAlpha cached.State T b :=
      chronologicalTimedCanonicalAlpha cached input T b hb
    obtain ⟨scheduled, hreplayed⟩ :=
      exists_actualTimedAlphaVisitScheduleAllBlockVisitsCanonicalCutCheck_eq_true
        cached input T b hb
    have hinPlace : timedAlphaVisitScheduleInPlaceCanonicalCutCheck
        cached input alpha scheduled = true :=
      (timedAlphaVisitScheduleInPlaceCanonicalCutCheck_iff_replayed
        cached input T b hb alpha scheduled).2 (by
          simpa [alpha] using hreplayed)
    have heval :
        (compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal
          (n := input.length) machine alpha scheduled).eval
            (fun index => input.get index) = true := by
      rw [compileRejectingMasterGuardedFiniteCachedTimedAlphaScheduleAllBlocksInPlaceRollingTotal_eval_eq_inPlaceCanonicalCutCheck]
      exact hinPlace
    have hterminal : cached.halt alpha.terminal.state = some .accept := by
      simpa [cached, alpha, IsAccepting, outcome,
        chronologicalTimedCanonicalAlpha] using haccept
    exact ⟨alpha, scheduled, heval, hterminal⟩

/-! ## Aggregate identity and exact unambiguity -/

/-- The existing semantic canonical aggregate is exactly the existential
union of strict rejecting-compiler certificates. -/
theorem cachedTimedAlphaInPlaceAcceptingAggregateCheck_eq_true_iff_rejectingGuardedFused
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b) :
    timedAlphaInPlaceAcceptingAggregateCheck
        (cachedInputMachine machine) input T b hb = true <->
      exists alpha : AmbientTimedCanonicalAlpha
          (cachedInputMachine machine).State T b,
        exists scheduled : List (TimedAlphaScheduledVisit
          (cachedInputMachine machine).State T b),
          RejectingMasterGuardedFusedAcceptingComponentCertificate
            machine input alpha scheduled := by
  rw [timedAlphaInPlaceAcceptingAggregateCheck_eq_true_iff]
  exact
    (exists_rejectingMasterGuardedFusedAcceptingComponentCertificate_iff
      machine input T b hb).symm

/-- Any two accepted strict certificates have the same canonical alpha. -/
theorem rejectingMasterGuardedFusedAcceptingComponentCertificate_alpha_unique
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    {left right : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b}
    {leftSchedule rightSchedule : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b)}
    (hleft : RejectingMasterGuardedFusedAcceptingComponentCertificate
      machine input left leftSchedule)
    (hright : RejectingMasterGuardedFusedAcceptingComponentCertificate
      machine input right rightSchedule) :
    left = right := by
  rw [rejectingMasterGuardedFusedAcceptingComponentCertificate_alpha_eq
      machine input T b hb left leftSchedule hleft,
    rejectingMasterGuardedFusedAcceptingComponentCertificate_alpha_eq
      machine input T b hb right rightSchedule hright]

/-- For a fixed alpha, two accepted strict certificates also have the same
advertised schedule: the schedule checker equates both lists with the output
of the deterministic schedule builder. -/
theorem rejectingMasterGuardedFusedAcceptingComponentCertificate_schedule_unique
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b)
    {leftSchedule rightSchedule : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b)}
    (hleft : RejectingMasterGuardedFusedAcceptingComponentCertificate
      machine input alpha leftSchedule)
    (hright : RejectingMasterGuardedFusedAcceptingComponentCertificate
      machine input alpha rightSchedule) :
    leftSchedule = rightSchedule := by
  have hleftCheck : timedAlphaVisitScheduleInPlaceCanonicalCutCheck
      (cachedInputMachine machine) input alpha leftSchedule = true :=
    (rejectingMasterGuardedFusedAcceptingComponentCertificate_iff
      machine input alpha leftSchedule).1 hleft |>.1
  have hrightCheck : timedAlphaVisitScheduleInPlaceCanonicalCutCheck
      (cachedInputMachine machine) input alpha rightSchedule = true :=
    (rejectingMasterGuardedFusedAcceptingComponentCertificate_iff
      machine input alpha rightSchedule).1 hright |>.1
  have hleftBase : timedAlphaVisitScheduleAllBlockVisitsCheck
      (cachedInputMachine machine) input alpha leftSchedule = true := by
    rw [timedAlphaVisitScheduleInPlaceCanonicalCutCheck,
      Bool.and_eq_true] at hleftCheck
    exact hleftCheck.1
  have hrightBase : timedAlphaVisitScheduleAllBlockVisitsCheck
      (cachedInputMachine machine) input alpha rightSchedule = true := by
    rw [timedAlphaVisitScheduleInPlaceCanonicalCutCheck,
      Bool.and_eq_true] at hrightCheck
    exact hrightCheck.1
  have hleftValid : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha leftSchedule :=
    ((timedAlphaVisitScheduleAllBlockVisitsCheck_eq_true_iff
      (cachedInputMachine machine) input alpha leftSchedule).1 hleftBase).1
  have hrightValid : TimedAlphaVisitScheduleValid
      (cachedInputMachine machine) alpha rightSchedule :=
    ((timedAlphaVisitScheduleAllBlockVisitsCheck_eq_true_iff
      (cachedInputMachine machine) input alpha rightSchedule).1 hrightBase).1
  rcases hleftValid with
    ⟨_hleftWord, leftCursor, leftPrefix, hleftFold, hleftFinish, _hleftChain⟩
  rcases hrightValid with
    ⟨_hrightWord, rightCursor, rightPrefix, hrightFold, hrightFinish,
      _hrightChain⟩
  have hleftBuild : buildTimedAlphaVisitSchedule
      (cachedInputMachine machine) alpha = some leftSchedule :=
    (buildTimedAlphaVisitSchedule_eq_some_iff
      (cachedInputMachine machine) alpha leftSchedule).2
        ⟨leftCursor, leftPrefix, hleftFold, hleftFinish⟩
  have hrightBuild : buildTimedAlphaVisitSchedule
      (cachedInputMachine machine) alpha = some rightSchedule :=
    (buildTimedAlphaVisitSchedule_eq_some_iff
      (cachedInputMachine machine) alpha rightSchedule).2
        ⟨rightCursor, rightPrefix, hrightFold, hrightFinish⟩
  exact Option.some.inj (hleftBuild.symm.trans hrightBuild)

/-- The entire accepted witness pair `(alpha, schedule)` is unique. -/
theorem rejectingMasterGuardedFusedAcceptingComponentCertificate_pair_unique
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    {left right : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b}
    {leftSchedule rightSchedule : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b)}
    (hleft : RejectingMasterGuardedFusedAcceptingComponentCertificate
      machine input left leftSchedule)
    (hright : RejectingMasterGuardedFusedAcceptingComponentCertificate
      machine input right rightSchedule) :
    left = right /\ leftSchedule = rightSchedule := by
  have halpha : left = right :=
    rejectingMasterGuardedFusedAcceptingComponentCertificate_alpha_unique
      machine input T b hb hleft hright
  subst right
  exact ⟨rfl,
    rejectingMasterGuardedFusedAcceptingComponentCertificate_schedule_unique
      machine input left hleft hright⟩

/-- Distinct alpha-indexed strict component fibers are disjoint pointwise. -/
theorem rejectingMasterGuardedFusedAcceptingComponentCertificates_disjoint
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b)
    {left right : AmbientTimedCanonicalAlpha
      (cachedInputMachine machine).State T b}
    {leftSchedule rightSchedule : List (TimedAlphaScheduledVisit
      (cachedInputMachine machine).State T b)}
    (hne : left ≠ right) :
    ¬ (RejectingMasterGuardedFusedAcceptingComponentCertificate
          machine input left leftSchedule /\
      RejectingMasterGuardedFusedAcceptingComponentCertificate
          machine input right rightSchedule) := by
  rintro ⟨hleft, hright⟩
  exact hne
    (rejectingMasterGuardedFusedAcceptingComponentCertificate_alpha_unique
      machine input T b hb hleft hright)

/-- Exact unambiguity of the strict aggregate: cached acceptance is
equivalent to existence of exactly one full `(alpha, schedule)` certificate. -/
theorem existsUnique_rejectingMasterGuardedFusedAcceptingComponentCertificate_iff
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) (T b : Nat) (hb : 0 < b) :
    (∃! witness :
        AmbientTimedCanonicalAlpha
            (cachedInputMachine machine).State T b ×
          List (TimedAlphaScheduledVisit
            (cachedInputMachine machine).State T b),
      RejectingMasterGuardedFusedAcceptingComponentCertificate
        machine input witness.1 witness.2) <->
      IsAccepting (cachedInputMachine machine)
        (run (cachedInputMachine machine) input T) := by
  constructor
  . rintro ⟨⟨alpha, scheduled⟩, hcertificate, _hunique⟩
    exact
      (exists_rejectingMasterGuardedFusedAcceptingComponentCertificate_iff
        machine input T b hb).1 ⟨alpha, scheduled, hcertificate⟩
  . intro haccept
    obtain ⟨alpha, scheduled, hcertificate⟩ :=
      (exists_rejectingMasterGuardedFusedAcceptingComponentCertificate_iff
        machine input T b hb).2 haccept
    refine ⟨⟨alpha, scheduled⟩, hcertificate, ?_⟩
    rintro ⟨otherAlpha, otherSchedule⟩ hother
    have hpair :=
      rejectingMasterGuardedFusedAcceptingComponentCertificate_pair_unique
        machine input T b hb hother hcertificate
    exact Prod.ext hpair.1 hpair.2

end OneTapeMagnification
end Frontier
end Pnp4
