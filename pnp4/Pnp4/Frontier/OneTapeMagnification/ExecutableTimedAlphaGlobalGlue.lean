import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.ExecutableTimedAlphaVisitChecker
import Pnp4.Frontier.OneTapeMagnification.ArbitraryAlphaGlobalGlue

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Executable arbitrary-alpha global glue

The combined Boolean checker reflects schedule validity and simultaneous
blank-start local replay.  `ArbitraryAlphaGlobalGlue` proves that exactly
those relational premises glue to the unique blank-start deterministic run.
This file records the direct executable consequences.

Cut minimality is deliberately not part of this checker yet.  Consequently
the theorem certifies computation soundness of an arbitrary accepted alpha,
not equality with the separately defined leftmost-minimum canonical cut word.
-/

/-- Every visit accepted by the executable checker is realized, in order, by
one blank-start global deterministic run. -/
theorem timedAlphaVisitScheduleAllBlockVisitsCheck_matchesGlobalRun
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hcheck : timedAlphaVisitScheduleAllBlockVisitsCheck
      machine input alpha scheduled = true) :
    TimedAlphaScheduledVisitsMatchGlobalRunFrom machine input
      (initialConfiguration machine) scheduled := by
  have hrel :=
    (timedAlphaVisitScheduleAllBlockVisitsCheck_eq_true_iff
      machine input alpha scheduled).1 hcheck
  exact timedAlphaVisitScheduleValid_allBlockVisitsAccepted_matchesGlobalRun
    machine input alpha scheduled hrel.1 hrel.2

/-- **Executable arbitrary-alpha computation soundness.**

If the Boolean schedule/all-block checker accepts, the advertised terminal
endpoint is exactly the endpoint of the actual deterministic run at time
`T`.  There is no reachability or global-glue hypothesis in the statement. -/
theorem timedAlphaVisitScheduleAllBlockVisitsCheck_globalGlue
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (input : List Bool) {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha machine.State T b)
    (scheduled : List (TimedAlphaScheduledVisit machine.State T b))
    (hcheck : timedAlphaVisitScheduleAllBlockVisitsCheck
      machine input alpha scheduled = true) :
    alpha.terminal = boundedTerminalEndpointAtRun machine input T := by
  have hrel :=
    (timedAlphaVisitScheduleAllBlockVisitsCheck_eq_true_iff
      machine input alpha scheduled).1 hcheck
  exact timedAlphaVisitScheduleValid_allBlockVisitsAccepted_globalGlue
    machine input alpha scheduled hrel.1 hrel.2

end OneTapeMagnification
end Frontier
end Pnp4
