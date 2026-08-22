import Complexity.TMVerifier.TuringToolkit.ConstStatePhasedProgramSeqRun

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM
namespace ConstStatePhasedProgram

open Pnp3.Internal.PsubsetPpoly.TM

universe v

variable {S : Type v} [Fintype S] [DecidableEq S]

/-!
## Acceptance from a `RunSpec`

`RunSpec.reachesAcceptPhase` identifies only the phase component of the
final control state.  The compiled TM accepts only when the entire dependent
state is its designated accept state.  These lemmas isolate the remaining
local-state equality instead of silently conflating the two conditions.
-/

/-- Once a `RunSpec` has supplied the final phase equality, full accepting
state equality is equivalent to equality of the final local state. -/
theorem RunSpec.final_state_eq_accept_iff
    {P : ConstStatePhasedProgram S} {n : Nat}
    {c : Configuration (M := P.toPhased.toTM) n}
    {Post : Configuration (M := P.toPhased.toTM) n → Prop}
    (spec : RunSpec P c Post) :
    let cf := TM.runConfig (M := P.toPhased.toTM) c (P.timeBound n)
    cf.state = P.toPhased.toTM.accept ↔
      cf.state.snd = P.acceptState := by
  dsimp only
  let cf := TM.runConfig (M := P.toPhased.toTM) c (P.timeBound n)
  constructor
  · intro h
    have hsnd := congrArg Sigma.snd h
    exact hsnd
  · intro hsnd
    have hfst : cf.state.fst = P.acceptPhase :=
      Fin.ext spec.reachesAcceptPhase
    exact Sigma.ext hfst (by rw [hfst]; exact heq_of_eq hsnd)

/-- For a run from the machine's actual initial configuration, `TM.accepts`
is exactly the decision procedure for the final local-state equality. -/
theorem RunSpec.accepts_eq_decide_local
    {P : ConstStatePhasedProgram S} {n : Nat}
    {x : Boolcube.Point n}
    {Post : Configuration (M := P.toPhased.toTM) n → Prop}
    (spec : RunSpec P (P.toPhased.toTM.initialConfig x) Post) :
    TM.accepts (M := P.toPhased.toTM) n x =
      decide ((P.toPhased.toTM.run x).state.snd = P.acceptState) := by
  unfold TM.accepts TM.run
  exact decide_eq_decide.mpr spec.final_state_eq_accept_iff

end ConstStatePhasedProgram
end TM
end PsubsetPpoly
end Internal
end Pnp3
