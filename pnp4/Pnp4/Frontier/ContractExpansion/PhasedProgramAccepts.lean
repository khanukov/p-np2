import Complexity.TMVerifier.TuringToolkit.Foundation

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM

/-!
# `accepts` for a compiled phased program

NP-verifier track (toward the `accepts ↔ treePrefixSemanticAccepts` bridge, audit §9).

The verifier TM is `(verifierProgram).toPhased.toTM` for some phased program.  Its acceptance is, by
definition of `TM.accepts` / `TM.run` and the transparent `toTM` fields, exactly: "after running the
declared `timeBound` steps from the initial configuration, the control state is the accept
phase/state".  This unfolding is the shape against which the verifier's correctness bridge reasons.
-/

/-- Acceptance of a compiled `PhasedProgram`, unfolded to its terminal control state. -/
theorem PhasedProgram.accepts_toTM (P : PhasedProgram) {L : Nat} (x : Boolcube.Point L) :
    TM.accepts (M := P.toTM) (n := L) x
      = decide ((TM.runConfig (M := P.toTM) ((P.toTM).initialConfig x) (P.timeBound L)).state
          = (⟨P.acceptPhase, P.acceptState⟩ : Σ i, P.phaseState i)) := rfl

end TM
end PsubsetPpoly
end Internal
end Pnp3
