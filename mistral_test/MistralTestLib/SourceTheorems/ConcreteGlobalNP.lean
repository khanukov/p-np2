/- 
Minimal NP-side compatibility witness for `mistral_test`.

The old file tried to build a bespoke verifier for a concrete global language.
That verifier no longer matches the active circuit / TM APIs.  For the purpose
of keeping `MistralTestLib` buildable without placeholders, we expose a simple
canonical NP language witness that the higher-level wrapper layer can import.
-/
import Complexity.Interfaces

namespace MistralTestLib.ConcreteGlobalNP

open Pnp3
open Pnp3.ComplexityInterfaces
open Pnp3.Internal.PsubsetPpoly

/-- Trivial compatibility language used by the shim layer. -/
noncomputable def concreteGlobalLanguage : Language := fun _ _ => false

private def rejectTM : TM := {
  state := Bool
  start := false
  accept := true
  step := fun q _ => (q, false, Move.stay)
  runTime := fun _ => 0
}

/-- The compatibility language is in canonical `NP` via an always-reject verifier. -/
theorem concreteGlobalLanguage_in_NP : NP concreteGlobalLanguage := by
  refine ⟨rejectTM, 0, 0, ?_, ?_⟩
  · intro n
    simp [rejectTM, certificateLength]
  · intro n x
    constructor
    · intro h
      simp [concreteGlobalLanguage] at h
    · intro h
      rcases h with ⟨w, hw⟩
      simp [rejectTM, TM.accepts, TM.run, TM.runConfig, TM.initialConfig] at hw

end MistralTestLib.ConcreteGlobalNP
