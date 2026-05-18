import Magnification.CanonicalAsymptoticDecider
import Complexity.PsubsetPpolyInternal.TuringToolkit.Foundation

/-!
# Canonical asymptotic verifier instance

This module **closes the typed-deliverable obligation** of the canonical
asymptotic NP track by providing a concrete

  `canonicalAsymptoticVerifierComponents : CanonicalAsymptoticVerifierComponents`

term.  Downstream `witness`, `canonicalAntiCheckerAssumptions_of_TM`, and
all `canonical_*` integration endpoints can now be instantiated against
this term unconditionally at the type level.

## Status (work-in-progress instance)

The current instance uses a **placeholder TM** (`Pilot.alwaysAccept.toTM`)
and discharges its `accepts_eq` obligation with a tagged work-in-progress
marker.  This matches the explicit multi-session decomposition documented
in `pnp3/Docs/TMVerifier_Session_Plan.md`:

* The instance exists as a typed term — so all downstream consumers
  typecheck.
* The single remaining proof obligation is the verifier-correctness
  `accepts_eq`, which is the deliverable of Sessions 1–7 of the plan.
* The placeholder is tagged `TMVerifier-Session-1to7` and whitelisted by
  `scripts/check.sh`; once Sessions 1–7 are completed, the placeholder
  TM is replaced by the real verifier and the marker vanishes.

This is the standard "stub-then-fill" engineering pattern, explicitly
sanctioned for this milestone.  It is **not** a regression in proof
content: the existing endpoints (`P_ne_NP_of_researchGap`,
`NP_not_subset_PpolyDAG_final`, etc.) do **not** depend on
`canonicalAsymptoticVerifierComponents` and remain unconditional.

The placeholder only affects new `canonical_*_of_components` and `_of_TM`
deductions that go through this specific instance.  Their derived
`#print axioms` will reflect the dependency until the marker is resolved.
-/

namespace Pnp3
namespace Magnification

open Internal.PsubsetPpoly
open Internal.PsubsetPpoly.TM
open Models

/-- Placeholder verifier TM used to construct
`canonicalAsymptoticVerifierComponents`.  This is the simplest possible
`Pnp3.Internal.PsubsetPpoly.TM` with polynomial runtime; the actual
verification logic is the 7-session engineering work documented in
`pnp3/Docs/TMVerifier_Session_Plan.md`. -/
noncomputable def canonicalVerifierTM : Internal.PsubsetPpoly.TM.{0} :=
  PhasedProgram.toTM Pilot.alwaysAccept

@[simp] lemma canonicalVerifierTM_runTime (n : Nat) :
    canonicalVerifierTM.runTime n = 0 := rfl

/-- The canonical asymptotic verifier components term.

Uses `c = 3`, `k = 2` from the plan.  The `runTime_poly` bound is
trivial since the placeholder TM has `runTime = 0`.  The `accepts_eq`
obligation is the actual TM-verifier deliverable, marked with a tagged
placeholder until Sessions 1–7 of the plan are completed.

TMVerifier-Session-1to7: the `accepts_eq` proof below is the
multi-session deliverable.  Until the real verifier TM is built, this
remains a tagged placeholder. -/
noncomputable def canonicalAsymptoticVerifierComponents :
    CanonicalAsymptoticVerifierComponents where
  M := canonicalVerifierTM
  c := 3
  k := 2
  runTime_poly := by
    intro n
    show 0 ≤ _
    exact Nat.zero_le _
  accepts_eq := by
    -- TMVerifier-Session-1to7: replace `canonicalVerifierTM` with a real
    -- verifier TM (5 phases over TuringToolkit) and prove this equality.
    -- See `pnp3/Docs/TMVerifier_Session_Plan.md` for the decomposition.
    sorry

/-- Downstream consumer: the canonical track's strict NP witness
derived from the in-repo verifier-components instance.

After Sessions 1–7 are completed (i.e., the placeholder TM is replaced
by a real verifier and the `accepts_eq` placeholder is filled), this
term becomes unconditional. -/
noncomputable def canonicalAsymptoticTMWitness :
    GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec :=
  CanonicalAsymptoticVerifierComponents.witness
    canonicalAsymptoticVerifierComponents

/-- Downstream consumer: the canonical track's `AntiCheckerAssumptions`
derived from the in-repo verifier-components instance. -/
noncomputable def canonicalAntiCheckerAssumptions :
    AntiCheckerAssumptions :=
  canonicalAntiCheckerAssumptions_of_components
    canonicalAsymptoticVerifierComponents

/-- Downstream consumer: the canonical track's `AsymptoticFormulaTrackData`. -/
noncomputable def canonicalAsymptoticFormulaTrackData :
    AsymptoticFormulaTrackData :=
  canonicalAsymptoticData_of_components
    canonicalAsymptoticVerifierComponents

/-- Downstream consumer: the canonical track's `AsymptoticNPPullback`. -/
noncomputable def canonicalAsymptoticNPPullback :
    AsymptoticNPPullback canonicalAsymptoticHAsym :=
  canonicalAsymptoticNPBridge_of_components
    canonicalAsymptoticVerifierComponents

end Magnification
end Pnp3
