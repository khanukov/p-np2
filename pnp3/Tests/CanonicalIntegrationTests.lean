import Magnification.CanonicalAsymptoticTrackData
import Magnification.CanonicalAsymptoticDecider
import Magnification.FinalResultMainline
import Magnification.FinalResultAuditRoutes
import Magnification.UnconditionalResearchGap
import Tests.BridgeLocalityRegression

/-!
# Canonical-asymptotic-track integration tests

This file demonstrates that the `canonicalAsymptoticHAsym` and the
`canonicalAnti{NPBridge,Data,AssumptionsCheckerAssumptions}_of_TM W` builders
from `Magnification.CanonicalAsymptoticTrackData` integrate cleanly with the
existing downstream mainline and audit-route endpoints.

Every theorem below is a **compile-time type-check**: it shows that the
canonical infrastructure can drive the corresponding downstream endpoint with
zero `(hAsym, hNPbridge)` boilerplate at the call site.

The single remaining hypothesis is the TM-verifier witness
`W : Models.GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec`,
which corresponds to the published OPS19/CJW20 fact "GapMCSP ∈ NP".
-/

namespace Pnp3.Tests

open Pnp3
open Pnp3.Models
open Pnp3.ComplexityInterfaces
open Pnp3.Magnification

/-! ## Smoke tests: the canonical builders type-check. -/

example : canonicalAsymptoticHAsym.spec = canonicalAsymptoticSpec := rfl

example : canonicalAsymptoticHAsym.N0 = 8 := rfl

example
    (W : Models.GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec) :
    AsymptoticNPPullback canonicalAsymptoticHAsym :=
  canonicalAsymptoticNPBridge_of_TM W

example
    (W : Models.GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec) :
    AsymptoticFormulaTrackData :=
  canonicalAsymptoticData_of_TM W

example
    (W : Models.GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec) :
    AntiCheckerAssumptions :=
  canonicalAntiCheckerAssumptions_of_TM W

/-! ## Plug into downstream endpoints

Every existing downstream theorem that takes `(hAsym, hNPbridge)` now accepts
the canonical pair as `canonicalAntiCheckerAssumptions_of_TM W`.
-/

/-- Plug the canonical track into `i4_final_wiring_of_formulaCertificate`.

After this, the result `NP_not_subset_PpolyFormula` depends only on:

* `hCert : FormulaCertificateProviderPartial`  — the AC0 source provider.
* `W : Models.GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec`
  — the TM verifier for canonical GapMCSP-asymptotic.
* `n : Nat` with `8 ≤ n` — the slice index. -/
theorem canonical_NP_not_subset_PpolyFormula_of_formulaCertificate
    (hCert : Pnp3.Magnification.FormulaCertificateProviderPartial)
    (W : Models.GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec)
    (n : Nat) (hn : 8 ≤ n) :
    NP_not_subset_PpolyFormula :=
  i4_final_wiring_of_formulaCertificate
    (hCert := hCert)
    (hAsym := (canonicalAntiCheckerAssumptions_of_TM W).asymptotic)
    (hNPbridge := (canonicalAntiCheckerAssumptions_of_TM W).npBridge)
    (n := n)
    (hn := hn)

/-- Plug the canonical track into the asymptotic iso-strong route.

After this, the DAG-side separation `NP_not_subset_PpolyDAG` depends only on:

* `W` — the TM verifier.
* `hIso` — the iso-strong family witness for the asymptotic anti-checker. -/
theorem canonical_NP_not_subset_PpolyDAG_of_isoStrongRoute
    (W : Models.GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec)
    (hIso : Pnp3.Magnification.AsymptoticIsoStrongRoute canonicalAsymptoticHAsym) :
    NP_not_subset_PpolyDAG :=
  Pnp3.Magnification.NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute_withAntiChecker
    (anti := canonicalAntiCheckerAssumptions_of_TM W)
    hIso

/-- Companion `P ≠ NP` endpoint via the canonical track. -/
theorem canonical_P_ne_NP_of_isoStrongRoute
    (W : Models.GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec)
    (hIso : Pnp3.Magnification.AsymptoticIsoStrongRoute canonicalAsymptoticHAsym) :
    P_ne_NP :=
  Pnp3.Magnification.P_ne_NP_final_of_asymptotic_isoStrongRoute_withAntiChecker
    (anti := canonicalAntiCheckerAssumptions_of_TM W)
    hIso

/-- Plug the canonical track into the promise-YES certificate route. -/
theorem canonical_NP_not_subset_PpolyDAG_of_promiseYesCertificateRoute
    (W : Models.GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec)
    (hRoute : Pnp3.Magnification.AsymptoticPromiseYesCertificateRoute
      canonicalAsymptoticHAsym) :
    NP_not_subset_PpolyDAG :=
  Pnp3.Magnification.NP_not_subset_PpolyDAG_final_of_asymptotic_promiseYesCertificateRoute_withAntiChecker
    (anti := canonicalAntiCheckerAssumptions_of_TM W)
    hRoute

/-- Companion `P ≠ NP` endpoint via the canonical promise-YES certificate route. -/
theorem canonical_P_ne_NP_of_promiseYesCertificateRoute
    (W : Models.GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec)
    (hRoute : Pnp3.Magnification.AsymptoticPromiseYesCertificateRoute
      canonicalAsymptoticHAsym) :
    P_ne_NP :=
  Pnp3.Magnification.P_ne_NP_final_of_asymptotic_promiseYesCertificateRoute_withAntiChecker
    (anti := canonicalAntiCheckerAssumptions_of_TM W)
    hRoute

/-! ## Decoder-bridge integration

The `CanonicalAsymptoticVerifierComponents` bridge reduces the open
TM-verifier obligation to a single typed sub-obligation.  Every
`canonical_*` theorem above can be re-stated taking `Components`
instead of `Asymptotic_TMWitness`, since `Components → Witness`. -/

example (V : Pnp3.Magnification.CanonicalAsymptoticVerifierComponents) :
    Models.GapPartialMCSP_Asymptotic_TMWitness canonicalAsymptoticSpec :=
  Pnp3.Magnification.CanonicalAsymptoticVerifierComponents.witness V

example (V : Pnp3.Magnification.CanonicalAsymptoticVerifierComponents) :
    AntiCheckerAssumptions :=
  Pnp3.Magnification.canonicalAntiCheckerAssumptions_of_components V

/-- Components-track version of the iso-strong route plug-in. -/
theorem canonical_NP_not_subset_PpolyDAG_of_components_and_isoStrongRoute
    (V : Pnp3.Magnification.CanonicalAsymptoticVerifierComponents)
    (hIso : Pnp3.Magnification.AsymptoticIsoStrongRoute canonicalAsymptoticHAsym) :
    NP_not_subset_PpolyDAG :=
  canonical_NP_not_subset_PpolyDAG_of_isoStrongRoute
    (W := Pnp3.Magnification.CanonicalAsymptoticVerifierComponents.witness V)
    hIso

/-- Components-track companion `P ≠ NP` via the iso-strong route. -/
theorem canonical_P_ne_NP_of_components_and_isoStrongRoute
    (V : Pnp3.Magnification.CanonicalAsymptoticVerifierComponents)
    (hIso : Pnp3.Magnification.AsymptoticIsoStrongRoute canonicalAsymptoticHAsym) :
    P_ne_NP :=
  canonical_P_ne_NP_of_isoStrongRoute
    (W := Pnp3.Magnification.CanonicalAsymptoticVerifierComponents.witness V)
    hIso

end Pnp3.Tests
