import Magnification.UnconditionalResearchGap
import Tests.FormulaSupportBoundsFalsifiabilityProbe

/-!
# FixedParams Probe — audit-only surface (FP-1)

Research Governance v0.1, FP-1 (FixedParams Probe preparation).

This module is the **audit-facing surface** for the FixedParams
Probe.  It is preparatory: it does NOT attempt Outcome A
(formal `→ False` for the route), Outcome B (factorisation through
known guards), or Outcome C (promotion of a new candidate
`SourceTheorem`).  Those are FP-2 / FP-3 / FP-4.

What this module does:

1. Re-export the key existing identifiers under canonical
   `FixedParamsProbe.*` audit names.
2. Surface the hardwiring obstruction (Probe 2 of the
   falsifiability probe) as the formal artifact backing the
   `HardwiringGuard` entry of `spec/known_guards.toml`.
3. Provide nothing else: no new theorems, no new predicates, no
   `class`/`instance`/`Fact` payload.

What this module does NOT do (per FP-1 scope):

* No new `Prop` defining a candidate provenance Π.
* No `gap_from_*` bridge.
* No `SourceTheorem_*`.
* No reference to `ResearchGapWitness`.
* No edits to the trust root
  (`Pnp3.Complexity.Interfaces`, `Pnp3.Magnification.UnconditionalResearchGap`,
  `Pnp3.Magnification.FormulaSupportBoundsPartial_fromPipeline_fixedParams`).
* No `class`/`instance`/`Fact`/`opaque`/`default_instance`.

The names below all begin with the `FixedParamsProbe.` namespace
prefix and the file lives under `pnp3/Magnification/AuditRoutes/`,
both of which are recognised by the project's quarantine guards as
audit-only zones.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace FixedParamsProbe

open Pnp3.Magnification (
  FormulaSupportBoundsPartial_fromPipeline_fixedParams
  OverbroadUniformFormulaProvenance
)

/-!
## Audit-only aliases for the FixedParams route shape.

Each `abbrev` below re-exports an existing identifier under a
canonical name that the FP-2/FP-3/FP-4 probes will reference.
-/

/-- Audit alias for `FormulaSupportBoundsPartial_fromPipeline_fixedParams`,
the predicate that the FixedParams Probe wants to either kill
(Outcome A) or factor through known guards (Outcome B). -/
abbrev FixedParamsRoute
    (ac0 : ThirdPartyFacts.AC0Parameters) (sb : Nat → Nat) : Prop :=
  FormulaSupportBoundsPartial_fromPipeline_fixedParams ac0 sb

/-- Audit alias for `OverbroadUniformFormulaProvenance`, the broad
provenance shape that, paired with `FixedParamsRoute`, reconstructs
the refuted `FormulaSupportRestrictionBoundsPartial`.  Used as the
"counterexample provenance" baseline in FP-2. -/
abbrev OverbroadUniformProvenance
    (ac0 : ThirdPartyFacts.AC0Parameters) : Prop :=
  OverbroadUniformFormulaProvenance ac0

/-!
## Hardwiring obstruction surface.

Probe 2 of `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`
constructs a `PpolyFormula` witness for `gapPartialMCSP_Language` by
truth-table hardwiring.  Any candidate provenance Π that fails to
exclude such a witness is automatically vacuous: the singleton
truth-table family satisfies "arbitrary `PpolyFormula` quantification"
without doing any real work.

`HardwiringObstruction` re-exposes the formal artifact
(`Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.fixedSlice_gapPartialMCSP_in_PpolyFormula`)
under a stable name so that
`spec/known_guards.toml::guards.HardwiringGuard` can refer to it
without fragility.
-/

/-- Audit alias for the truth-table hardwiring lemma (Probe 2). -/
def HardwiringObstruction
    (p : Pnp3.Models.GapPartialMCSPParams) :
    Pnp3.ComplexityInterfaces.PpolyFormula
        (Pnp3.Models.gapPartialMCSP_Language p) :=
  Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.fixedSlice_gapPartialMCSP_in_PpolyFormula p

/-- The hardwiring guard, in audit-only form: every Partial-MCSP
slice has at least one `PpolyFormula` witness, and that witness is
exhibited by the truth-table construction above.  This is the formal
backing of `spec/known_guards.toml::guards.HardwiringGuard`.

A candidate provenance Π that does not formally exclude this witness
shape (or factor through it) is deemed vacuous in FP-2. -/
def HardwiringGuard : Prop :=
  ∀ (p : Pnp3.Models.GapPartialMCSPParams),
    Nonempty (Pnp3.ComplexityInterfaces.PpolyFormula
                (Pnp3.Models.gapPartialMCSP_Language p))

/-- The hardwiring guard is inhabited via Probe 2. -/
theorem hardwiring_guard_holds : HardwiringGuard :=
  fun p => ⟨HardwiringObstruction p⟩

end FixedParamsProbe
end AuditRoutes
end Magnification
end Pnp3
