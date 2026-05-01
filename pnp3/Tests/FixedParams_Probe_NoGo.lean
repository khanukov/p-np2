import Magnification.AuditRoutes.FixedParamsProbe

/-!
# FixedParams Probe — NoGo smoke skeleton (FP-1)

Research Governance v0.1, FP-1.

This is the **regression-test scaffolding** for the FixedParams
Probe.  It is intentionally minimal: FP-1 only verifies that the
audit-only surface in
`pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean` builds and
exposes the canonical names used by `spec/known_guards.toml`.

FP-2 will populate this file with the actual Outcome A regression
test:

```
theorem fixedParams_route_dies_via_hardwiring :
    ∀ Π satisfying Rule-5 hardwiring exclusion,
      ¬ (FixedParamsRoute ac0 sb ∧ Π → ResearchGapWitness)
```

(or a more concrete formulation against a specific candidate Π).

FP-1 only asserts that the import compiles and the audit names are
present.  Anything stronger lives in FP-2.
-/

namespace Pnp3
namespace Tests
namespace FixedParamsProbeNoGo

open Pnp3.Magnification.AuditRoutes.FixedParamsProbe

/-! ## Smoke checks: audit names exist and have the expected types. -/

example
    (ac0 : Pnp3.ThirdPartyFacts.AC0Parameters)
    (sb : Nat → Nat) :
    FixedParamsRoute ac0 sb = FixedParamsRoute ac0 sb :=
  rfl

example
    (ac0 : Pnp3.ThirdPartyFacts.AC0Parameters) :
    OverbroadUniformProvenance ac0 = OverbroadUniformProvenance ac0 :=
  rfl

/-- Smoke: the hardwiring guard is inhabited (Probe 2 backing). -/
theorem fp1_hardwiring_guard_holds : HardwiringGuard :=
  hardwiring_guard_holds

/-- Smoke: the hardwiring obstruction's underlying formal artifact
(Probe 2 of the falsifiability probe) elaborates as a
`PpolyFormula` witness for every slice. -/
theorem fp1_hardwiring_obstruction_exists
    (p : Pnp3.Models.GapPartialMCSPParams) :
    Nonempty (Pnp3.ComplexityInterfaces.PpolyFormula
                (Pnp3.Models.gapPartialMCSP_Language p)) :=
  ⟨HardwiringObstruction p⟩

end FixedParamsProbeNoGo
end Tests
end Pnp3
