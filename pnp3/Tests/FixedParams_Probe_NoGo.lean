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

/-! ### FP-2 — Outcome A baseline (overbroad uniform provenance) -/

/-- **FP-2 regression test**: the audit-only Outcome A baseline
elaborates and produces `False` from `FixedParamsRoute` paired with
`OverbroadUniformProvenance`.

This is a re-statement of the underlying audit theorem
`NoGo_FixedParamsRoute_with_OverbroadUniformProvenance`; if the
audit chain ever drifts (e.g. a refactor of Probe 8a), this test
breaks at build time. -/
theorem fp2_outcome_a_overbroad_baseline
    (p : Pnp3.Models.GapPartialMCSPParams)
    (ac0 : Pnp3.ThirdPartyFacts.AC0Parameters)
    (sb : Nat → Nat)
    (hUniform : OverbroadUniformProvenance ac0)
    (hRoute   : FixedParamsRoute ac0 sb) :
    False :=
  NoGo_FixedParamsRoute_with_OverbroadUniformProvenance
    p ac0 sb hUniform hRoute

/-! ### FP-3 actual — `SupportFunctionalDiversity` candidate (audit-only)

Regression-test scaffolding for the FP-3 actual self-attack work.
The candidate `FP3Attempt.InSupportFunctionalDiversity` is NOT
promoted to `spec/known_guards.toml`; these tests simply pin the
audit-only surface against future drift.

Per `FixedParams_Probe.md` §FP-3 actual, the candidate is classified
as **C-candidate with caveats** — it formally defeats the Probe-2
single-slice truth-table hardwiring attack via the abstract uniform-
`polyBound` exclusion lemma, but it carries an explicit multi-slice
hardwiring caveat and is NOT a green light to start FP-4. -/

/-- Smoke: the candidate diversity Prop elaborates at the expected
type. -/
example
    {L : Pnp3.ComplexityInterfaces.Language}
    (w : Pnp3.ComplexityInterfaces.InPpolyFormula L) :
    FP3Attempt.InSupportFunctionalDiversity w
      = FP3Attempt.InSupportFunctionalDiversity w :=
  rfl

/-- **FP-3 actual Test-3 regression**: the abstract hardwiring-attack
defeat lemma is inhabited.  Any `InPpolyFormula` record with a
uniformly-bounded `polyBound` violates the candidate diversity
filter.  The Probe-2 hardwired record is an instance of this
abstract pattern (its `polyBound` is `c₀_size` at one length and `1`
elsewhere); the abstract form keeps the regression light-weight
without re-constructing the full hardwired record here. -/
theorem fp3_actual_test3_hardwiring_attack_defeated
    {L : Pnp3.ComplexityInterfaces.Language}
    (w : Pnp3.ComplexityInterfaces.InPpolyFormula L) (B : Nat)
    (hBound : ∀ n, w.polyBound n ≤ B) :
    ¬ FP3Attempt.InSupportFunctionalDiversity w :=
  FP3Attempt.InSupportFunctionalDiversity_excludes_uniformPolyBound w B hBound

end FixedParamsProbeNoGo
end Tests
end Pnp3
