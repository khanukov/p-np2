# E19: PolyTimeVerifierSpec + bridge to NP_TM

**Engineer:** E19 | **Phase:** D — Contract expansion completion | **Estimated:** 3 weeks | **Difficulty:** medium | **Dependencies:** none (Option B.1 from D0 scoping)

## Goal

Implement the **`PolyTimeVerifierSpec` Lean structure** + the **bridge theorem** `PolyTimeVerifierSpec L → Pnp3.ComplexityInterfaces.NP L`, per the polynomial-time formalism scoping D0 (V4 selected, merged at `d3676520`).

This implements **Option B.1** from the D0 scoping. It is **not** R1-C work; it's reusable NP infrastructure.

## Source material

* `seed_packs/polynomial_time_formalism_scoping_D0/reports/D0_polynomial_time_formalism_gpt55.md` (the canonical D0 report, V4).
* `seed_packs/polynomial_time_formalism_scoping_D0/reports/D0_four_way_review_and_synthesis_claudeopus.md` (synthesis).
* `pnp3/Complexity/Interfaces.lean` (read-only target): definition of `NP_TM`, `certificateLength n k = n^k + k`, `concatBitstring`.
* `pnp3/Complexity/PsubsetPpolyInternal/TuringEncoding.lean` (read-only): TM model.

## Deliverable

```
pnp4/Pnp4/Frontier/ContractExpansion/PolyTimeVerifierSpec.lean
pnp4/Pnp4/Frontier/ContractExpansion/BridgeToNPTM.lean
```

### Expected signatures (PolyTimeVerifierSpec.lean)

```lean
namespace Pnp4
namespace Frontier
namespace ContractExpansion

/-- A polynomial-time NP verifier specification, suitable for bridging to pnp3 NP_TM. -/
structure PolyTimeVerifierSpec (L : Pnp3.ComplexityInterfaces.Language) where
  /-- Concrete TM that decides the verifier's accepts predicate. -/
  verifierTM : Pnp3.Internal.PsubsetPpoly.TM
  /-- Certificate length exponent. -/
  certExp : Nat
  /-- Runtime exponent. -/
  runExp : Nat
  /-- Runtime bound: TM accepts within (n + certLen n certExp)^runExp + runExp steps. -/
  runTimeBound : 
    ∀ n : Nat, verifierTM.runTime (n + Pnp3.ComplexityInterfaces.certificateLength n certExp) ≤ 
      (n + Pnp3.ComplexityInterfaces.certificateLength n certExp) ^ runExp + runExp
  /-- Accepts equivalence: L n x iff some certificate makes TM accept. -/
  accepts : 
    ∀ n (x : Pnp3.ComplexityInterfaces.Bitstring n),
      L n x = true ↔ 
        ∃ w : Pnp3.ComplexityInterfaces.Bitstring (Pnp3.ComplexityInterfaces.certificateLength n certExp),
          verifierTM.accepts (Pnp3.ComplexityInterfaces.concatBitstring x w)
```

### Expected signatures (BridgeToNPTM.lean)

```lean
namespace Pnp4
namespace Frontier
namespace ContractExpansion

/-- The bridge theorem: every PolyTimeVerifierSpec instantiates pnp3 NP_TM. -/
theorem PolyTimeVerifierSpec.toNP_TM 
    {L : Pnp3.ComplexityInterfaces.Language} 
    (spec : PolyTimeVerifierSpec L) :
    Pnp3.ComplexityInterfaces.NP L := by
  refine ⟨spec.certExp, spec.runExp, spec.verifierTM, ?_, ?_⟩
  · exact spec.runTimeBound
  · exact spec.accepts
```

### Toy verifier instantiation

Provide one **trivial PolyTimeVerifierSpec** showing the structure is not vacuous:

```lean
/-- The empty language has a trivial PolyTimeVerifierSpec (accepts nothing). -/
def emptyLanguageSpec : PolyTimeVerifierSpec (fun _ _ => false) where
  verifierTM := ...  -- TM that always rejects
  certExp := 1
  runExp := 1
  runTimeBound := ...
  accepts := by
    intros n x
    simp
    intro w
    -- TM always rejects, so no w accepts
    sorry  -- TODO: actually prove this; placeholder will be rejected by acceptance criteria
```

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] `PolyTimeVerifierSpec` structure with all 5 fields specified.
- [ ] `toNP_TM` bridge theorem proven kernel-clean (one-liner via `refine`).
- [ ] **No `Classical.choose`** in the bridge theorem.
- [ ] At least one toy verifier instantiation (e.g., empty language or universal language) proven with `sorry`-free `accepts` and `runTimeBound` fields.
- [ ] Module doc-comment cites the D0 scoping report.
- [ ] **Anti-faking criterion** (per V1 of D0): the bridge must NOT accept staged `Prop` placeholders. Only `runTime` inequalities and real `accepts` equivalences are permitted.

### Honest caveats expected
- The toy verifier instantiation must actually be `sorry`-free. If proving its `accepts` field is too painful, choose a simpler language (e.g., language that is `true` everywhere, with a trivial TM that always accepts).

## Scope

### Allowed
- New modules under `pnp4/Pnp4/Frontier/ContractExpansion/`.
- One `Glob.one` per new module.

### Forbidden
- Universal.
- ❌ **No modification of `pnp3/Complexity/Interfaces.lean`.**
- ❌ **No modification of `pnp3/Complexity/PsubsetPpolyInternal/TuringEncoding.lean`.**
- ❌ No claim that `PrefixExtensionLanguage_in_NP` is proven (that depends on E20).
- ❌ No R1-C work.
- ❌ No `sorry` in any final landed code (placeholders during development OK; before PR, must be removed).

## Output
Universal template. Be especially explicit in "Honest caveats" about what toy language you chose and why.
