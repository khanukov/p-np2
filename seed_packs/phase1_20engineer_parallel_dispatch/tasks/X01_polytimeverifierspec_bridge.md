# X01: PolyTimeVerifierSpec + bridge to NP_TM

**Engineer:** X01 | **Phase:** 5 — Contract expansion | **Estimated:** 3 weeks | **Difficulty:** medium

## Goal

Implement the `PolyTimeVerifierSpec` Lean structure + the bridge theorem `PolyTimeVerifierSpec L → Pnp3.ComplexityInterfaces.NP L` per the polynomial-time formalism scoping D0 (V4 canonical, merged `d3676520`).

This implements **Option B.1** from the D0 scoping. **Not R1-C work.**

## Source material

* `seed_packs/polynomial_time_formalism_scoping_D0/reports/D0_polynomial_time_formalism_gpt55.md` (V4).
* `seed_packs/polynomial_time_formalism_scoping_D0/reports/D0_four_way_review_and_synthesis_claudeopus.md`.
* `pnp3/Complexity/Interfaces.lean` (read-only): `NP_TM`, `certificateLength`, `concatBitstring`.
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

structure PolyTimeVerifierSpec (L : Pnp3.ComplexityInterfaces.Language) where
  verifierTM : Pnp3.Internal.PsubsetPpoly.TM
  certExp : Nat
  runExp : Nat
  runTimeBound : ∀ n : Nat, 
    verifierTM.runTime (n + Pnp3.ComplexityInterfaces.certificateLength n certExp) ≤
      (n + Pnp3.ComplexityInterfaces.certificateLength n certExp) ^ runExp + runExp
  accepts : ∀ n (x : Pnp3.ComplexityInterfaces.Bitstring n),
    L n x = true ↔
      ∃ w : Pnp3.ComplexityInterfaces.Bitstring (Pnp3.ComplexityInterfaces.certificateLength n certExp),
        verifierTM.accepts (Pnp3.ComplexityInterfaces.concatBitstring x w)
```

### Expected signatures (BridgeToNPTM.lean)

```lean
theorem PolyTimeVerifierSpec.toNP_TM 
    {L : Pnp3.ComplexityInterfaces.Language} (spec : PolyTimeVerifierSpec L) :
    Pnp3.ComplexityInterfaces.NP L := by
  refine ⟨spec.certExp, spec.runExp, spec.verifierTM, ?_, ?_⟩
  · exact spec.runTimeBound
  · exact spec.accepts
```

### Toy verifier instantiation

Construct one **non-trivial PolyTimeVerifierSpec** for an explicit language (e.g., `fun _ _ => false` empty language or `fun _ _ => true` universal language) with concrete TM and proven `runTimeBound` / `accepts`. **No `sorry`.**

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] Two modules at exact paths.
- [ ] `PolyTimeVerifierSpec` structure with all 5 fields.
- [ ] `toNP_TM` bridge theorem proven kernel-clean (one-liner via `refine`).
- [ ] At least one toy verifier `def` constructed with **no `sorry`**.
- [ ] Doc-comment cites D0 scoping report.
- [ ] **Anti-faking criterion (V1 of D0)**: bridge must NOT accept staged `Prop` placeholders.

### Honest caveats
- The toy verifier must actually be `sorry`-free. If too painful, choose a simpler language.

## Scope

### Allowed
- New modules under `pnp4/Pnp4/Frontier/ContractExpansion/`.

### Forbidden
- Universal.
- ❌ Editing `pnp3/Complexity/Interfaces.lean` or `pnp3/Complexity/PsubsetPpolyInternal/TuringEncoding.lean`.
- ❌ Claim of `PrefixExtensionLanguage_in_NP` (that's X02 dependency).
- ❌ R1-C work.
- ❌ `sorry` in final landed code.

## Output
Universal template. Especially explicit about toy verifier choice in "Honest caveats".
