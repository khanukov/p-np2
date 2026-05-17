# E08: OPS 2021 magnification thresholds

**Engineer:** E08 | **Phase:** A | **Estimated:** 2 weeks | **Difficulty:** medium | **Dependencies:** can run in parallel with E07

## Goal

Formalize the **statement** of OPS 2021's main magnification theorem: weak lower bounds at `n^{1+ε}` formula size imply strong lower bounds (e.g., super-polynomial). Capture the threshold parameters `β, ε, c` and the FML/PFML formula-size schedule.

## Source material

* OPS 2021, DOI 10.4086/toc.2021.v017a011.
* Specific theorem: §1 main theorem `intromain`: Gap-MCSP at thresholds `s_1, s_2` is not in `FML[n^{1+2ε+δ}]` ⇒ `NP ⊄ FML[n^c]`. Universal constant `c`, slack `β`, `ε > 0`.

## Deliverable

```
pnp4/Pnp4/Literature/OPS2021/MagnificationThresholds.lean
```

### Expected signatures

```lean
namespace Pnp4
namespace Literature
namespace OPS2021

structure OPSMagnificationParameters where
  β : Nat  -- threshold exponent inside Gap-MCSP
  ε : Rat  -- small slack
  δ : Rat  -- additional slack for the input regime
  c : Nat  -- target lower-bound exponent (NP ⊄ FML[n^c])
  ε_pos : 0 < ε
  δ_pos : 0 < δ

/-- OPS magnification statement: weak Gap-MCSP bound ⇒ strong NP-vs-FML bound. -/
structure OPSMagnificationStatement extends OPSMagnificationParameters where
  -- "Gap-MCSP[2^{β·n}/cn, 2^{β·n}] not in FML[n^{1+2ε+δ}]"
  weakBound : Prop
  -- "NP ⊄ FML[n^c]"
  strongBound : Prop
  magnifies : weakBound → strongBound

/-- Sample concrete parameter regime from OPS §1.1. -/
def OPS_sampleParameters : OPSMagnificationParameters where
  β := 1
  ε := 1/100
  δ := 1/100
  c := 100
  ε_pos := by norm_num
  δ_pos := by norm_num
```

### Lemmas to prove

```lean
theorem OPSMagnificationParameters.exists : 
    ∃ p : OPSMagnificationParameters, p.c ≥ 100

theorem OPS_sampleParameters_valid : 
    OPS_sampleParameters.c ≥ 100 := by decide
```

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] `OPSMagnificationParameters` structure with all 6 fields per OPS §1.
- [ ] `OPSMagnificationStatement` extending the parameters.
- [ ] At least one concrete sample (`OPS_sampleParameters`).
- [ ] Two theorems proven kernel-clean.
- [ ] **No claim** that any specific `OPSMagnificationStatement` is true — `weakBound → strongBound` is structure data, not asserted.
- [ ] Module doc-comment cites OPS 2021 §1 explicitly.

## Scope

### Allowed
- `pnp4/Pnp4/Literature/OPS2021/MagnificationThresholds.lean`.
- May import from E07 if landed.

### Forbidden
- Universal.
- ❌ No claim that OPS magnification has been proven for any specific instance.

## Output
Universal template.
