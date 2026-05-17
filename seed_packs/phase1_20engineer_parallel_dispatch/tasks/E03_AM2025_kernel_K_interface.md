# E03: AM 2025 Kernel K(Q,D,r) construction interface

**Engineer:** E03 | **Phase:** A | **Estimated:** 2 weeks | **Difficulty:** medium | **Dependencies:** none (defines self-contained interface; if E01/E02 land first, integrate by import)

---

## Goal

Formalize Atserias-Müller 2025's **Kernel** construction `K(Q,D,r)` as a Lean structure that represents the encoded oracle/kernel input used by the magnification proof. Provide accessor functions for its components (`n`, sampled coordinates `u ∈ [m(n)]^r`, bits `b_j = (xD)_{u_j}`) and the length bound `≤ 10 r(n) log m(n)`.

---

## Source material

* **Paper:** Atserias-Müller 2025, arXiv:2503.24061.
* **Specific construction:** §3 Definition `K(Q,D,r)`, plus Lemma `kernel` and Lemma `localform`.

---

## Deliverable

```
pnp4/Pnp4/Literature/AtseriasMuller2025/KernelK.lean
```

### Expected signatures

```lean
namespace Pnp4
namespace Literature
namespace AtseriasMuller2025

/-- Parameters of the AM 2025 kernel construction. -/
structure KernelParameters where
  n : Nat
  m : Nat  -- distinguisher output length (from Theorem 1)
  r : Nat  -- sampling count
  m_pos : 0 < m

/-- An AM 2025 kernel input string: contains `n`, sampled coords `u`, and sampled bits. -/
structure KernelInput (p : KernelParameters) where
  sampled_coords : Fin p.r → Fin p.m
  sampled_bits : Fin p.r → Bool

/-- Encoded kernel length bound `≤ 10 r log m`. -/
def kernelLengthBound (p : KernelParameters) : Nat :=
  10 * p.r * Nat.log2 (p.m + 1) + 10  -- closed-form upper bound

theorem kernelInput_lengthBound (p : KernelParameters) (_k : KernelInput p) :
    1 ≤ kernelLengthBound p

/-- Sampled XOR fan-in: each sampled bit `(xD)_{u_j}` is XOR over `w` input bits where `w` is the distinguisher weight. -/
structure SampledXORStructure (p : KernelParameters) (w : Nat) where
  selected_inputs : Fin p.r → Fin w → Fin p.n
  -- Each sampled bit is determined by ≤ w input bits

/-- The sampled incidence product `r · w`, used by AM §3 success condition. -/
def sampledIncidence (p : KernelParameters) (w : Nat) : Nat :=
  p.r * w
```

### Lemmas to prove

```lean
/-- Kernel length is polynomial in `r` and `log m`. -/
theorem kernelLengthBound_poly (p : KernelParameters) :
    kernelLengthBound p ≤ 10 * p.r * (p.m + 1) + 10

/-- Sampled incidence product equals `r · w`. -/
theorem sampledIncidence_eq (p : KernelParameters) (w : Nat) :
    sampledIncidence p w = p.r * w := rfl

/-- The kernel input is type-finite for fixed parameters. -/
instance KernelInput_fintype (p : KernelParameters) : Fintype (KernelInput p)
```

---

## Acceptance criteria

### Universal
(see COMMON §4)

### Task-specific
- [ ] `KernelParameters` and `KernelInput` structures defined with exactly the fields above.
- [ ] `kernelLengthBound : KernelParameters → Nat` defined as closed-form Nat function.
- [ ] `SampledXORStructure` defined per AM §3.
- [ ] `sampledIncidence`, `kernelLengthBound_poly`, `sampledIncidence_eq` all proven kernel-clean.
- [ ] `Fintype (KernelInput p)` instance proven.
- [ ] Module doc-comment cites AM 2025 §3 explicitly.
- [ ] **No `Classical.choose`.**

### Verification
```bash
rg "^structure KernelParameters" pnp4/Pnp4/Literature/AtseriasMuller2025/
rg "^structure KernelInput" pnp4/Pnp4/Literature/AtseriasMuller2025/
rg "^def kernelLengthBound" pnp4/Pnp4/Literature/AtseriasMuller2025/
rg "^instance KernelInput_fintype" pnp4/Pnp4/Literature/AtseriasMuller2025/
```

---

## Scope

### Allowed
- New module at `pnp4/Pnp4/Literature/AtseriasMuller2025/KernelK.lean`.
- One `Glob.one` line.
- Smoke test + axiom audit per universal acceptance.

### Forbidden
- Universal forbiddens (COMMON §3).
- ❌ No `axiom`.
- ❌ No claim that AM 2025's `Lemma kernel` (collision probability bound `2^q(1-δ)^r`) holds for any specific Q.

---

## Notes

- `Nat.log2` is the right approximation for `log m` since `m` is an integer.
- For `Fintype (KernelInput p)`, use the standard `Fintype` derivation for function types from `Fin p.r → Fin p.m × Fin p.r → Bool`.
- 2-week estimate assumes ~3 days reading AM §3, ~7 days Lean implementation, ~2 days proving lemmas, ~2 days polish.

---

## Output

Universal template (COMMON §12).
