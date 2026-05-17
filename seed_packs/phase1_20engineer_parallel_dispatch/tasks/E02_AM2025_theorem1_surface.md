# E02: AM 2025 Theorem 1 typed surface

**Engineer:** E02
**Phase:** A — Literature formalization
**Estimated time:** 2 weeks
**Difficulty:** medium
**Dependencies:** none (does not depend on E01; you may import E01's `Distinguisher` once it lands, or define a self-contained version)

---

## Goal

Formalize the **statement** of Atserias-Müller 2025 Theorem 1 as a typed surface (structure containing the existence claim plus the bound parameters). **Do not** prove existence — that would require formalizing the entire AM construction. Provide a clear separation between "Theorem 1's statement" (what AM claim) and "an instance" (constructive evidence; out of scope).

---

## Source material

* **Paper:** Atserias-Müller 2025, arXiv:2503.24061.
* **Specific theorem:** §1 / §2 Theorem 1 (also restated as Theorem `dist`): for `0 < ε ≤ 1`, there is a polynomial-time algorithm which, given `n`, computes an `(n,m,n^{-ε},1/8)`-distinguisher with `m ≤ n^7` and weight at most `⌈2n^ε⌉`.

---

## Deliverable

```
pnp4/Pnp4/Literature/AtseriasMuller2025/Theorem1Surface.lean
```

### Expected signatures

```lean
namespace Pnp4
namespace Literature
namespace AtseriasMuller2025

/-- Parameters of an AM 2025 Theorem 1 instance.
    Captures the existence claim without committing to a specific construction. -/
structure Theorem1Parameters (n : Nat) (ε : Rat) where
  m : Nat
  m_bound : m ≤ n ^ 7
  weight : Nat
  weight_bound : weight ≤ Nat.ceil (2 * (n : Rat) ^ ε.num.toNat)
  -- ε must be in (0,1]
  ε_pos : 0 < ε
  ε_le_one : ε ≤ 1

/-- AM 2025 Theorem 1's witness: an actual distinguisher with the claimed bounds. -/
structure Theorem1Witness (n : Nat) (ε : Rat) extends Theorem1Parameters n ε where
  D : Distinguisher n m (1 / (n : Rat) ^ ε.num.toNat) (1 / 8)
  D_sparse : IsSparse n m weight D.M

/-- Polynomial-time construction algorithm (as an abstract existence claim). -/
def Theorem1ConstructibleInPolyTime (n : Nat) (ε : Rat) : Prop :=
  ∃ _w : Theorem1Witness n ε, True
  -- The `poly-time` aspect is currently captured at the type level only:
  -- a Lean theorem `Theorem1ConstructibleInPolyTime n ε` exists per AM.
  -- A future task may upgrade to a real runtime bound.
```

### Theorem statements (declared, not proven — see §"Why not proven" below)

```lean
/-- AM 2025 Theorem 1, as a typed surface (statement only, instance not constructed). -/
theorem AM2025_Theorem1_statement_shape (n : Nat) (ε : Rat) 
    (hε_pos : 0 < ε) (hε_le : ε ≤ 1) :
    ∀ _h : Theorem1ConstructibleInPolyTime n ε,
      ∃ w : Theorem1Witness n ε, True := by
  intro h
  exact h

/-- The parameter bound `m ≤ n^7` is structural. -/
theorem Theorem1Parameters.m_polynomial_in_n (n : Nat) (ε : Rat)
    (p : Theorem1Parameters n ε) :
    p.m ≤ n ^ 7 :=
  p.m_bound
```

### Why not proven

The literal proof of AM 2025 Theorem 1 requires:
- Coding-theory machinery (error-correcting codes with rate/distance trade-offs)
- A polynomial-time construction algorithm (multi-step pseudorandom generator)
- Runtime analysis in the pnp3 / pnp4 sense

This is multi-month work. E02 captures only the **typed surface** so future engineers (or external researchers) can:
- Reference AM Theorem 1 as a Lean `Prop`.
- Instantiate the `Theorem1Witness` if they later provide a construction.
- Compose with downstream theorems (E03 kernel construction, etc.) without re-deriving the statement.

This is honest: the structure exists; the witness existence is a `Prop` we **declare** (via the existential), not **prove**.

---

## Acceptance criteria

### Universal

(see COMMON_WORKER_INSTRUCTIONS.md §4 — applies)

### Task-specific

- [ ] `Theorem1Parameters` structure with exactly the fields specified.
- [ ] `Theorem1Witness` structure extending `Theorem1Parameters` with `D` (distinguisher), `D_sparse`.
- [ ] `Theorem1ConstructibleInPolyTime` defined as `∃ _w : Theorem1Witness ..., True`.
- [ ] Two trivial theorems (`statement_shape`, `m_polynomial_in_n`) proven without `sorry`.
- [ ] **No claim** that `Theorem1ConstructibleInPolyTime` is actually `True` for any specific `(n, ε)`. The Prop is left as a literature reference.
- [ ] Module doc-comment must say: *"This module captures AM 2025 Theorem 1 as a typed surface. The existence claim is encoded as `Theorem1ConstructibleInPolyTime` but is not proven here."*

### Operator verification

```bash
lake build PnP3 Pnp4
./scripts/check.sh
rg sorry|admit -g"*.lean" pnp3 pnp4
rg "^structure Theorem1Parameters" pnp4/Pnp4/Literature/AtseriasMuller2025/
rg "^structure Theorem1Witness" pnp4/Pnp4/Literature/AtseriasMuller2025/
rg "^def Theorem1ConstructibleInPolyTime" pnp4/Pnp4/Literature/AtseriasMuller2025/
```

---

## Scope

### Allowed

- New module at `pnp4/Pnp4/Literature/AtseriasMuller2025/Theorem1Surface.lean`.
- Importing E01's `Distinguisher` if E01 has landed; otherwise define a local placeholder structure with the right shape.
- One `Glob.one` entry in `lakefile.lean`.
- Test surface + axiom audit per universal acceptance.

### Forbidden

- ❌ No `axiom Theorem1ConstructibleInPolyTime` — the existence remains a Prop, not an asserted axiom.
- ❌ No proof that AM 2025 Theorem 1 is true (out of scope; multi-month).
- ❌ No claim that this implies any unconditional lower bound.
- ❌ All universal forbiddens (see COMMON §3).

---

## Notes

- If E01 hasn't landed when you start, define a local `Distinguisher_local` structure with the same shape, and add a comment marking it as "to be replaced with E01's import once that lands". The operator will handle the integration.
- Be precise about whether `ε` is `Rat` or `Real`. Pick `Rat` for Lean compatibility; document if AM 2025 actually requires `Real` and what that gap means.
- The `Theorem1Witness` should be a `structure`, not a `def`. This makes downstream pattern-matching cleaner.

---

## Output

Use universal template from COMMON §12.
