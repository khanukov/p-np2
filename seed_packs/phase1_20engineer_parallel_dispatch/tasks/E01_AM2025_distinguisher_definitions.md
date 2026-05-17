# E01: AM 2025 Distinguisher structure + weight + sparsity

**Engineer:** E01
**Phase:** A — Literature formalization
**Estimated time:** 2 weeks
**Difficulty:** medium
**Dependencies:** none (independent of all other tasks)

---

## Goal

Formalize the **definition** of an `(n,m,ε,δ)`-distinguisher matrix from Atserias-Müller 2025 (arXiv:2503.24061) as a Lean structure, with its weight and sparsity invariants. Prove 2-3 basic structural lemmas (sparsity preserved under transpose, weight is bounded, etc.). **Do not** prove existence theorems (those are E02).

---

## Source material

* **Paper:** Albert Atserias, Moritz Müller, "Simple general magnification of circuit lower bounds", arXiv:2503.24061, 2025.
* **Verifiable identifier:** arXiv:2503.24061; DOI 10.48550/arXiv.2503.24061.
* **Specific definition:** §1 / §2 Definition immediately before Theorem 1. An `(n,m,ε,δ)`-distinguisher is a binary `n × m` matrix `D` such that, for all `x, y ∈ {0,1}^n` with `d_H(x,y) ≥ εn`, we have `d_H(xD, yD) ≥ δm`. **Weight** is the maximum Hamming weight of a column of `D`.

---

## Deliverable

### Lean module

```
pnp4/Pnp4/Literature/AtseriasMuller2025/DistinguisherDefinitions.lean
```

### Expected signatures

```lean
namespace Pnp4
namespace Literature
namespace AtseriasMuller2025

/-- An `(n,m,ε,δ)`-distinguisher matrix per AM 2025 §2.
    Matrix is `n × m` binary; ε, δ are rationals in (0,1]. -/
structure Distinguisher (n m : Nat) (ε δ : Rat) where
  matrix : AlgorithmsToLowerBounds.BitVec n → AlgorithmsToLowerBounds.BitVec m
  -- Linear/code-shaped: actual implementation as a Bool matrix
  M : Fin n → Fin m → Bool
  matrix_via_M : ∀ x : AlgorithmsToLowerBounds.BitVec n,
                   ∀ j : Fin m, matrix x j = ...
  -- Distinguisher property: far inputs have far images
  distinguishes :
    ∀ x y : AlgorithmsToLowerBounds.BitVec n,
      farEnough ε n x y → farEnough δ m (matrix x) (matrix y)

/-- Hamming weight of a column. -/
def columnWeight (n m : Nat) (M : Fin n → Fin m → Bool) (j : Fin m) : Nat := ...

/-- Maximum column weight = AM's `weight(D)`. -/
def maxColumnWeight (n m : Nat) (M : Fin n → Fin m → Bool) : Nat := ...

/-- Sparsity predicate: max column weight ≤ w. -/
def IsSparse (n m w : Nat) (M : Fin n → Fin m → Bool) : Prop :=
  ∀ j : Fin m, columnWeight n m M j ≤ w

/-- Hamming distance helper (rational-radius version). -/
def farEnough (ε : Rat) (n : Nat) (x y : AlgorithmsToLowerBounds.BitVec n) : Prop := ...
```

### Lemmas to prove

```lean
/-- A sparse matrix has bounded total weight. -/
theorem totalWeight_le (n m w : Nat) (M : Fin n → Fin m → Bool) 
    (hSparse : IsSparse n m w M) :
    (∑ j, columnWeight n m M j) ≤ m * w

/-- The all-zero matrix is sparse for any w. -/
theorem zero_isSparse (n m w : Nat) : 
    IsSparse n m w (fun _ _ => false)

/-- Sparsity preserved under permutation of rows. -/
theorem sparse_permute_rows (n m w : Nat) (M : Fin n → Fin m → Bool)
    (σ : Equiv.Perm (Fin n)) (hSparse : IsSparse n m w M) :
    IsSparse n m w (fun i j => M (σ i) j)
```

---

## Acceptance criteria

### Universal (see COMMON_WORKER_INSTRUCTIONS.md §4)

- [ ] `lake build PnP3 Pnp4` green.
- [ ] `./scripts/check.sh` green.
- [ ] `rg sorry|admit` empty across pnp3, pnp4.
- [ ] No trust-root edits.
- [ ] `lakefile.lean` has one new `Glob.one` line for this module.
- [ ] Smoke test wrappers in `pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean`.
- [ ] `#print axioms` entries for the three lemmas in `pnp4/Pnp4/Tests/AxiomsAudit.lean`.
- [ ] Module doc-comment honestly describes scope.

### Task-specific

- [ ] `Distinguisher` structure defined with exactly the fields specified above (field order may vary; names must match).
- [ ] `columnWeight`, `maxColumnWeight`, `IsSparse`, `farEnough` defined with exactly the names specified.
- [ ] All three lemmas `totalWeight_le`, `zero_isSparse`, `sparse_permute_rows` proven kernel-clean.
- [ ] **No `Classical.choose`** anywhere in this file. All proofs constructive.
- [ ] At least one example: explicitly construct a `Distinguisher 2 2 (1/2) (1/2)` (the identity matrix) and verify properties via `decide` or short proof.

### Verification commands the operator will run

```bash
# Build and check
lake build PnP3 Pnp4
./scripts/check.sh
rg -n "\bsorry\b|\badmit\b" -g"*.lean" pnp3 pnp4

# Specific signature checks
rg "^structure Distinguisher" pnp4/Pnp4/Literature/AtseriasMuller2025/
rg "^def maxColumnWeight" pnp4/Pnp4/Literature/AtseriasMuller2025/
rg "^theorem totalWeight_le" pnp4/Pnp4/Literature/AtseriasMuller2025/
rg "^theorem zero_isSparse" pnp4/Pnp4/Literature/AtseriasMuller2025/
rg "^theorem sparse_permute_rows" pnp4/Pnp4/Literature/AtseriasMuller2025/

# Classical.choose audit
rg "Classical\." pnp4/Pnp4/Literature/AtseriasMuller2025/DistinguisherDefinitions.lean
# expected: no output
```

---

## Scope

### Allowed

- New module at `pnp4/Pnp4/Literature/AtseriasMuller2025/DistinguisherDefinitions.lean`.
- One `Glob.one` entry in `lakefile.lean`.
- Test surface in `pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean`.
- Axiom audit in `pnp4/Pnp4/Tests/AxiomsAudit.lean`.
- Reading any existing file in the repo.
- Importing pnp3 / pnp4 trust-root types via `import`.

### Forbidden

See COMMON §3. Specific reminders for E01:

- ❌ No theorem of existence of distinguishers (that's E02).
- ❌ No specific bounds like `m ≤ n^7` (that's E02).
- ❌ No `Classical.choose`.
- ❌ No claim that AM 2025 implies any specific lower bound.
- ❌ No edits to `pnp3/Complexity/Interfaces.lean` or any trust-root file.

---

## Notes

- The rationale for `Rat` for `ε`, `δ`: AM 2025 uses real numbers, but `Rat` is sufficient for all theorem statements and Lean-friendly. If you need `Real`, document the choice in caveats.
- For `farEnough`, choose a formulation that aligns with Mathlib's existing Hamming distance API. If Mathlib doesn't have one for `Fin n → Bool`, define a local helper and prove it equivalent.
- The `matrix_via_M` field is the "extensional view": each output bit is a parity over the corresponding column. Pick a clear computational definition.
- 2-week estimate assumes you spend ~3 days reading AM 2025 §1-2, ~5 days writing Lean, ~2 days proving the three lemmas, ~2 days polishing.

---

## Honest caveats (worker should fill these in)

- Document any place where the Lean definition is more general or more restrictive than AM's literal definition.
- Document the `Rat` vs `Real` choice.
- Document any Mathlib lemmas you depend on that have non-obvious axiom surfaces.

---

## Output (PR description template)

Use the universal template from COMMON §12. Replace `<NN>` with `01` and `<title>` with "AM 2025 Distinguisher structure + weight + sparsity".
