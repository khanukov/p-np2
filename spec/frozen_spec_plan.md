# Frozen Spec — implementation plan for `pnp3/Spec/FrozenSpec.lean`

This document describes the planned `FrozenSpec` module. It is **not** yet
implemented; implementing it is a Foundational PR (Rule 0 in
`RESEARCH_CONSTITUTION.md`) and must not be combined with cleanup or
candidate work.

The purpose of `FrozenSpec` is to give the trust root a second,
independently-stated reference semantics that can be checked against the
current `ComplexityInterfaces` definitions via equivalence theorems. This
guards against silent drift in the active definitions.

---

## 1. Trust-root constraints

`pnp3/Spec/FrozenSpec.lean` must:

- import the smallest possible set of modules,
- not import `pnp3/Magnification/`,
- not import `pnp3/LowerBounds/`,
- not import `pnp3/ThirdPartyFacts/`,
- avoid importing `pnp3/Complexity/PsubsetPpolyInternal/` if at all possible,
- be self-contained at the level of definitions (no aliases that immediately
  unfold to active code).

**Known trust-root vulnerability (must be recorded explicitly):**
`ComplexityInterfaces.P` currently delegates to
`Internal.PsubsetPpoly.Complexity.P`. As a consequence,
`pnp3/Complexity/PsubsetPpolyInternal/` is **part of the current trust
root**. The `FrozenSpec` PR must either:

1. give `P_ref` a fresh, independent definition and prove
   `P_matches_ref` against the active definition, or
2. document precisely which `PsubsetPpolyInternal` files are part of the
   trust root and freeze their hashes in `spec/target.toml::[frozen_files]`.

Option (1) is preferred because it removes the silent dependency.

---

## 2. Reference definitions

`FrozenSpec.lean` will introduce, at minimum, the following references:

- `FrozenSpec.P_ref`
- `FrozenSpec.NP_ref`
- `FrozenSpec.PpolyDAG_ref`
- `FrozenSpec.PpolyFormula_ref`
- `FrozenSpec.NP_not_subset_PpolyDAG_ref`
- `FrozenSpec.P_ne_NP_ref`
- `FrozenSpec.ResearchGapWitness_ref`
- `FrozenSpec.FormulaCircuit_size_ref`
- `FrozenSpec.DagCircuit_size_ref`

Each reference is defined from first principles (Turing machines / circuit
families / size measures) without going through `ComplexityInterfaces`.
This is what makes the file an independent semantics, not a wrapper.

---

## 3. Equivalence theorems

The PR must provide and prove (or, if a proof is structurally infeasible,
explicitly mark `human-review-required`) the following equivalences:

```
theorem P_matches_ref :
  ∀ L, ComplexityInterfaces.P L ↔ FrozenSpec.P_ref L

theorem NP_matches_ref :
  ∀ L, ComplexityInterfaces.NP L ↔ FrozenSpec.NP_ref L

theorem PpolyDAG_matches_ref :
  ∀ L, ComplexityInterfaces.PpolyDAG L ↔ FrozenSpec.PpolyDAG_ref L

theorem PpolyFormula_matches_ref :
  ∀ L, ComplexityInterfaces.PpolyFormula L ↔ FrozenSpec.PpolyFormula_ref L

theorem NP_not_subset_PpolyDAG_matches_ref :
  ComplexityInterfaces.NP_not_subset_PpolyDAG ↔
  FrozenSpec.NP_not_subset_PpolyDAG_ref

theorem P_ne_NP_matches_ref :
  ComplexityInterfaces.P_ne_NP ↔ FrozenSpec.P_ne_NP_ref

theorem ResearchGapWitness_matches_ref :
  Nonempty ResearchGapWitness ↔ Nonempty FrozenSpec.ResearchGapWitness_ref
```

If an equivalence cannot be closed in one PR, the unproved direction must
be carved out as an explicit `theorem` with a `sorry`-free hypothesis (e.g.
`P_ref_subset_P : ∀ L, FrozenSpec.P_ref L → ComplexityInterfaces.P L`)
flagged in `human-review-required`. The PR must not be merged with `sorry`
in the spec.

---

## 4. Verifier integration

After `FrozenSpec.lean` lands:

- `spec/target.toml::[frozen_files]` is updated to include
  `pnp3/Spec/FrozenSpec.lean`.
- The verifier checks that every claim of the form
  `theorem ... : ComplexityInterfaces.P_ne_NP` is matched by a closed
  inhabitant of `FrozenSpec.P_ne_NP_ref` via `P_ne_NP_matches_ref`.
- The verifier hashes `FrozenSpec.lean`. Mismatch with the hash recorded
  for the candidate's `attack_suite_version` triggers Rule 14 revalidation.

---

## 5. What this PR does **not** do

- It does **not** introduce candidates.
- It does **not** modify `ComplexityInterfaces.lean` (those are separate
  Foundational PRs).
- It does **not** prove `P ≠ NP` or `NP_not_subset_PpolyDAG`.
- It does **not** add typeclasses, providers, or facts.

---

## 6. Acceptance criteria for the FrozenSpec PR

1. New file `pnp3/Spec/FrozenSpec.lean` exists.
2. All named references in §2 exist.
3. All equivalence theorems in §3 are stated, and each is either proved or
   carved out as an explicit `human-review-required` theorem (no `sorry`).
4. The file imports nothing from `Magnification/`, `LowerBounds/`, or
   `ThirdPartyFacts/`.
5. `spec/target.toml::[frozen_files]` lists the new file.
6. The verifier's frozen-hash check passes.
7. The PR is tagged `foundational` and contains no other scope.
