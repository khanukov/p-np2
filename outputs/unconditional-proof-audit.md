# Audit: what currently blocks unconditional recognition of the proof

Date: 2026-03-26

## Bottom line

The repository **does not currently contain an unconditional theorem `P ≠ NP`**.

The decisive blocker is not `axiom`/`sorry` hygiene: those are clean in `pnp3/`.
The blocker is that the final `P ≠ NP` endpoint still takes an **explicit external hypothesis**
`hNPDag : NP_not_subset_PpolyDAG`, and the project docs state the same boundary.

## What I checked

### Build / hygiene

Ran:

```bash
cd /root/p-np2 && ./scripts/check.sh
```

Observed:

- build completed successfully;
- source hygiene scan reported:
  - `Axiom inventory OK (0 axioms)`
  - `Proof hole scan OK (no sorry/admit)`;
- axiom surface dump still reports dependence on standard Lean assumptions
  `propext`, `Classical.choice`, `Quot.sound`.

### Final theorem signatures

Inspected `pnp3/Magnification/FinalResult.lean`.

The active endpoint is explicitly conditional:

```lean
theorem P_ne_NP_final_dag_only
  (hNPDag : ComplexityInterfaces.NP_not_subset_PpolyDAG) :
  ComplexityInterfaces.P_ne_NP := by
```

and the public wrapper is also conditional:

```lean
theorem P_ne_NP_final
  (hMag : MagnificationAssumptions)
  (hNPDag : ComplexityInterfaces.NP_not_subset_PpolyDAG) :
  ComplexityInterfaces.P_ne_NP := by
```

So the repository proves only:

```text
if NP ⊄ PpolyDAG, then P ≠ NP
```

not an unconditional `P ≠ NP`.

## Exact blocker

The missing theorem is an **internal proof of `NP_not_subset_PpolyDAG`**.

This is stated consistently in:

- `README.md`
- `STATUS.md`
- `PROOF_OVERVIEW.md`
- `CHECKLIST_UNCONDITIONAL_P_NE_NP.md`
- `pnp3/Docs/Unconditional_NP_not_subset_PpolyDAG_Plan.md`

The plan document says the current mathematical blocker is exactly:

> construct `dagStableRestrictionInvariantProvider p` from strict DAG semantics
> (without additional bridge assumptions).

## More detailed diagnosis

### 1. Inclusion side is not the blocker anymore

The repo claims the inclusion side is already closed:

- `proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG`

and `P_ne_NP_final_dag_only` uses that internal inclusion theorem.
So the old issue “you still need to show `P ⊆ P/poly-DAG`” is **not** the current blocker.

### 2. Formula-side separation is not enough for unconditional `P ≠ NP`

There are formula/real separation endpoints:

- `NP_not_subset_PpolyFormula_final*`
- `NP_not_subset_PpolyReal_final*`

but the file itself says that AC0/magnification assumptions live on a separate route
**until an explicit bridge to DAG separation is formalized**.

So even if the formula route is internally wired, it does **not** by itself close
unconditional `P ≠ NP` in the present architecture.

### 3. The DAG route exists only as a conditional interface

There are strong-looking wrappers such as:

- `NP_not_subset_PpolyDAG_final_of_dag_stableRestriction_TM`
- `NP_not_subset_PpolyDAG_final_of_certificateProvider_TM`
- `NP_not_subset_PpolyDAG_final_of_invariantProvider_TM`
- `P_ne_NP_final_of_*`

But each of these still requires one of the following external producer inputs:

- a stable-restriction theorem for every DAG solver;
- a certificate provider;
- an invariant provider;
- or a `DAG → Formula` bridge.

These are **interfaces for the missing mathematics**, not completion of that mathematics.

### 4. The remaining gap is mathematical, not just plumbing

`pnp3/LowerBounds/DAGStableRestrictionProducer.lean` defines the source-side objects:

- `DAGStableRestrictionCertificate`
- `dagStableRestrictionCertificateProvider`
- `DAGStableRestrictionInvariantPackage`
- `dagStableRestrictionInvariantProvider`

and proves that **if** such data exists, then the lower-bound stack yields
`NP_not_subset_PpolyDAG`.

What is still missing is a theorem constructing those objects from strict DAG semantics.
That is why the project can honestly claim “conditional wrappers are in place” but not
“unconditional proof completed”.

## Secondary caveat

Even after removing project-local assumptions, the current theorem surface still depends on
standard Lean axioms reported by `#print axioms`:

- `propext`
- `Classical.choice`
- `Quot.sound`

This is **not** the main reason the result is not unconditional in the project’s own sense;
its docs explicitly distinguish “no project-local axioms” from “unconditional `P ≠ NP`”.
But if someone demands a fully constructive/foundation-minimal result, this is still a
separate caveat.

## What would have to become true before calling it unconditional

At minimum, all of the following must happen:

1. Prove `ComplexityInterfaces.NP_not_subset_PpolyDAG` inside the repo, with no external DAG-side hypothesis.
2. Remove `hNPDag` from `P_ne_NP_final*` wrappers.
3. Ensure the proof uses the existing consumer stack rather than another ad hoc endpoint.
4. Update status docs so they all state unconditional status consistently.

## Verdict

### What is already strong

- The active tree builds.
- `pnp3/` has no project-local `axiom` declarations.
- `pnp3/` has no `sorry`/`admit`.
- The final route is documented honestly.
- The remaining open boundary is localized fairly precisely.

### What prevents unconditional recognition right now

**One explicit missing theorem:** internal DAG-side separation `NP_not_subset_PpolyDAG`.

Equivalently: the repository currently formalizes a conditional implication
from DAG nonuniform separation to `P ≠ NP`, but it does **not** yet formalize the DAG
nonuniform separation itself.

## Evidence paths

- `pnp3/Magnification/FinalResult.lean`
- `pnp3/LowerBounds/DAGStableRestrictionProducer.lean`
- `STATUS.md`
- `CHECKLIST_UNCONDITIONAL_P_NE_NP.md`
- `PROOF_OVERVIEW.md`
- `pnp3/Docs/Unconditional_NP_not_subset_PpolyDAG_Plan.md`
