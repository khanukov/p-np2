# Source Search Contract Expansion R1-A — DAG Adapter

## Status

OPEN — R1-A only.

Full Round 1 is NOT authorised.

R1-B/R1-C are gated until R1-A lands and receives operator review.

## Progress classification

Infrastructure / interface-alignment seed pack.

This seed pack is limited to staging a pnp4 adapter around the frozen pnp3 DAG
circuit interface. It does not claim P-vs-NP mainline progress by itself and it
must not introduce a source theorem, endpoint, or `VerifiedNPDAGLowerBoundSource`.

## Required reading

Before attempting R1-A, read:

- `RESEARCH_CONSTITUTION.md`
- `seed_packs/source_search_contract_expansion_D0/README.md`
- `seed_packs/source_search_contract_expansion_D0/reports/D0_contract_expansion_gpt55.md`
- `seed_packs/source_search_contract_expansion_D0/reports/D0_1_interface_alignment_gpt55.md`
- `pnp4/Pnp4/Frontier/SearchMCSPMagnification.lean`
- `pnp4/Pnp4/Frontier/CompressionMagnification.lean`
- `pnp4/Pnp4/AlgorithmsToLowerBounds/BridgeToPpolyDAG.lean`
- `pnp3/Complexity/Interfaces.lean`
- `pnp3/Magnification/UnconditionalResearchGap.lean`

## Purpose

Define pnp4 `C_DAG` wrapper around frozen pnp3 `DagCircuit`, and prove/stage the
alignment statement between:

- polynomially bounded C_DAG families;
- pnp3 PpolyDAG / InPpolyDAG.

## R1-A authorised target

1. Define or propose:

```lean
C_DAG : CircuitFamilyClass
```

with:

```lean
Family n := Pnp3.ComplexityInterfaces.DagCircuit n
eval := Pnp3.ComplexityInterfaces.DagCircuit.eval
size := Pnp3.ComplexityInterfaces.DagCircuit.size
```

2. Prove or stage:

```lean
C_DAG_family_to_InPpolyDAG
InPpolyDAG_to_C_DAG_family
PpolyDAG_decider_as_C_DAG_decider
```

3. No endpoint, no source theorem, no VerifiedNPDAGLowerBoundSource.

## Explicit non-goals

R1-A must not construct or modify:

- `SourceTheorem`
- `gap_from`
- `VerifiedNPDAGLowerBoundSource`
- `ResearchGapWitness`
- `NP_not_subset_PpolyDAG`
- any `P_ne_NP*` theorem or claim

R1-A must not edit route-policy, no-go, guardrail, trust-root, or FP-4 files.

## Success criteria

A successful R1-A worker result is either:

- a small Lean adapter/audit module that introduces the `C_DAG` wrapper and
  lands at least one safe alignment direction, with precise remaining theorem
  statements for any unproved directions; or
- a structured failure report explaining the exact interface blocker and the
  minimal follow-up needed for operator review.

In both cases, R1-A remains a gated interface-alignment task only.
