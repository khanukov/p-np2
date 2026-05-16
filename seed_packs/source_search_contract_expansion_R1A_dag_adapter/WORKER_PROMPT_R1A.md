# Worker Prompt — R1-A DAG Adapter Only

Branch: `main`

Task: limited Round 1 seed pack execution for R1-A only.

Seed pack:

```text
seed_packs/source_search_contract_expansion_R1A_dag_adapter/
```

This is not full Round 1. Only R1-A is authorised.

Do not start R1-B or R1-C. R1-B/R1-C are gated until R1-A lands and receives
operator review.

## Progress classification

Infrastructure / interface alignment.

Do not report this task as unconditional progress toward `P != NP`. R1-A only
stages an adapter between pnp4 circuit-family interfaces and the frozen pnp3 DAG
circuit endpoint.

## Required reading

Read these files before editing:

- `RESEARCH_CONSTITUTION.md`
- `seed_packs/source_search_contract_expansion_D0/README.md`
- `seed_packs/source_search_contract_expansion_D0/reports/D0_contract_expansion_gpt55.md`
- `seed_packs/source_search_contract_expansion_D0/reports/D0_1_interface_alignment_gpt55.md`
- `pnp4/Pnp4/Frontier/SearchMCSPMagnification.lean`
- `pnp4/Pnp4/Frontier/CompressionMagnification.lean`
- `pnp4/Pnp4/AlgorithmsToLowerBounds/BridgeToPpolyDAG.lean`
- `pnp3/Complexity/Interfaces.lean`
- `pnp3/Magnification/UnconditionalResearchGap.lean`

## Authorised target

Define or propose the pnp4 DAG class wrapper:

```lean
C_DAG : CircuitFamilyClass
```

with exactly the frozen pnp3 DAG circuit components:

```lean
Family n := Pnp3.ComplexityInterfaces.DagCircuit n
eval := Pnp3.ComplexityInterfaces.DagCircuit.eval
size := Pnp3.ComplexityInterfaces.DagCircuit.size
```

Then prove or stage alignment between polynomially bounded `C_DAG` families and
pnp3 `PpolyDAG` / `InPpolyDAG`, targeting names of this shape:

```lean
C_DAG_family_to_InPpolyDAG
InPpolyDAG_to_C_DAG_family
PpolyDAG_decider_as_C_DAG_decider
```

The exact type signatures may be adjusted to fit the existing pnp4 interfaces,
but they must preserve the frozen pnp3 semantics and size measure.

## Outcome A — theorem/skeleton landed

Prefer landing a small Lean module:

```text
pnp4/Pnp4/Frontier/ContractExpansion/C_DAG_Adapter.lean
```

If the normal pnp4 path is too risky, land an audit-only module instead:

```text
pnp4/Pnp4/Frontier/ContractExpansion/C_DAG_Adapter_Audit.lean
```

The module should contain:

- `C_DAG`
- alignment definitions
- at least one proved direction if possible
- if the full proof is too hard, precise theorem statements plus a structured
  failure report under this seed pack

Keep any new pnp4 module listed in `lakefile.lean` if required by the repository
module policy.

Update the public theorem-surface and axiom-audit tests if and only if the work
adds new public theorem surfaces requiring those audits.

## Outcome B — structured failure

If R1-A cannot safely land a Lean module, write a structured failure report:

```text
seed_packs/source_search_contract_expansion_R1A_dag_adapter/failures/R1A_<HANDLE>.md
```

The report must include:

- attempted module path;
- exact definitions or theorem statements attempted;
- import or namespace blockers;
- proof blockers, with the missing lemma or mismatch stated precisely;
- whether the blocker requires operator permission to touch a forbidden file;
- recommended next action for operator review.

## Forbidden scope

No edits to:

- `pnp3/Complexity/Interfaces.lean`
- `pnp3/Magnification/UnconditionalResearchGap.lean`
- `pnp4/Pnp4/AlgorithmsToLowerBounds/BridgeToPpolyDAG.lean` unless operator explicitly permits
- `ResearchGapWitness`
- `NP_not_subset_PpolyDAG`
- `P_ne_NP*`

No:

- `SourceTheorem`
- `gap_from`
- `VerifiedNPDAGLowerBoundSource` construction
- endpoint
- NoGoLog edits
- spec edits
- known_guards edits
- trust-root edits
- FP-4
- `P != NP` / `P≠NP` claim

## Allowed scope

- The R1-A Lean adapter or audit module described above.
- A structured failure report in this seed pack if needed.
- Minimal build-registration/test-surface edits only when required by repository
  policy for a landed module.

Do not modify pnp3 trust-root files.

## Required command

Run:

```sh
./scripts/check.sh
```

## Required worker output

End with this exact report shape:

```text
Task: R1-A seed pack skeleton
Commit before:
Commit after:
Changed files:
R1-A only: yes/no
R1-B/R1-C gated: yes/no
Commands run:
Scope violations:
```
