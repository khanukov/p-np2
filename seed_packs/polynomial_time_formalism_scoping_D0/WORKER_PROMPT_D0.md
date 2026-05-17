# Worker prompt — polynomial-time formalism scoping D0

## Branch

`main`

## Task

Produce the D0 scoping report for the seed pack:

```text
seed_packs/polynomial_time_formalism_scoping_D0/
```

This is markdown-only.  Do not write Lean code.

## Required reading

Read these files before writing the report:

- `RESEARCH_CONSTITUTION.md`
- `seed_packs/first_move_search_2026/reports/fp3b_epoch_strategic_retrospective_claudeopus.md`
- `seed_packs/source_search_contract_expansion_R1B2_runtime_serialization_budget/reports/R1B2_runtime_budget_gpt55.md`
- `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageRuntime.lean`
- `pnp3/Complexity/Interfaces.lean`
- `pnp3/Complexity/PsubsetPpolyInternal/**`
- `pnp4/Pnp4/Frontier/ContractExpansion/C_DAG_Adapter.lean`
- `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguage.lean`
- `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageNP.lean`
- `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageRuntime.lean`

## Context

The FP3b + contract-expansion retrospective recommends stopping R1-cadence dispatches.  R1-A/B/B1/B2/B2a landed useful infrastructure, but the remaining blocker is architectural: the repo lacks a pnp4 polynomial-time formalism that can bridge local parser/codec/runtime facts to the canonical pnp3 `ComplexityInterfaces.NP` / `NP_TM`.

D0 is not an implementation task.  It is a scope and route decision for whether to invest in that formalism layer.

## Central question

Can the repository build a minimal polynomial-time formalism sufficient to prove:

```text
PrefixExtensionLanguage ∈ NP
```

from local runtime facts, without modifying trust roots and without faking runtime proofs?

## Deliverable

Write exactly one markdown report:

```text
seed_packs/polynomial_time_formalism_scoping_D0/reports/D0_polynomial_time_formalism_<HANDLE>.md
```

Use your handle in place of `<HANDLE>`.

## Required report contents

The report must include:

1. A short verdict, choosing exactly one of:
   - `GREEN-light_formalism_investment`
   - `RED-light_too_large_or_wrong_layer`
   - `INCONCLUSIVE_needs_external_literature_or_tooling`
2. A map of the existing interfaces relevant to `PrefixExtensionLanguage ∈ NP`.
3. The smallest plausible polynomial-time formalism layer, if any.
4. A list of concrete obligations that would still need proofs after that layer exists.
5. A trust-root safety check explaining why the plan does not edit pnp3 core semantics.
6. A fake-proof risk check explaining how the plan avoids replacing runtime with `True`, promises, or noncomputable shortcuts.
7. A recommendation for whether R1-C should remain forbidden, remain blocked pending this formalism, or be retired.

## Forbidden scope

- No Lean code.
- No pnp3 trust-root edits.
- No source theorem.
- No `gap_from`.
- No `ResearchGapWitness`.
- No endpoint.
- No R1-C.
- No P≠NP claim.

## Allowed scope

Only write the D0 markdown report under `reports/`.  Do not modify Lean files.

## Commands

Run:

```sh
./scripts/check.sh
```

## Output format

End your response with:

```text
Task: polynomial-time formalism D0 report
Commit before:
Commit after:
Changed files:
D0 only: yes/no
No implementation: yes/no
Commands run:
Scope violations:
```
