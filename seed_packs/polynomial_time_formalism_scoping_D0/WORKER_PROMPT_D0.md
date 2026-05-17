# Worker prompt — polynomial-time formalism scoping D0

## Branch

`main`

## Task

Write the D0 scoping report for a minimal pnp4 polynomial-time formalism that could bridge local `PrefixExtensionLanguage` parser/codec/runtime facts to canonical pnp3 `ComplexityInterfaces.NP` / `NP_TM`.

This is markdown-only.  Do not write Lean code.

## Classification

Infrastructure scoping.  This does not reduce `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`, and it must not be reported as P-vs-NP mainline progress.

## Required reading

Read before writing the report:

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

## Central question

Can the repository build a minimal polynomial-time formalism sufficient to prove:

```text
PrefixExtensionLanguage ∈ NP
```

from local runtime facts, without modifying trust roots and without faking runtime proofs?

## Deliverable

Create exactly one markdown report:

```text
seed_packs/polynomial_time_formalism_scoping_D0/reports/D0_polynomial_time_formalism_<HANDLE>.md
```

Use your own handle in `<HANDLE>`.

## Report requirements

Your report must include:

1. **Verdict** — choose exactly one:
   - `GREEN-light_formalism_investment`
   - `RED-light_too_large_or_wrong_layer`
   - `INCONCLUSIVE_needs_external_literature_or_tooling`
2. **Evidence from required reading** — identify the existing local facts, the pnp3 `NP_TM` target, and the exact missing bridge.
3. **Minimal interface sketch** — if green or inconclusive, describe the smallest formalism that would be worth implementing later.  Keep this at the design level; do not write Lean code.
4. **Trust-root assessment** — explain why the proposed next step does or does not require changing frozen pnp3 trust roots.
5. **Runtime honesty check** — explain how the plan avoids replacing real runtime proofs with opaque `Prop` placeholders.
6. **Next authorised pack shape** — if any next pack is recommended, describe it as a future explicitly authorised pack, not as R1-C and not as implementation inside this D0 report.

## Forbidden scope

- No Lean code.
- No pnp3 trust-root edits.
- No source theorem.
- No `gap_from`.
- No `ResearchGapWitness`.
- No endpoint.
- No R1-C.
- No P≠NP claim.
- Do not claim that `PrefixExtensionLanguage ∈ NP` has already been proved.
- Do not introduce new files outside the single report unless you are recording a failure note under `failures/` because the D0 report could not be completed.

## Allowed scope

- One D0 markdown report under `reports/`.
- If the report cannot be completed, one markdown failure note under `failures/` explaining why.

## Commands

Run:

```bash
./scripts/check.sh
```

## Output format

End your response with:

```text
Task: polynomial-time formalism D0 skeleton
Commit before: <hash>
Commit after: <hash>
Changed files:
- <path>
D0 only: yes/no
No implementation: yes/no
Commands run:
- <command> => <result>
Scope violations: <none or list>
```
