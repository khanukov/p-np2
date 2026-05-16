# Worker prompt — R1-B2a runtime-aware codec / parser

## Branch

`main`

## Task

Attempt the limited R1-B2a runtime-aware codec/parser seed pack only.

This is not R1-C. Only R1-B2a is authorised. R1-C remains gated.
Do not claim full contract expansion.

## Classification

Classify this attempt as Infrastructure / contract-expansion staging unless it
directly reduces `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`.
Do not report runtime-aware parser or codec scaffolding as a P-vs-NP endpoint.

## Required reading

Read before editing:

- `RESEARCH_CONSTITUTION.md`
- R1-B2:
  - `seed_packs/source_search_contract_expansion_R1B2_runtime_serialization_budget/README.md`
  - `seed_packs/source_search_contract_expansion_R1B2_runtime_serialization_budget/WORKER_PROMPT_R1B2.md`
  - `seed_packs/source_search_contract_expansion_R1B2_runtime_serialization_budget/reports/R1B2_runtime_budget_gpt55.md`
- R1-B1:
  - `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageNP.lean`
  - `seed_packs/source_search_contract_expansion_R1B1_parser_codec_budget/reports/R1B1_operator_review_claudeopus.md`
- R1-B:
  - `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguage.lean`
  - `seed_packs/source_search_contract_expansion_R1B_prefix_language/reports/R1B_operator_review_claudeopus.md`
- Core files:
  - `pnp4/Pnp4/Frontier/SearchMCSPMagnification.lean`
  - `pnp4/Pnp4/Frontier/SearchMCSPConcreteTargets.lean`
  - `pnp4/Pnp4/Frontier/CompressionMagnification.lean`
  - `pnp3/Complexity/Interfaces.lean`

## Context

R1-B2 resolved the key runtime distinction:

- truth-table verification is exponential in target parameter `n`;
- but can be polynomial in ambient input length `M(n)` if `M(n)` includes
  `tableLen n`.

The current repo still lacks concrete `M(n)`, a concrete parser, codec
witness-length bounds, decode runtime bounds, threshold bounds in `M(n)`, and a
bridge from local runtime facts to `NP_TM`.

## Central R1-B2a question

Can we define a runtime-aware tree-circuit codec/parser interface with enough
explicit arithmetic/runtime fields to make the eventual
`PrefixExtensionLanguage_in_NP` theorem meaningful, without claiming it yet?

## Authorised outcomes

Produce exactly one of the following outcomes.

### Outcome A — Lean/audit module landed

Preferred path:

```text
pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageRuntime.lean
```

Expected contents:

- ambient length convention;
- `tableLen_le_M` lemma;
- runtime-aware codec/parser records;
- do **not** prove `PrefixExtensionLanguage_in_NP`;
- do **not** prove any NP-membership theorem;
- keep R1-C gated even if all local fields are staged.

If Lean is premature, you may instead write a markdown+Lean audit report under:

```text
seed_packs/source_search_contract_expansion_R1B2a_runtime_aware_codec_parser/reports/R1B2a_<HANDLE>.md
```

The report must include the proposed Lean shape and must clearly separate proved
facts from staged obligations.

### Outcome B — structured failure

If R1-B2a cannot honestly land, write a structured failure report:

```text
seed_packs/source_search_contract_expansion_R1B2a_runtime_aware_codec_parser/failures/R1B2a_<HANDLE>.md
```

The failure report must identify the exact blocker, choosing at least one of:

- no polynomial-time formalism;
- codec too abstract;
- parser serialization cannot be fixed locally;
- witnessBits bound unavailable.

It must distinguish blockers in target parameter `n` from blockers in ambient
input length `M(n)`.

## Required staged interface pieces for Outcome A

### A. Ambient length convention

Define/stage:

```lean
TreeMCSPPrefixAmbientLength
```

with fields or parameters:

- `overhead`
- `witnessBits`
- `padBits`
- `tableLen` component

and prove/stage:

```lean
tableLen_le_M
```

### B. Runtime-aware codec refinement

Define/stage a runtime-aware codec refinement, for example:

```lean
RuntimeAwareTreeCircuitCodec
```

or similar, extending / wrapping `TreeCircuitWitnessCodec` with fields:

- `witnessBits_poly_in_M`
- `decode_polynomial_time_in_M`
- `threshold_poly_in_M`
- `circuit_eval_polynomial_time_in_size`
- `truth_table_lookup_polynomial_time_in_M`

### C. Parser runtime record

Define/stage a parser runtime record, for example:

```lean
RuntimeAwarePrefixParser
```

or similar, with:

- concrete parse or parser obligations
- `parser_polynomial_time_in_M`
- malformed-input soundness
- length convention soundness

## Explicit non-goals

- No extraction theorem.
- No `PpolyDAG L → BoundedSearchSolver`.
- No `target.noBoundedSolver`.
- No `VerifiedNPDAGLowerBoundSource`.
- No `ResearchGapWitness`.
- No endpoint.
- No R1-C.
- No `SourceTheorem` / `gap_from`.
- No P≠NP claim.

## Allowed scope

Only:

- `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageRuntime.lean`
  if producing Outcome A in Lean;
- reports under
  `seed_packs/source_search_contract_expansion_R1B2a_runtime_aware_codec_parser/reports/`;
- failures under
  `seed_packs/source_search_contract_expansion_R1B2a_runtime_aware_codec_parser/failures/`;
- minimal tests/audit registrations required by the repository if and only if a
  Lean module is added.

## Forbidden

- No Lean code outside the authorised Outcome A path.
- No lakefile changes unless a Lean module is actually added and the repository
  requires registration.
- No JSONL edits.
- No spec edits.
- No trust-root edits.
- No `SourceTheorem`.
- No `gap_from`.
- No `ResearchGapWitness`.
- No endpoint.
- No P≠NP claim.
- No R1-C.

## Commands

Run:

```bash
./scripts/check.sh
```

If a Lean module is added, also run the narrowest relevant Lean build/test
commands and document them in the output report.

## Output format

End your worker response with:

```text
Task: R1-B2a seed pack skeleton
Commit before: <hash>
Commit after: <hash>
Changed files:
- <path>
R1-B2a only: yes/no
R1-C gated: yes/no
Commands run:
- <command> — <result>
Scope violations: <none or details>
```
