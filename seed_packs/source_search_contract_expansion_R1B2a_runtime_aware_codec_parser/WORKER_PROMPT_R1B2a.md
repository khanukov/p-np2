# Worker prompt — R1-B2a runtime-aware codec/parser interface

## Branch

`main`

## Task

Create a limited seed-pack attempt for R1-B2a only.

This is not R1-C. Only R1-B2a is authorised. R1-C remains gated.
Full contract expansion is not authorised.

## Classification

Classify this attempt as Infrastructure / contract-expansion staging unless it
directly reduces `SearchMCSPWeakLowerBound` or
`VerifiedNPDAGLowerBoundSource`.

Do not report runtime-interface staging, restricted lower-bound work, or parser
cleanup as P-vs-NP mainline progress.

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

## Central R1-B2a question

Can we define a runtime-aware tree-circuit codec/parser interface with enough
explicit arithmetic/runtime fields to make the eventual
`PrefixExtensionLanguage_in_NP` theorem meaningful, without claiming it yet?

## Runtime distinction that must be preserved

The R1-B2 distinction is load-bearing:

- truth-table verification is exponential in target parameter `n`;
- truth-table verification may still be polynomial in ambient encoded input
  length `M(n)` if `M(n)` includes `tableLen n`.

Do not replace an `M(n)`-polynomial obligation with an `n`-polynomial one. Do
not claim NP membership from a finite `Decidable` instance alone.

## Authorised deliverables

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
- no NP theorem unless all real fields are discharged.

Recommended names, unless the surrounding API suggests better names:

- `TreeMCSPPrefixAmbientLength`;
- `RuntimeAwareTreeCircuitCodec`;
- `RuntimeAwarePrefixParser`.

The ambient length convention should include or parameterize:

- overhead;
- witness bits;
- pad bits;
- table-length component.

The codec runtime record should expose fields corresponding to:

- witness bits polynomially bounded in `M`;
- decode polynomial time in `M`;
- threshold polynomially bounded in `M`;
- circuit evaluation polynomial time in circuit size;
- truth-table lookup polynomial time in `M`.

The parser runtime record should expose fields corresponding to:

- concrete parse or parser obligations;
- parser polynomial time in `M`;
- malformed-input soundness;
- length convention soundness.

If you add a Lean module, obey all repository requirements for module listing,
surface tests, and axiom audits. Do not add `axiom`, `sorry`, `admit`, or
`native_decide` in active pnp3/pnp4 code.

### Outcome B — structured failure

If R1-B2a cannot honestly land, write a structured failure report:

```text
seed_packs/source_search_contract_expansion_R1B2a_runtime_aware_codec_parser/failures/R1B2a_<HANDLE>.md
```

The failure report must identify the exact blocker and distinguish blockers in
`n` from blockers in `M(n)`.

Use this blocker taxonomy where applicable:

- no polynomial-time formalism;
- codec too abstract;
- parser serialization cannot be fixed locally;
- witnessBits bound unavailable.

## Allowed scope

Only:

- `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageRuntime.lean`
  when producing Outcome A in Lean;
- reports under
  `seed_packs/source_search_contract_expansion_R1B2a_runtime_aware_codec_parser/reports/`;
- failures under
  `seed_packs/source_search_contract_expansion_R1B2a_runtime_aware_codec_parser/failures/`;
- minimal tests/audit registrations required by the repository if and only if a
  Lean module is added.

## Forbidden

- No R1-C.
- No extraction theorem.
- No `PpolyDAG L → BoundedSearchSolver`.
- No `target.noBoundedSolver`.
- No `VerifiedNPDAGLowerBoundSource`.
- No `ResearchGapWitness`.
- No endpoint.
- No `SourceTheorem`.
- No `gap_from`.
- No P≠NP claim.
- No lakefile changes unless a Lean module is actually added and the repository
  requires registration.
- No JSONL edits.
- No spec edits.
- No trust-root edits.

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
