# R1-B2a Runtime-Aware Codec / Parser Seed Pack

## Status

OPEN — R1-B2a only.

R1-C is gated.
Full contract expansion is NOT authorised.

## Classification

Infrastructure / contract-expansion staging.

This seed pack is not mainline P-vs-NP progress by itself. It is a limited
R1-B2a staging task for the runtime-aware codec/parser interface needed before
any honest `PrefixExtensionLanguage_in_NP` theorem can be attempted. Any future
mainline claim must still reduce `SearchMCSPWeakLowerBound` or
`VerifiedNPDAGLowerBoundSource` under the repository route policy.

## Required reading

Before attempting this seed pack, read:

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

## Why R1-B2a exists

R1-B2 resolved the key runtime distinction:

- truth-table verification is exponential in target parameter `n`;
- but can be polynomial in ambient input length `M(n)` if `M(n)` includes
  `tableLen n`.

However, current repo still lacks:

- concrete `M(n)`;
- concrete parser;
- codec witness-length bound;
- decode runtime bound;
- threshold bound in `M(n)`;
- bridge from local runtime facts to `NP_TM`.

## Central R1-B2a question

Can we define a runtime-aware tree-circuit codec/parser interface with enough
explicit arithmetic/runtime fields to make the eventual
`PrefixExtensionLanguage_in_NP` theorem meaningful, without claiming it yet?

## Authorised deliverables

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

### D. R1-C remains gated

Do **not** prove `PrefixExtensionLanguage_in_NP`.
Do **not** open R1-C.

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

## Success criteria

### Outcome A

Lean module or markdown+Lean report lands with runtime-aware codec/parser
interface and at least one real arithmetic lemma such as `tableLen_le_M`.

### Outcome B

Structured failure identifies exact blocker:

- no polynomial-time formalism;
- codec too abstract;
- parser serialization cannot be fixed locally;
- witnessBits bound unavailable.
