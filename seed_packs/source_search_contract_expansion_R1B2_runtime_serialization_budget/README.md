# R1-B2 Runtime / Serialization Budget Seed Pack

## Status

OPEN — R1-B2 only.

R1-C is gated.
Full contract expansion is NOT authorised.

## Classification

Infrastructure / contract-expansion staging.

This seed pack does not claim mainline P-vs-NP progress by itself. It is a limited
R1-B2 staging task for the prefix-extension NP-language budget surface. Any
future mainline claim must still reduce `SearchMCSPWeakLowerBound` or
`VerifiedNPDAGLowerBoundSource` under the repository route policy.

## Required reading

Before attempting this seed pack, read:

- `RESEARCH_CONSTITUTION.md`
- R1-B1 review:
  `seed_packs/source_search_contract_expansion_R1B1_parser_codec_budget/reports/R1B1_operator_review_claudeopus.md`
- R1-B1 module:
  `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageNP.lean`
- R1-B module:
  `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguage.lean`
- R1-B review:
  `seed_packs/source_search_contract_expansion_R1B_prefix_language/reports/R1B_operator_review_claudeopus.md`
- R1-A module:
  `pnp4/Pnp4/Frontier/ContractExpansion/C_DAG_Adapter.lean`
- R1-A review:
  `seed_packs/source_search_contract_expansion_R1A_dag_adapter/reports/R1A_operator_review_claudeopus.md`
- Core files:
  - `pnp4/Pnp4/Frontier/SearchMCSPMagnification.lean`
  - `pnp4/Pnp4/Frontier/SearchMCSPConcreteTargets.lean`
  - `pnp4/Pnp4/Frontier/CompressionMagnification.lean`
  - `pnp3/Complexity/Interfaces.lean`

## Why R1-B2 exists

R1-B1 discharged relation decidability for the codec case, but did not prove NP
membership.

Remaining staged obligations:

- `parser_polynomial_time`
- `relation_polynomial_time`
- `witness_length_polynomial`
- concrete serialization / parse
- possibly codec witness-length bounds
- polynomial-time formalism alignment

## Central question

Can the R1-B / R1-B1 prefix-extension language be shown to be an NP language
under a concrete serialization and runtime budget, without hiding the verifier
work in staged Prop fields?

## Critical runtime distinction

R1-B2 must distinguish:

- runtime polynomial in target parameter `n`;
- runtime polynomial in ambient encoded input length `M(n)`.

For tree-MCSP, truth-table verification enumerates `2^n` inputs, which is
exponential in `n` but may be polynomial in `M(n)` if `M(n)` includes
`tableLen n = 2^n`.

This distinction is load-bearing.

## R1-B2 authorised deliverables

Priority order:

### A. Concrete or parameterized serialization convention

Define / specify:

- `M(n)`
- tag layout
- encoding of `n`
- encoding of `x`
- encoding of `i`
- encoding of prefix `p`
- padding policy
- malformed-input behavior

### B. Concrete parser

Define or stage:

- `parseTreeMCSPPrefix`
- `treeMCSPPrefixParser_concrete`

### C. Runtime budget analysis

Prove or precisely stage:

- `parser_polynomial_time`
- `relation_polynomial_time`
- `witness_length_polynomial`

### D. Relation runtime clarification

Clarify whether `TreeCircuitWitnessCodec.verifiesDecidable` is polynomial in
`M(n)`.

### E. Optional partial budget

If honest, assemble partial:

- `PrefixExtensionNPVerifierBudget`

or a new R1-B2 budget record showing exactly which fields are discharged.

## Explicit non-goals

- No R1-C.
- No extraction theorem.
- No `PpolyDAG L → BoundedSearchSolver`.
- No `target.noBoundedSolver`.
- No `VerifiedNPDAGLowerBoundSource`.
- No `ResearchGapWitness`.
- No endpoint.
- No `SourceTheorem` / `gap_from`.
- No P≠NP claim.

## Success criteria

### Outcome A

Lean or markdown+Lean progress lands:

- concrete parser / runtime budget / witness-length bounds.

### Outcome B

Structured failure explains exact missing polynomial-time formalism or
serialization blocker.
