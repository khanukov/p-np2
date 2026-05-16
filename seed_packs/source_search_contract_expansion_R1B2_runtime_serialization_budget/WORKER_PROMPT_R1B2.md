# Worker prompt — R1-B2 runtime / serialization budget

## Branch

`main`

## Task

Create a limited Round 1 seed-pack attempt for R1-B2 only.

This is not full Round 1. Only R1-B2 is authorised. R1-C remains gated.

## Classification

Classify this attempt as Infrastructure / contract-expansion staging unless it
directly reduces `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`.
Do not report restricted or staged runtime work as a P-vs-NP endpoint.

## Required reading

Read before editing:

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

## Central question

Can the R1-B / R1-B1 prefix-extension language be shown to be an NP language
under a concrete serialization and runtime budget, without hiding the verifier
work in staged Prop fields?

## Critical runtime distinction

Your attempt must distinguish:

- runtime polynomial in target parameter `n`;
- runtime polynomial in ambient encoded input length `M(n)`.

For tree-MCSP, truth-table verification enumerates `2^n` inputs, which is
exponential in `n` but may be polynomial in `M(n)` if `M(n)` includes
`tableLen n = 2^n`.

This distinction is load-bearing. Do not silently replace an `M(n)`-polynomial
budget with an `n`-polynomial budget, or vice versa.

## Authorised deliverables

Produce exactly one of the following outcomes.

### Outcome A — Lean or audit module landed

Preferred Lean module path:

```text
pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageRuntime.lean
```

Use this path only if the formalization is ready and stays inside R1-B2 scope.
If you add a Lean module, obey all repository requirements for module listing,
surface tests, and axiom audits.

If Lean is premature, produce a markdown report instead:

```text
seed_packs/source_search_contract_expansion_R1B2_runtime_serialization_budget/reports/R1B2_runtime_budget_<HANDLE>.md
```

The successful report or module should cover as much of the following priority
order as possible:

1. Concrete or parameterized serialization convention:
   - `M(n)`
   - tag layout
   - encoding of `n`
   - encoding of `x`
   - encoding of `i`
   - encoding of prefix `p`
   - padding policy
   - malformed-input behavior
2. Concrete parser, defining or staging:
   - `parseTreeMCSPPrefix`
   - `treeMCSPPrefixParser_concrete`
3. Runtime budget analysis, proving or precisely staging:
   - `parser_polynomial_time`
   - `relation_polynomial_time`
   - `witness_length_polynomial`
4. Relation runtime clarification:
   - clarify whether `TreeCircuitWitnessCodec.verifiesDecidable` is polynomial
     in `M(n)`.
5. Optional partial budget:
   - honestly assemble `PrefixExtensionNPVerifierBudget`, or
   - introduce a new R1-B2 budget record showing exactly which fields are
     discharged.

### Outcome B — structured failure

If R1-B2 cannot honestly land, write a structured failure report:

```text
seed_packs/source_search_contract_expansion_R1B2_runtime_serialization_budget/failures/R1B2_<HANDLE>.md
```

The failure report must identify the exact missing polynomial-time formalism or
serialization blocker, and must distinguish blockers in `n` from blockers in
`M(n)`.

## Allowed scope

Only these areas are authorised for an R1-B2 attempt:

- `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageRuntime.lean`
  when producing Outcome A in Lean;
- reports under
  `seed_packs/source_search_contract_expansion_R1B2_runtime_serialization_budget/reports/`;
- failures under
  `seed_packs/source_search_contract_expansion_R1B2_runtime_serialization_budget/failures/`;
- any minimal tests/audit registrations required by the repository if and only
  if a Lean module is added.

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
- No JSONL edits unless a supervising protocol explicitly requires them for the
  completed worker attempt.
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
Task: R1-B2 seed pack skeleton
Commit before: <hash>
Commit after: <hash>
Changed files:
- <path>
R1-B2 only: yes/no
R1-C gated: yes/no
Commands run:
- <command> — <result>
Scope violations: <none or details>
```
