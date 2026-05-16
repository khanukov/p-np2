# Worker prompt — R1-B1 parser/codec budget only

## Branch

`main`

## Task

Execute the limited R1-B1 seed pack:

```text
seed_packs/source_search_contract_expansion_R1B1_parser_codec_budget/
```

This is not full Round 1.
Only R1-B1 is authorised.
R1-C remains gated.

## Required reading

Read before editing:

- `RESEARCH_CONSTITUTION.md`
- `seed_packs/source_search_contract_expansion_R1B_prefix_language/reports/R1B_operator_review_claudeopus.md`
- `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguage.lean`
- `seed_packs/source_search_contract_expansion_R1B_prefix_language/README.md`
- `seed_packs/source_search_contract_expansion_R1B_prefix_language/WORKER_PROMPT_R1B.md`
- `pnp4/Pnp4/Frontier/ContractExpansion/C_DAG_Adapter.lean`
- `seed_packs/source_search_contract_expansion_R1A_dag_adapter/reports/R1A_operator_review_claudeopus.md`
- `pnp4/Pnp4/Frontier/SearchMCSPMagnification.lean`
- `pnp4/Pnp4/Frontier/SearchMCSPConcreteTargets.lean`
- `pnp4/Pnp4/Frontier/CompressionMagnification.lean`
- `pnp3/Complexity/Interfaces.lean`

## Goal

Make the staged verifier budget concrete for a tree-MCSP prefix language, without opening R1-C.

R1-B approved `PrefixExtensionLanguage`, but NP membership remains staged through:

- `PrefixExtensionNPVerifierBudget`
- `PrefixExtensionNPVerifierPlan`

Your job is to partially discharge the core parser/codec/verifier budget or produce a precise structured failure report explaining why that cannot yet be done honestly.

## Outcome A — Lean landed

If feasible, land one Lean module:

```text
pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageNP.lean
```

Expected contents:

- `treeMCSPPrefixParser` or a parameterized parser for `treeMCSPSearchProblem threshold encoding`;
- a `relation_decidable` theorem or instance if possible;
- parser/budget theorem statements or theorem proofs for the core fields;
- no extraction theorem.

Priority order:

1. Define a concrete or parameterized tree-MCSP prefix parser, targeting a shape like:

   ```lean
   treeMCSPPrefixParser : PrefixParser (treeMCSPSearchProblem threshold encoding)
   ```

   or an equivalent compatible with the exact current signatures.

2. Address relation decidability.  Either prove/provide:

   ```lean
   Decidable (problem.relation n x w)
   ```

   for the concrete target, or explain precisely why the interface only exposes `Prop`.

3. Attempt to discharge real Lean theorems or precise audit statements for:

   - `parser_polynomial_time`
   - `relation_decidable`
   - `relation_polynomial_time`
   - `witness_length_polynomial`

4. If honest, assemble a partial or complete:

   ```lean
   PrefixExtensionNPVerifierBudget treeMCSPPrefixParser
   ```

   Do not fill budget fields with vacuous statements that hide missing parser, codec, decidability, or runtime work.

If a new pnp4 module lands, keep pnp4 modules listed in `lakefile.lean` and update theorem-surface or axiom-audit tests only if the new public theorem surfaces require those audits.

## Outcome B — structured failure

If Outcome A cannot be done honestly, write a structured failure report:

```text
seed_packs/source_search_contract_expansion_R1B1_parser_codec_budget/failures/R1B1_<HANDLE>.md
```

The report must include:

- attempted parser shape and module path;
- exact parser input convention considered, including tag, `n`, `x`, `i`, prefix `p`, and padding;
- proposed ambient length convention `M(n)`;
- malformed-input policy;
- attempted relation-decidability path;
- whether the current interface exposes only `Prop` and where;
- attempted `parser_polynomial_time` formalization path;
- attempted `relation_polynomial_time` formalization path;
- attempted `witness_length_polynomial` formalization path;
- parser/codec/runtime blocker;
- whether the blocker requires operator permission to touch a forbidden file;
- recommended next action for operator review.

## Allowed scope

Only:

- `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageNP.lean` for Outcome A;
- `lakefile.lean` only if registering the Outcome A module is necessary;
- `pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean` only if new public theorem surfaces require it;
- `pnp4/Pnp4/Tests/AxiomsAudit.lean` only if new audited theorem surfaces require it;
- `seed_packs/source_search_contract_expansion_R1B1_parser_codec_budget/failures/R1B1_<HANDLE>.md` for Outcome B;
- `seed_packs/source_search_contract_expansion_R1B1_parser_codec_budget/reports/R1B1_<HANDLE>.md` only if the operator asks for a report.

## Forbidden

No extraction theorem.
No `PpolyDAG L → BoundedSearchSolver`.
No `target.noBoundedSolver`.
No `VerifiedNPDAGLowerBoundSource` construction.
No `ResearchGapWitness`.
No endpoint.
No R1-C.
No `SourceTheorem`.
No `gap_from`.
No P≠NP claim.
No JSONL edits.
No spec edits.
No trust-root edits.
No unrelated lower-bound route work.

Do not add `axiom`, `sorry`, `admit`, or `native_decide` in active pnp3/pnp4 code.

## Commands

Run:

```sh
./scripts/check.sh
```

## Output format

End with this exact report shape:

```text
Task: R1-B1 seed pack skeleton
Commit before:
Commit after:
Changed files:
R1-B1 only: yes/no
R1-C gated: yes/no
Commands run:
Scope violations:
```
