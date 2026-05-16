# R1-B1 parser/codec budget seed pack — limited skeleton

## Status

OPEN — R1-B1 only.

R1-C is gated.
Full contract expansion is NOT authorised.

## Classification

Infrastructure / contract-expansion preparation.

R1-B1 is not a P-vs-NP endpoint and must not be reported as unconditional progress toward `P != NP`.  It is a limited follow-up to R1-B that can make parser, decidability, and verifier-budget obligations concrete before any separately gated R1-C work is considered.

## Why R1-B1 exists

R1-B approved `PrefixExtensionLanguage`, but NP membership is staged via:

- `PrefixExtensionNPVerifierBudget`
- `PrefixExtensionNPVerifierPlan`

R1-C must not open until the core parser/codec/verifier budget is partially discharged.

The R1-B operator review identified the next useful step as a concrete tree-MCSP parser plus the core budget facts, with structured failure accepted if the current interfaces expose only relation-level `Prop` data or lack a runtime formalism.

## Purpose

Make the staged verifier budget concrete for a tree-MCSP prefix language.

A successful worker should focus on the concrete target built from:

```lean
treeMCSPSearchProblem threshold encoding
```

and the prefix language interface from:

```lean
PrefixParser (treeMCSPSearchProblem threshold encoding)
PrefixExtensionNPVerifierBudget
PrefixExtensionNPVerifierPlan
```

## Required reading for the worker

Read these before attempting the R1-B1 task:

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

## R1-B1 authorised deliverables

Work in the following priority order.

### A. Concrete or parameterized tree-MCSP prefix parser

Target shape:

```lean
treeMCSPPrefixParser : PrefixParser (treeMCSPSearchProblem threshold encoding)
```

or an equivalent construction, depending on the exact signatures needed by the current Lean interfaces.

The parser may be concrete or parameterized, but it must remain honest about the ambient length convention, tags, decoded fields, malformed-input behavior, and padding policy.

### B. Relation decidability

Either:

- prove or provide `Decidable (problem.relation n x w)` for the concrete target; or
- write a structured failure explaining why current interfaces only expose `Prop` and what additional interface or codec data would be needed.

### C. Budget fields

Attempt to discharge real Lean theorems or precise audit statements for:

- `parser_polynomial_time`
- `relation_decidable`
- `relation_polynomial_time`
- `witness_length_polynomial`

The worker may leave other `PrefixExtensionNPVerifierBudget` fields staged, but must explicitly say which fields remain staged and why.

### D. Optional partial budget object

If possible, assemble a partial or complete:

```lean
PrefixExtensionNPVerifierBudget treeMCSPPrefixParser
```

Only if honest.

Do not manufacture a complete budget by hiding unproved parser, codec, runtime, or decidability work behind vacuous propositions.

## Explicit non-goals

No extraction theorem.
No `PpolyDAG L → BoundedSearchSolver`.
No `target.noBoundedSolver`.
No `VerifiedNPDAGLowerBoundSource`.
No `ResearchGapWitness`.
No endpoint.
No R1-C.
No `SourceTheorem`/`gap_from`.
No P≠NP claim.

## Success criteria

### Outcome A: Lean module lands with parser/decidability/budget progress

A Lean module lands under the authorised R1-B1 path with at least one concrete parser, decidability, or budget obligation advanced honestly, and without an extraction theorem or endpoint claim.

### Outcome B: structured failure explains exact parser/codec/runtime blocker

A failure report lands under this seed pack explaining the exact parser, codec, relation-decidability, or runtime-formalism blocker.  The report should identify whether the blocker is intrinsic to the current mathematical interface or merely a missing implementation detail.

## Allowed scope for a future R1-B1 worker

A future R1-B1 execution may touch only:

- `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageNP.lean`, if pursuing Outcome A;
- `lakefile.lean`, only if needed to register the new module for Outcome A;
- `pnp4/Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean`, only if new public theorem surfaces require it;
- `pnp4/Pnp4/Tests/AxiomsAudit.lean`, only if new audited theorem surfaces require it;
- `seed_packs/source_search_contract_expansion_R1B1_parser_codec_budget/failures/R1B1_<HANDLE>.md`, if pursuing Outcome B;
- `seed_packs/source_search_contract_expansion_R1B1_parser_codec_budget/reports/R1B1_<HANDLE>.md`, if writing a review/report requested by the operator.

## Forbidden scope

No Lean code in this skeleton task.

For future R1-B1 execution, no edits to JSONL logs, spec files, trust-root files, endpoint files, or R1-C artifacts unless a separate operator instruction explicitly authorises them.

No `axiom`, `sorry`, `admit`, `native_decide`, or hidden endpoint payload may be added in active pnp3/pnp4 code.

## Required command

Run:

```sh
./scripts/check.sh
```

## Required worker output

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
