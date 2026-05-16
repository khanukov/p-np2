# Worker Prompt — R1-B Prefix Language Only

Branch: `main`

Task: limited Round 1 seed pack execution for R1-B only.

Seed pack:

```text
seed_packs/source_search_contract_expansion_R1B_prefix_language/
```

This is not full Round 1. Only R1-B is authorised.

R1-C remains gated. Do not start extraction, endpoint, or lower-bound contradiction work.

## Progress classification

Infrastructure / prefix-language interface specification.

R1-B may define or stage the prefix-extension language and NP verifier for a concrete tree-MCSP search target. It must not be reported as unconditional progress toward `P != NP`, and it must not construct a `VerifiedNPDAGLowerBoundSource`.

## Required reading

Read these files before editing:

- `RESEARCH_CONSTITUTION.md`
- `seed_packs/source_search_contract_expansion_R1A_dag_adapter/reports/R1A_operator_review_claudeopus.md`
- `seed_packs/source_search_contract_expansion_R1A_dag_adapter/README.md`
- `seed_packs/source_search_contract_expansion_R1A_dag_adapter/WORKER_PROMPT_R1A.md`
- `seed_packs/source_search_contract_expansion_D0/reports/D0_contract_expansion_gpt55.md`
- `seed_packs/source_search_contract_expansion_D0/reports/D0_1_interface_alignment_gpt55.md`
- `pnp4/Pnp4/Frontier/ContractExpansion/C_DAG_Adapter.lean`
- `pnp4/Pnp4/Frontier/SearchMCSPMagnification.lean`
- `pnp4/Pnp4/Frontier/SearchMCSPConcreteTargets.lean`
- `pnp4/Pnp4/Frontier/CompressionMagnification.lean`
- `pnp4/Pnp4/AlgorithmsToLowerBounds/BridgeToPpolyDAG.lean`
- `pnp3/Complexity/Interfaces.lean`

## Goal

Specify and, only if safe, begin formalizing `L_prefix_target` for a concrete tree-MCSP search target.

The language should encode prefix extendability for target witnesses. For a well-formed input `⟨tag,n,x,i,p,pad⟩`, membership should assert that some full witness `w` extends prefix `p` through index `i` and satisfies the concrete target relation for `x` at length `n`.

## Required specification details

A successful R1-B result must address:

1. Prefix input format: `⟨tag,n,x,i,p,pad⟩`.
2. Length convention: an auditable ambient length `M(n)`.
3. Malformed input behavior: malformed inputs are nonmembers.
4. Membership condition: existence of a full relation witness extending the prefix.
5. NP verifier witness: full witness `w`, plus any explicit codec auxiliary data if required.
6. Prefix agreement check.
7. Relation check.
8. Codec requirements.
9. Polynomial witness-length and verifier-runtime conditions.

## Outcome A — theorem/skeleton landed

If feasible, land a Lean module at exactly one of these paths:

```text
pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguage.lean
```

or, if the normal module is too risky, an audit-only module:

```text
pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguage_Audit.lean
```

Expected contents:

- prefix input format / parser interface;
- `L_prefix_target` definition;
- NP verifier plan or theorem;
- no extraction theorem.

If a new pnp4 module is landed, keep it registered according to the repository module policy and update public theorem-surface or axiom-audit tests only if new public theorem surfaces require those audits.

## Outcome B — structured failure

If R1-B cannot safely land a Lean module or precise specification, write a structured failure report:

```text
seed_packs/source_search_contract_expansion_R1B_prefix_language/failures/R1B_<HANDLE>.md
```

The report must include:

- attempted module path or markdown-only specification scope;
- exact prefix input format attempted;
- proposed `M(n)` convention;
- malformed-input policy;
- proposed membership predicate;
- NP verifier witness format and checks;
- codec or polynomial-budget blockers;
- whether the blocker requires operator permission to touch a forbidden file;
- recommended next action for operator review.

## Allowed scope

Only these seed-pack skeleton files are in scope for the skeleton-creation task:

- `seed_packs/source_search_contract_expansion_R1B_prefix_language/README.md`
- `seed_packs/source_search_contract_expansion_R1B_prefix_language/WORKER_PROMPT_R1B.md`
- `seed_packs/source_search_contract_expansion_R1B_prefix_language/reports/.gitkeep`
- `seed_packs/source_search_contract_expansion_R1B_prefix_language/failures/.gitkeep`

A minimal `seed_packs/README.md` registration is optional only if the operator requests or repository convention requires it.

For an actual later R1-B execution, the only additional authorised outputs are the Outcome A module path above, the audit-only module path above, or the Outcome B failure report path above.

## Forbidden scope

No Lean code in the skeleton-creation task.

No edits to:

- `lakefile.lean` during the skeleton-creation task;
- JSONL files;
- spec files;
- trust-root files;
- `pnp3/Complexity/Interfaces.lean`;
- endpoint or no-go policy files.

No:

- `SourceTheorem`;
- `gap_from`;
- `ResearchGapWitness`;
- endpoint;
- `VerifiedNPDAGLowerBoundSource` construction;
- `PpolyDAG` lower-bound claim;
- extraction theorem;
- `BoundedSearchSolver` construction;
- `target.noBoundedSolver` contradiction;
- R1-C;
- `P != NP` / `P≠NP` claim.

## Required command

Run:

```sh
./scripts/check.sh
```

## Required worker output

End with this exact report shape:

```text
Task: R1-B seed pack skeleton
Commit before:
Commit after:
Changed files:
R1-B only: yes/no
R1-C gated: yes/no
Commands run:
Scope violations:
```
