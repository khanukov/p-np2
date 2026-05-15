# fp3b8 — direct MCSP source-interface D0

## 1. Status

**RED-LIGHT — full Round 1 not authorised.**

Full Round 1 is **NOT** authorised.

This seed pack is a markdown-only feasibility skeleton.  It does not introduce
Lean code, a source theorem, a bridge, a `ResearchGapWitness`, an endpoint, or a
`P != NP` claim.

## 2. Why fp3b8 exists

The post-FP3b strategy refresh ended with the verdict
`return_to_research_gap_source_search`.  It recommends stopping the FP3b
provenance-filter route as an active mainline route and opening exactly one next
D0 seed pack: this directory.

The reason is strategic and audit-driven:

- FP3b provenance-filter work is no longer an active mainline route.
- The next useful question returns to the main `ResearchGap` source-theorem
  search rather than attempting another provenance-filter patch.
- fp3b8 examines whether there is a direct MCSP / meta-complexity source
  interface whose route into `SearchMCSPWeakLowerBound` and then
  `VerifiedNPDAGLowerBoundSource` is clearer than the failed FP3b
  provenance-filter paths.

This is not a claim of progress toward the final endpoint.  It is a D0 audit of
whether a responsible full fp3b8 Round 1 could later be designed.

## 3. D0 only

Authorised slot:

**D0 — Direct MCSP source-interface feasibility audit.**

Type: **markdown-only**.

D0 may write one feasibility report under `reports/`.  No Lean development,
JSONL logging, specification edit, guard edit, trust-root edit, theorem
promotion, endpoint work, or full Round 1 design is authorised here.

## 4. D0 central question

Can the repository state a concise, non-circular, non-large
`SearchMCSPWeakLowerBound` candidate whose path to
`VerifiedNPDAGLowerBoundSource` is clearer than every FP3b provenance-filter
path, and whose first self-attack survives:

- `NOGO-000006`;
- `NOGO-000007`;
- `NOGO-000008`;
- `NOGO-000009`;
- Natural Proofs;
- relativization;
- algebrization;
- hidden `PpolyDAG` hardness / circularity?

## 5. Existing repository objects to respect

D0 workers must treat these repository surfaces as read-only context:

- `SearchMCSPWeakLowerBound` — the pnp4 compression/search-MCSP mainline source
  package: a weak lower-bound proposition, its proof, and a magnification map to
  a verified DAG lower-bound source.
- `SearchMCSPWeakCircuitLowerBoundTarget` and
  `SearchMCSPMagnificationContract` — the more concrete pnp4 target/contract
  interface for search/compression lower bounds.
- `VerifiedNPDAGLowerBoundSource` — an explicit `NP` language plus a verified
  lower bound against `PpolyDAG`.
- `ResearchGapWitness` — the pnp3 final research-gap witness whose mathematical
  field is `NP_not_subset_PpolyDAG`.
- `NP_not_subset_PpolyDAG` — the fixed trust-root target boundary for the final
  non-uniform DAG separation.

D0 may discuss how a future candidate could be upstream or downstream of these
objects, but it must not add, edit, or promote any of them.

## 6. D0 required outputs

D0 must produce a report at:

```text
seed_packs/fp3b8_mcsp_direct_source_D0/reports/D0_mcsp_source_interface_<HANDLE>.md
```

Replace `<HANDLE>` with the worker handle.

The report must answer the central question and end with exactly one of the D0
verdicts below.

## 7. D0 possible verdicts

- **GREEN-light:** a full fp3b8 Round 1 can be designed.
- **RED-light:** direct MCSP source-interface route should not be expanded.
- **INCONCLUSIVE:** operator decides whether to treat as RED-light or escalate.

A GREEN-light verdict is only permission to design a later full Round 1; it is
not permission to write Lean code, open an endpoint, or claim a final theorem in
this D0 seed pack.

## 8. Forbidden scope

The following are forbidden in this seed pack and in D0 work:

- No Lean code.
- No JSONL edits.
- No spec edits.
- No `known_guards` edits.
- No trust-root edits.
- No `ProvenanceFilter` promotion.
- No `SourceTheorem`.
- No `gap_from`.
- No `ResearchGapWitness`.
- No endpoint.
- No `P≠NP` claim.
- No full Round 1.
