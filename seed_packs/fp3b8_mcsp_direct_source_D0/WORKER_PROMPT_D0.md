# Worker prompt — fp3b8-D0 direct MCSP source-interface feasibility audit

## Slot

`fp3b8-D0` — Direct MCSP source-interface feasibility audit.

## Task type

Markdown-only feasibility report.

Do **not** write Lean code.  Do **not** edit JSONL logs.  Do **not** edit specs,
known guards, trust roots, `lakefile.lean`, or existing theorem surfaces.  Do
**not** create a `SourceTheorem`, `gap_from`, `ResearchGapWitness`, candidate
package, final endpoint, or `P != NP` claim.  Do **not** promote any
`ProvenanceFilter`.  Do **not** design or launch a full Round 1; a GREEN-light
verdict may only recommend that the operator design one later.

## Required reading

Read these files before writing the D0 report:

- `RESEARCH_CONSTITUTION.md`
- `seed_packs/first_move_search_2026/reports/post_fp3b6_fp3b7_strategy_refresh_codex.md`
- `outputs/nogolog.jsonl` entries `NOGO-000006`, `NOGO-000007`,
  `NOGO-000008`, and `NOGO-000009`

Also search the repository for these identifiers and inspect the relevant files
that define or use them:

- `SearchMCSPWeakLowerBound`
- `VerifiedNPDAGLowerBoundSource`
- `ResearchGapWitness`
- `NP_not_subset_PpolyDAG`

At minimum, identify the existing upstream/downstream role of the pnp4
search-MCSP source package, the pnp4 verified DAG lower-bound source, the pnp3
research-gap witness, and the final `NP_not_subset_PpolyDAG` target.

## Output file

Create exactly one report file:

```text
seed_packs/fp3b8_mcsp_direct_source_D0/reports/D0_mcsp_source_interface_<HANDLE>.md
```

Replace `<HANDLE>` with your worker handle.

## Central question

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

## Required report sections

Your report must contain all of these sections:

1. What is the direct MCSP/source-interface route?
2. Which exact existing repository objects are upstream/downstream?
3. What is a candidate `SearchMCSPWeakLowerBound` statement?
4. Why is it non-circular?
5. Why is it non-large / not natural-proof-shaped?
6. Why does it avoid FP3b NoGos?
7. How could it connect to `VerifiedNPDAGLowerBoundSource`?
8. What are the first self-attacks?
9. Verdict: GREEN-light / RED-light / INCONCLUSIVE.

## Minimum analysis requirements

In the report, explicitly address:

- whether the proposed route is a direct MCSP/meta-complexity source interface
  rather than a renamed FP3b provenance filter;
- whether the proposed weak lower-bound statement avoids support-cardinality-only
  criteria, displayed-syntax-only criteria, tautological-seed rewrite fragility,
  and structural-normalisation self-defeat;
- whether the proposed statement hides a `PpolyDAG` lower bound in its
  assumptions, definitions, promises, oracle access, advice, certificate, or
  verifier;
- whether the proposed statement becomes a large and constructive useful
  property of Boolean functions in the Razborov--Rudich sense;
- whether the proposed route relativizes or algebrizes in a way that makes the
  claimed bridge implausible;
- what concrete magnification contract would be needed to turn the candidate
  weak lower bound into `VerifiedNPDAGLowerBoundSource`.

## Verdict rules

End with exactly one of:

- **GREEN-light** — a full fp3b8 Round 1 can be designed.
- **RED-light** — direct MCSP source-interface route should not be expanded.
- **INCONCLUSIVE** — operator decides whether to treat as RED-light or escalate.

A GREEN-light verdict must identify a concise candidate source statement and
explain why its route to `VerifiedNPDAGLowerBoundSource` is clearer than the
FP3b provenance-filter route.

A RED-light verdict must identify the fatal barrier, circularity, largeness, or
NoGo collision.

An INCONCLUSIVE verdict must state the minimum missing evidence needed before a
full Round 1 could be responsibly designed.
