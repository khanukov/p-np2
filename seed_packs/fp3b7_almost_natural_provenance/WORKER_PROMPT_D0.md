# Worker prompt — fp3b7-D0 barrier feasibility

## Slot

`fp3b7-D0` — barrier-aware feasibility check for almost-natural / Family B.

## Task type

Markdown-only feasibility report.

Do **not** write Lean code.  Do **not** edit JSONL logs.  Do **not** edit specs,
known guards, trust roots, `fp3b6`, or any existing seed pack.  Do **not** create
a `SourceTheorem`, `gap_from`, candidate package, final endpoint, or `P≠NP`
claim.  Do **not** dispatch or design a full Round 1 unless your final verdict is
only a recommendation that the operator may use later.

## Required reading

Read these files before writing the D0 report:

- `RESEARCH_CONSTITUTION.md`
- `seed_packs/fp3b6_distinguisher_matrix_provenance/audits/fp3b6_status_reclassification_and_fp3b7_dispatch_plan.md`
- `seed_packs/fp3b6_distinguisher_matrix_provenance/reports/D5_tight_parameter_extraction_gpt55.md`
- `seed_packs/fp3b6_distinguisher_matrix_provenance/reports/D6_budget_reconciliation_gpt55.md`
- `seed_packs/fp3b5_outcome_b_design_audit/audits/outcome_b_strategic_audit.md`
- `outputs/nogolog.jsonl` entries `NOGO-000006`, `NOGO-000007`, `NOGO-000008`,
  and `NOGO-000009`

## Output file

Create exactly one report file:

```text
seed_packs/fp3b7_almost_natural_provenance/reports/D0_barrier_feasibility_<HANDLE>.md
```

Replace `<HANDLE>` with your worker handle.

## Required report sections

Your report must contain all of these sections:

1. What is almost-natural provenance?
2. Candidate semantic predicates.
3. Natural parameter regime.
4. Structural double-bind search.
5. NOGO-000006/7/8/9 cross-check.
6. Razborov–Rudich / Natural Proofs analysis.
7. Relation to fp3b5 strategic audit.
8. Verdict: GREEN-light / RED-light / INCONCLUSIVE.
9. Recommended next action.

## Feasibility questions to answer

In the report, explicitly answer:

- What would an almost-natural provenance filter look like?
- What quantities does it charge?
- Does it avoid support-cardinality-only collapse?
- Does it avoid displayed-syntax-only rewrite fragility?
- Does it avoid normalisation self-defeat?
- Does it re-enter Razborov–Rudich natural-proofs barrier?
- Does it have its own structural double-bind analogous to `fp3b6`?
- Is it worth opening full `fp3b7` Round 1?

## Verdict rules

End with exactly one of:

- **GREEN-light** — full `fp3b7` Round 1 may be designed.
- **RED-light** — `fp3b7` should not be expanded.
- **INCONCLUSIVE** — operator decides whether to treat as RED-light or escalate.

A GREEN-light verdict must explain why the proposed almost-natural provenance
idea plausibly avoids all four active barrier checks (`NOGO-000006` through
`NOGO-000009`) and why any Razborov–Rudich risk is structurally controlled.

A RED-light verdict must identify the fatal barrier or double-bind.

An INCONCLUSIVE verdict must state the minimum missing evidence needed before a
full Round 1 could be responsibly designed.
