# external_barriers_audit_D0

D0 markdown-only audit: compare the surviving proof-template surfaces
in `pnp3` and `pnp4` against published barriers in circuit complexity
and meta-complexity, with the goal of identifying routes that are
**already known to be blocked** by external literature so the project
can avoid re-discovering known dead-ends.

## Why this exists

The pnp3 audit chain has spent substantial effort formalizing
internal no-go results that, on inspection, often recover phenomena
already established (and published) in the meta-complexity
literature.  Examples:

- `FormulaSupportBoundsPartial → False` (Probe 7) — recovers a
  natural-proofs-style obstruction for support-cardinality
  combinatorial properties.
- `isoStrong_conclusion_negative_general` (L1 sessions 1–4 + route
  closure) — recovers a counting/diagonalisation obstruction
  analogous in spirit to the locality barrier of Chen et al.
  (JACM 2022).

Each such "local" no-go costs many engineer-sessions to formalize,
but does not advance the project beyond what published barriers
already imply.

This audit is **proactive**: rather than continue to rediscover
barriers internally, we list the surviving proof-template Props in
the codebase, compare each against published barriers, and recommend
NoGoLog entries (subject to operator approval per repo policy) for
routes that are already published-blocked.

## Triggering context

- Repo at `main` HEAD after `f6a6e8e6`
  (general_isoStrong_route_closure merged).
- All three `Asymptotic*Route` Props at canonical asymptotic
  instantiation are now formally closed in
  `pnp3/Tests/GeneralIsoStrongRouteClosure.lean`.
- Remaining open territory: `FixedSlice*Route` family,
  `pnp4` SearchMCSP frontier, `ResearchGapWitness` (method-agnostic).

## Scope

- Markdown-only.
- One D0 report under `reports/`.
- No Lean code, no JSONL, no NoGoLog, no `known_guards`, no
  trust-root edits.
- No `ResearchGapWitness`, `SourceTheorem`, `gap_from`, endpoint,
  or `P ≠ NP` claim.
- Recommended NoGoLog entries are **listed as proposals**, not
  applied (per repository governance: NoGoLog edits require
  operator approval).

## Deliverable

`reports/external_barriers_audit_opus47.md` — comprehensive audit
with:

1. Catalog of live routes in `pnp3` and `pnp4`.
2. Catalog of published barriers with citations.
3. Per-route applicability table.
4. Recommended NoGoLog proposal list (operator-approval-pending).
5. Routes that survive the audit (no published barrier directly
   applies).
6. Strategic recommendation.
