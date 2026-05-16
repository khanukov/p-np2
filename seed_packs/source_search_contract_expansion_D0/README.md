# Seed pack `source_search_contract_expansion_D0`

## 1. Status

**OPEN — D0 only.**

Full Round 1 is **NOT** authorised. This seed pack is a markdown-only D0
scoping and audit surface. It creates no theorem, no candidate package, no
endpoint, and no formal lower-bound route.

**Progress classification:** Infrastructure / research triage. This pack does
not reduce `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`; it
only asks whether a later, explicitly authorised source-theorem surface could
be stated honestly.

## 2. Why this seed pack exists

The ResearchGap source-theorem reset selected
`search_mcsp_contract_expansion` as the next honest source-theorem surface
after:

- `fp3b6` — **STALLED**;
- `fp3b7` — **RED-LIGHT**;
- `fp3b8` — **RED-LIGHT**.

The `fp3b8` operator decision red-lighted the direct MCSP source attempt because
`TreeMCSPSearchMagnificationSource` already contains the abstract magnification
contract. In particular, the direct package does not independently derive the
hard bridge; it carries a field of the following shape:

```text
SearchMCSPMagnificationContract :
  target.noBoundedSolver → VerifiedNPDAGLowerBoundSource
```

Therefore, treating `TreeMCSPSearchMagnificationSource` as the next source
surface would merely assume the hard conversion from the no-bounded-solver
condition to `VerifiedNPDAGLowerBoundSource`. The reset report says the next
honest surface is to study the contract itself:

```text
target.noBoundedSolver → VerifiedNPDAGLowerBoundSource
```

with all assumptions visible, instead of hiding the decisive implication inside
`TreeMCSPSearchMagnificationSource`, `SearchMCSPMagnificationContract`, or a
wrapper field.

## 3. D0 central question

Can `SearchMCSPMagnificationContract` be expanded into a concrete theorem whose
assumptions are strictly weaker than `VerifiedNPDAGLowerBoundSource` and which
avoids natural proofs / relativization / algebrization?

The D0 worker must treat this as an audit question, not as a theorem-creation
dispatch. A useful answer may be negative. A negative or inconclusive D0 report
is acceptable if it identifies the exact circularity, hidden-hardness, or
barrier failure.

## 4. What counts as fake progress

The following are rejected as fake progress for this seed pack:

- assuming `SearchMCSPMagnificationContract`;
- assuming `VerifiedNPDAGLowerBoundSource`;
- assuming `ResearchGapWitness`;
- adding a field `weakLowerBound → VerifiedNPDAGLowerBoundSource`;
- hiding `¬ PpolyDAG` inside a promise/certificate;
- using refuted support-bounds routes, including the support-cardinality,
  syntactic-filter, and structural-normalisation families recorded in
  `outputs/nogolog.jsonl` entries `NOGO-000001` through `NOGO-000009`;
- claiming endpoint progress.

A proposal is also fake progress if its claimed language `L` is only hard
because the promise, certificate, verifier, or target object already encodes
`¬ PpolyDAG L`, an NP-vs-P/poly lower bound, a `ResearchGapWitness`, or an
unexpanded magnification contract.

## 5. D0 deliverable

One report:

```text
seed_packs/source_search_contract_expansion_D0/reports/D0_contract_expansion_<HANDLE>.md
```

The report should be markdown-only and should answer the questions in
`WORKER_PROMPT_D0.md`. If the worker cannot make the surface honest, the report
should explain the obstruction precisely and may place any auxiliary notes under
`failures/` only if explicitly authorised later. For this D0 skeleton, no such
failure report is created.

## 6. Verdicts

D0 must end with exactly one of the following verdicts:

- **GREEN-light** — a concrete theorem surface appears non-circular enough to
  justify a separately authorised Round 1 design attempt;
- **RED-light** — the contract expansion collapses into a known fake-progress
  pattern, hidden lower bound, or barrier violation;
- **INCONCLUSIVE** — the question remains open but D0 found specific missing
  definitions, reductions, or audits that must be resolved before any Round 1.

No other verdict labels are allowed.

## 7. Forbidden scope

The following are forbidden for D0 work in this seed pack:

- No Lean code.
- No JSONL edits.
- No spec edits.
- No `known_guards` edits.
- No trust-root edits.
- No `SourceTheorem`.
- No `gap_from`.
- No `ResearchGapWitness`.
- No endpoint.
- No `P≠NP` claim.
- No full Round 1.
