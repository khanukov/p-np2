# Barrier certificate — template

**This is a template, not a real candidate.** Copy to a real
candidate directory before editing.

Per `RESEARCH_CONSTITUTION.md` Rule 7, every candidate must declare
which classical barriers (relativization, natural proofs,
algebrization) its approach contends with, and where in the candidate
the obstacle is overcome.

## Relativization

Status: `unknown` | `non-relativizing` | `relativizing-but-OK`

Which step is non-relativizing? (Identify the proof step in
`proof.lean` whose argument fails under an oracle. If the candidate
relativizes, justify why this is not a Baker–Gill–Solovay-style
obstruction for the target.)

## Natural proofs (Razborov–Rudich)

Status: `unknown` | `non-natural` | `natural-but-with-caveat`

Which Razborov–Rudich condition does the candidate break?
- `constructivity` — the predicate cannot be evaluated in P/poly.
- `largeness` — the predicate captures only a small fraction of
  Boolean functions.
- `usefulness` — the predicate fails on functions in NP.

If `unknown-human-review`, this entry counts against
`spec/target.toml::[human_review].candidate_queue_limit`.

## Algebrization (Aaronson–Wigderson)

Status: `unknown` | `non-algebrizing` | `algebrizing-but-OK`

Which step fails under a multilinear-extension oracle? (Identify
the proof step whose argument breaks when the oracle is replaced by
an algebraic extension.)

## Hardwiring (Probe 2 of the falsifiability audit)

Status: `not-checked` | `checked-and-excluded` | `unknown-human-review`

Has the candidate been tested against truth-table hardwiring?
Specifically, does there exist a `PpolyFormula` witness whose family
is a singleton truth-table evaluator that satisfies
`SourceTheorem_<id>` but that the candidate's bridge cannot use?

If `checked-and-excluded`, point to the formal lemma in `proof.lean`
that excludes hardwiring (Rule 5 exclusion lemma shape).

## Collapse-vs-contradiction (Rule 8)

Status: `not-applicable` | `genuine-contradiction` |
`collapse-only` (forbidden)

If the candidate's argument is "if NP ⊆ P/poly then PH collapses",
the status is `collapse-only` and the candidate is rejected per
Rule 8. A real contradiction is required.

## Formal witnesses

Where in `proof.lean` do the above status decisions show up as Lean
declarations?

- Hardwiring exclusion lemma: (file:line)
- Non-relativization signal: (file:line)
- Etc.
