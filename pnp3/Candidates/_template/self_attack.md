# Self-attack — template

**This is a template, not a real candidate.** Copy to a real
candidate directory before editing.

Per `RESEARCH_CONSTITUTION.md` Rule 12, the Generator and the Critic
are separate roles. Before the Critic phase, the Generator (or the
candidate's author) must perform an explicit self-attack: identify
and document the most plausible failure modes of their own
candidate.

This document is **not** a defence. It is a structured admission of
the most likely ways the candidate breaks.

## Attack 1 — hardwiring

Does the candidate's `SourceTheorem_<id>` admit a truth-table
hardwired witness? (Probe 2 of the falsifiability audit.) If yes,
the candidate is refuted.

Status: `not-attempted` | `attack-failed` | `attack-succeeded`

If `attack-succeeded`, the candidate is its own refutation; record
it as a `NoGoLog` entry with `failure_class = "hardwiring"`.

## Attack 2 — refuted-predicate sneak-in

Does the candidate transitively reach any of the six refuted
predicates listed in `spec/target.toml::[refuted_predicates]`?
(Walk the dependency closure of `SourceTheorem_<id>` and
`gap_from_<id>`.)

Status: `not-attempted` | `attack-failed` | `attack-succeeded`

## Attack 3 — typeclass-payload channel

Does the candidate hide a payload through a typeclass parameter?
(Per Rule 16 and `spec/implicit_assumption_channels.md`.)

Status: `not-attempted` | `attack-failed` | `attack-succeeded`

## Attack 4 — collapse-not-contradiction

Does the candidate's bridge actually deduce P ≠ NP, or only that
some other implication would hold? (Rule 8.)

Status: `not-attempted` | `attack-failed` | `attack-succeeded`

## Attack 5 — arbitrary-witness exploitation

Does the candidate rely on `∀ W : PpolyWitness, ...` shapes without
the Rule 5 exclusion lemma?

Status: `not-attempted` | `attack-failed` | `attack-succeeded`

## Attack 6 — prior-art duplication

Per Rule 15, does this candidate replicate an approach already
refuted in the literature or in `outputs/nogolog.jsonl`?

Status: `not-attempted` | `attack-failed` | `attack-succeeded`

## Attack 7 — size policy violation

Per Rule 4, does the candidate's `SourceTheorem_<id>` (and its
dependency closure) fit within `K_stmt = 40` and `K_exp = 200`
lines? Or is it over-broad?

Status: `not-attempted` | `attack-failed` | `attack-succeeded`

If `attack-succeeded`, the candidate is too broad and must be
narrowed before re-submission.
