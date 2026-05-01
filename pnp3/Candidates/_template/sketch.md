# Sketch — template

**This is a template, not a real candidate.** Copy to a real
candidate directory before editing.

## One-paragraph summary

(Replace with a one-paragraph description of the candidate's
intended approach.)

## Source theorem

`SourceTheorem_<id>`: (state the candidate's main claim in plain
language. The Lean form lives in `proof.lean`.)

## Bridge

`gap_from_<id>` connects `SourceTheorem_<id>` to a
`Pnp3.Magnification.ResearchGapWitness`. (Briefly explain why this
implication holds.)

## What the candidate is NOT

Per `RESEARCH_CONSTITUTION.md` Rule 1, this candidate does not claim
to produce a closed `P_ne_NP_unconditional` term. The most a verified
candidate can produce in the current pipeline is a survivor entry in
`outputs/survivor_history.jsonl` with status `survived` (pending the
Critic's attacks).

## What the candidate explicitly avoids

(List the specific drift surfaces the candidate avoids:
- refuted predicates (Rule 6)
- typeclass-payload channels (Rule 16)
- bare package-based finals (PR 3b)
- arbitrary witness quantification without provenance (Rule 5)
- collapse-not-contradiction style arguments (Rule 8))

## Connection to prior work

(Per Rule 15, list relevant prior work and explain what is
structurally different.)
