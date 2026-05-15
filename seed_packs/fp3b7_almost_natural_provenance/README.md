# fp3b7 — almost-natural provenance

## 1. Status

**RED-LIGHT — full Round 1 not authorised.**

Full Round 1 is **NOT** authorised.  fp3b7 remains an audit-artifact seed
pack only after D0, D0.1, and D0.1-second-review.  See
`audits/fp3b7_red_light_operator_decision_gpt55.md` for the closure decision.

This seed pack is an infrastructure / research-governance record for
markdown-only feasibility checks.  It is not mainline progress toward `P != NP`,
does not reduce `SearchMCSPWeakLowerBound` or
`VerifiedNPDAGLowerBoundSource`, and does not introduce any endpoint.

## 2. Why fp3b7 exists

`fp3b6` is **STALLED** as a Family-A magnification route because its useful
local anti-collapse theorem does not reach the parameter regime needed for
AM-style magnification.  The obstruction is a structural double-bind:

- log-width hardwiring must stay `O(log n)` for polynomial `ttFormula` size;
- AM-style fingerprint footprints exceed that log window;
- D3′-A local anti-collapse is valid but not magnification-ready.

In other words, keeping the arbitrary truth-table payload inside polynomial-size
formula hardwiring forces a logarithmic payload window, while the larger
fingerprint footprint needed by the Family-A / AM-style distinguisher route can
read through that whole window and destroys the hiding argument.  The D3′-A
result remains a valid local anti-collapse check, but not a sufficient
magnification bridge.

Therefore `fp3b7` explores **Family B / almost-natural provenance**: a different
possible design family whose first question is whether any almost-natural
provenance filter can avoid the known hardwiring, syntactic-rewrite,
normalisation, and natural-proofs barriers before a full seed-pack round is
opened.

## 3. D0 only

The only authorised starting slot is:

**D0 — barrier-aware feasibility check for almost-natural / Family B.**

Type: **markdown-only**.

D0 may write one feasibility report under `reports/` using the worker prompt in
`WORKER_PROMPT_D0.md`.  No Lean development, JSONL logging, specification edit,
registry edit, guard promotion, trust-root change, candidate promotion, or final
endpoint work is authorised by this seed pack.

## 4. D0 required questions

D0 must answer all of the following questions:

- What would an almost-natural provenance filter look like?
- What quantities does it charge?
- Does it avoid support-cardinality-only collapse?
- Does it avoid displayed-syntax-only rewrite fragility?
- Does it avoid normalisation self-defeat?
- Does it re-enter Razborov–Rudich natural-proofs barrier?
- Does it have its own structural double-bind analogous to `fp3b6`?
- Is it worth opening full `fp3b7` Round 1?

## 5. D0 possible verdicts

D0 must end with exactly one of these verdicts:

- **GREEN-light:** full `fp3b7` Round 1 may be designed.
- **RED-light:** `fp3b7` should not be expanded.
- **INCONCLUSIVE:** operator decides whether to treat as RED-light or escalate.

## 6. Forbidden scope

The following are forbidden in this seed pack and in D0 work:

- No Lean code.
- No JSONL edits.
- No spec edits.
- No `known_guards` edits.
- No trust-root edits.
- No `ProvenanceFilter` promotion.
- No `SourceTheorem`.
- No `gap_from`.
- No endpoint.
- No `P≠NP` claim.
- No full Round 1.
