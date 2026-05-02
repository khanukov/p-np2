# Critic report — `<candidate_id>`

> **Template note.**  This file is a placeholder for the structured
> Critic output specified in `spec/critic_protocol.md`.  Each candidate
> package under `pnp3/Candidates/<id>/` should ship with this file
> filled in **after** `scripts/verify_candidate.sh` returns
> `verifier_status ∈ {PASS, PASS_SHAPE_ONLY}`.  The Critic produces it,
> not the Generator (Rule 12).
>
> The six-attack schema below is fixed; do not reorder, rename, or
> add sections.  Each section's three-field schema (`status`,
> `summary`, `evidence`) is enforced by `spec/critic_protocol.md`.

## Attack 1: Hidden-payload attack

- **status:** `attack not applicable`
- **summary:** Template placeholder — replace with whether the
  candidate's `proof.lean` introduces a typeclass / `Fact` /
  `axiom` / `opaque` / hidden-payload channel that smuggles
  `ResearchGapWitness` (or any of its dependency closure) past
  Rule 16.
- **evidence:**
    - Template — fill with file paths, line numbers, or a structural
      argument that another reviewer can independently reproduce.

## Attack 2: Hardwiring attack

- **status:** `attack not applicable`
- **summary:** Template placeholder — replace with whether the
  candidate's `gap_from_*` bridge admits a truth-table-style
  hardwiring witness that satisfies the candidate's `Π` while
  refuting any non-trivial conclusion.
- **evidence:**
    - Template.

## Attack 3: KnownGuards-factorization attack

- **status:** `attack not applicable`
- **summary:** Template placeholder — replace with whether the
  candidate's `Π` factors through any guard listed in
  `spec/known_guards.toml::[guards.*]` whose `status = "accepted"`
  and `standalone_factorization_target = true`.
- **evidence:**
    - Template.

## Attack 4: Natural-proof / relativization / algebrization barrier audit

- **status:** `attack not applicable`
- **summary:** Template placeholder — replace with the result of
  examining `barrier_certificate.md` against the candidate's
  `SourceTheorem_*` shape.  Cite Razborov-Rudich (natural proof),
  Baker-Gill-Solovay (relativization), Aaronson-Wigderson
  (algebrization) where applicable.
- **evidence:**
    - Template.

## Attack 5: Collapse-not-contradiction audit

- **status:** `attack not applicable`
- **summary:** Template placeholder — replace with whether the
  candidate's `SourceTheorem_*` is a *collapse* statement (e.g.
  "if NP ⊆ P/poly then PH collapses") rather than an unconditional
  *contradiction*.  Rule 8 forbids using a collapse as a stand-in
  for a separation.
- **evidence:**
    - Template.

## Attack 6: Vacuity / source-theorem rephrasing audit

- **status:** `attack not applicable`
- **summary:** Template placeholder — replace with whether the
  candidate's `SourceTheorem_*` is a renaming, restatement, or
  trivial weakening of a previously refuted predicate (see
  `pnp3/RefutedPredicates/Registry.lean`) or of a previously
  refuted route (see `spec/target.toml::[refuted_predicates]`).
- **evidence:**
    - Template.

## Verdict

- **critic_status:** `pass`
- **dominant_break_class:** `null`
- **dominant_break_section:** `null`
- **next_recommended_action:** `Template — replace with concrete next-step recommendation. Default: do NOT promote until at least one human Critic reviews this report.`

> **Template caveat.**  The default `pass` above is a TEMPLATE marker,
> NOT an actual Critic verdict.  A real `pass` requires every attack
> section to be FILLED IN with non-template evidence.  Verifier
> tooling that records `critic_status = pass` from this template
> file is incorrect — the template's `attack not applicable` defaults
> are placeholders.
