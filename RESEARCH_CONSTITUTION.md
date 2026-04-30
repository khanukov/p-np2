# Research Constitution v0.1

This file freezes the rules of engagement for work on the `p-np2` repository
during Phase 0 of the research-governance program. It is binding for all
subsequent PRs (governance, cleanup, foundational, candidate, verifier).

The constitution is **append-only with respect to the current scope**:
new rules may be added only when a concrete, factual hole in the repository
is found. Architectural speculation does not justify new rules.

If something is unclear, mark it `needs_review` and continue.

---

## Frozen target (one sentence)

The target of the project is to produce a closed, zero-argument term

```
P_ne_NP_unconditional : ComplexityInterfaces.P_ne_NP
```

by exhibiting a `ResearchGapWitness` whose field
`dagSeparation : NP_not_subset_PpolyDAG` is honestly inhabited.

Until that closed term exists, the repository must not advertise an
unconditional proof of P ≠ NP.

---

## Rule 0 — Frozen target and core semantics

The following identifiers are part of the **trust root**. Their meaning is
frozen. Changing any of them is a Foundational PR and is forbidden inside a
Candidate PR, a cleanup PR, or a governance PR.

Frozen identifiers:

- `ComplexityInterfaces.P`
- `ComplexityInterfaces.NP`
- `ComplexityInterfaces.PpolyDAG`
- `ComplexityInterfaces.PpolyFormula`
- `ComplexityInterfaces.NP_not_subset_PpolyDAG`
- `ComplexityInterfaces.P_ne_NP`
- `ResearchGapTarget` (= `NP_not_subset_PpolyDAG`)
- `ResearchGapWitness`
- `ResearchGapWitness.dagSeparation`
- The size measures `FormulaCircuit.size`, `DagCircuit.size`
- The SAT encoding and DAG encoding semantics
- The `decides` / `recognizes` semantics

A Candidate PR is allowed to **prove** new theorems whose conclusions reduce
to these objects, but it is **not allowed to redefine them**.

A Foundational PR may touch the trust root, but only one trust-root object
per PR, and it must include a justification, an equivalence theorem (when
plausible), and an explicit version bump in `spec/target.toml`.

---

## Rule 1 — No unconditional claim without closed final term

A theorem of type `ComplexityInterfaces.P_ne_NP` counts as an unconditional
proof of P ≠ NP **only if**:

1. it is a `theorem` (not an `axiom`, `opaque`, or `noncomputable def`),
2. it has zero explicit arguments,
3. it has zero implicit arguments **other than the whitelisted typeclass
   instances** listed in `spec/implicit_assumption_channels.md`,
4. its dependency closure imports no `axiom` outside
   `spec/target.toml::[axioms].allowed`,
5. its dependency closure imports no theorem from
   `pnp3/RefutedPredicates/`, `pnp3/Magnification/AuditRoutes/`,
   `pnp3/Tests/`, or `pnp3/Barrier/`,
6. its dependency closure does not pass through a `FinalPayloadProvider` or
   any object marked `@audit-class: refuted-channel`.

Documents (Markdown, LaTeX, READMEs) that claim unconditional P ≠ NP must
fail the doc-honesty linter unless such a term exists. A placeholder of the
form `axiom P_ne_NP_unconditional : ...` is forbidden.

---

## Rule 2 — No goalpost moving

A failed candidate must be archived as a `NoGoLog` entry. It must **not** be
"fixed" by:

- weakening or strengthening `ResearchGapWitness`,
- adding fields to `ResearchGapWitness`,
- changing `PpolyDAG`, `PpolyFormula`, or any size measure,
- adding a new hypothesis to the final theorem,
- renaming a refuted route to look new,
- replacing the target with a closely related but inequivalent one.

The target is fixed. Only candidates change.

A Foundational PR may legitimately change a trust-root definition, but only
under Rule 0.

---

## Rule 3 — Candidates live only under `Candidates/`

A candidate proof attempt must live exclusively under

```
pnp3/Candidates/<method>/<id>/
```

with the following minimum layout:

- `proof.lean`
- `manifest.toml`
- `sketch.md`
- `barrier_certificate.md`
- `self_attack.md`

A Candidate PR **must not** add public endpoints, instances, or theorems
to:

- `pnp3/Magnification/`
- `pnp3/LowerBounds/`
- `pnp3/Complexity/`
- `pnp3/ThirdPartyFacts/`
- `pnp3/Spec/`

A Candidate PR may import these modules read-only.

---

## Rule 4 — One small `SourceTheorem` with dependency closure

Each candidate exposes exactly one main source theorem and one bridge:

```
SourceTheorem_<id>            -- the candidate's mathematical claim
gap_from_<id>
  : SourceTheorem_<id> → ResearchGapWitness
```

Size limits, evaluated according to `spec/source_theorem_size_policy.md`:

- `K_stmt = 40` lines for the statement of `SourceTheorem_<id>`.
- `K_exp  = 200` lines for the dependency-closed expansion of
  `SourceTheorem_<id>` plus everything `gap_from_<id>` needs from candidate-
  local code.

Trusted boundaries (not counted): `pnp3/Spec/FrozenSpec.lean`, the stdlib
whitelist, the `Core` whitelist.

If the limit is exceeded, the PR status becomes `human-review-required`,
not auto-rejected.

---

## Rule 5 — No arbitrary witness quantification without provenance

Routes whose statements universally quantify over `PpolyWitness`,
`PpolyFormula`, or any "witness for an arbitrary `L ∈ P/poly`" object are
suspect. They are accepted only if accompanied by a formal lemma showing
that truth-table / singleton / hardwired witnesses are excluded by the
candidate's predicate. For example:

```
no_truth_table_hardwiring :
  ¬ ∃ W, TruthTableHardwired W ∧ Predicate W
```

Without such a lemma the candidate is `human-review-required`.

---

## Rule 6 — Refuted routes are audit artifacts only

A theorem of the shape

```
RefutedHypothesis → P_ne_NP
```

(where `RefutedHypothesis → False` is provable in the repository) is **not
mathematical progress**. It is audit-only.

All refuted/vacuous endpoints must be relocated to:

- `pnp3/RefutedPredicates/`
- `pnp3/Magnification/AuditRoutes/`
- `pnp3/Tests/`
- `pnp3/Barrier/`
- `pnp3/Docs/`

and renamed with the prefix `RefutedRoute_*`, `Vacuous_*`, or
`AuditOnly_*`.

No file outside those directories may import them transitively (enforced
by the verifier).

---

## Rule 7 — Executable barrier certificates and bounded human review

Every candidate must include a `barrier_certificate.md` that, where
possible, is backed by an executable Lean witness:

- For natural-proof-shaped attempts: which of `constructivity`, `largeness`,
  `usefulness` is broken, and the formal lemma demonstrating the break.
- For relativization-shaped attempts: which step fails to relativize.
- For algebrization-shaped attempts: which step breaks under a multilinear-
  extension oracle.

Human-review queue limits:

- At most **3** open `human-review-required` candidates at any time.
- SLA: **14 days** per item.
- Expired review **≠ refuted**. Expired = archived; resubmission allowed.
- Foundational PRs use a **separate** human-review queue.

---

## Rule 8 — Collapse consequences are not contradictions

A theorem of the shape "if `NP ⊆ P/poly` then PH collapses" is a
**collapse consequence**, not a contradiction. It does **not** prove
P ≠ NP. To use such a result inside a candidate, the candidate must also
exhibit a real contradiction; appeals to "PH-collapse is widely believed
unlikely" are not accepted.

---

## Rule 9 — Every failure becomes a structured `NoGoLog` entry

A failed or refuted candidate must produce a `NoGoLog` entry conforming to
`spec/nogolog_schema.json`. Required fields:

- `failure_class`
- `structural_pattern`
- `counterexample_family`
- `why_generalizes`
- `regression_test` (file path, or null with a justification)
- `applicable_spec_version`
- `attack_suite_version`

`NoGoLog` is append-only. Entries are not retroactively edited; corrections
are added as new entries that reference the original.

---

## Rule 10 — `NoGoLog` is a managed product; `ResearchGapWitness` is the target product

Two products, two purposes:

- **`NoGoLog`** prevents drift, deduplicates dead ends, and accumulates
  structural knowledge. It is a managed product but **not** a substitute for
  the target.
- **`ResearchGapWitness`** is the target. The project ends when its
  `dagSeparation` field is honestly inhabited and Rule 1 is satisfied.

A large `NoGoLog` is not a proof of progress on the target.

---

## Rule 11 — Joint candidates require independent validation

If a candidate has the shape

```
A ∧ B → ResearchGapWitness
```

then `A` and `B` must each pass intake **independently**. The candidate
must include a non-vacuity probe demonstrating that:

- removing `A` makes the proof fail,
- removing `B` makes the proof fail.

Otherwise the joint candidate is treated as the conjunct that actually
carries the weight, with the other conjunct flagged as decorative.

---

## Rule 12 — Generator/Critic separation and diversity

When automated agents are introduced (after the verifier exists):

- Generator and Critic are separate processes.
- Critic does not see Generator's chain-of-thought or scratch state. It
  receives only the final intake package (Rule 3 layout).
- Generator and Critic must use different model snapshots, different prompt
  templates, and different random seeds.

Generator/Critic identity is recorded in the `NoGoLog` entry.

---

## Rule 13 — Reproducibility

A candidate must verify in a **fresh worktree** with no local state. The
verifier is run twice; both runs must produce identical pass/fail and
identical artifact hashes. Any nondeterminism (e.g. ambient `Nat` vs.
`Nat.succ` reduction order) is treated as a verifier bug, not a candidate
bug.

---

## Rule 14 — Time-locked verification

A candidate certificate is valid only against a specific
`attack_suite_version` recorded at the time of verification. When the attack
suite is extended:

- All `accepted` and `under-review` candidates are demoted to
  `requires-revalidation`.
- Revalidation is mandatory before the next public claim.

This is to prevent silent regressions when new probes are added to the
attack suite.

---

## Rule 15 — Prior-work disclosure

Every candidate's `manifest.toml` must contain a `[prior_work]` section
listing known papers, preprints, archived attempts, and similar
`SourceTheorem` skeletons.

If a similar approach is already refuted in the literature or in
`NoGoLog`, the candidate must explain in `sketch.md` what is structurally
different. "I did not check" is not a valid answer; it triggers human
review.

---

## Rule 16 — No hidden payload providers

A candidate must not hide mathematical assumptions through any of the
following channels:

- `class`, `instance`, `default_instance`, `attribute [instance]`
- `Fact ...`
- objects whose name contains `Provider`, `Payload`, `Default`, `Source`,
  `Witness`, `Gap`
- `opaque` declarations
- `noncomputable def` declarations
- implicit arguments that are not in the whitelist of
  `spec/implicit_assumption_channels.md`
- typeclass synthesis from candidate-local typeclasses
- global attributes

The pattern

```
theorem candidate_final [SomePayloadProvider] : P_ne_NP := ...
```

is forbidden. Every mathematical assumption must appear explicitly in the
statement of `SourceTheorem_<id>` or in the explicit hypothesis list of
`gap_from_<id>`.

The verifier renders both with `pp.all` and rejects any statement whose
rendered form depends on a non-whitelisted typeclass over a frozen-target
type.

---

## Mutually exclusive PR scopes

A single PR must have exactly one of these scopes:

- **governance/spec** — markdown, toml, json, csv, schemas, plans
- **cleanup/audit** — refuted-route renames, audit-folder moves, doc fixes
- **foundational** — touches a trust-root identifier (Rule 0)
- **verifier/test** — adds or modifies the verifier or smoke probes
- **candidate** — lives under `pnp3/Candidates/<method>/<id>/`
- **docs** — documentation only, no code changes

CI must reject PRs that mix Foundational and Candidate scope. Mixing other
pairs is discouraged but not auto-rejected.

---

## What is forbidden during this phase

The following moves are explicitly forbidden until the listed prerequisite
is satisfied:

| Move                                              | Prerequisite                              |
| ------------------------------------------------- | ----------------------------------------- |
| Claim unconditional P ≠ NP in any document        | Rule 1 satisfied                          |
| Touch Lean proofs in this phase                   | Phase 0 governance package merged         |
| Add a candidate                                   | Phase 0 cleanup PR 1–6 merged             |
| Implement `FrozenSpec.lean`                       | Phase 0 cleanup merged                    |
| Run an auto-research generator                    | Verifier exists and PR 1–7 merged         |
| Resurrect a refuted predicate under a new name    | Always forbidden                          |
| Add a `Fact`/`Provider`/`Payload` to the trust    |                                           |
|   root                                            | Always forbidden                          |

---

## Five-line summary

1. Generate lemmas, not claims.
2. Verify terms, not prose.
3. Reward refutations, not optimism.
4. No hidden payload providers.
5. No goal drift.
