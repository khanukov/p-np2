# Critic report — fp3b1_log_width_hardwiring_lift / S11 integration

> Six-attack Critic report per `spec/critic_protocol.md` §1–3 against
> the integration artefact
> `Pnp3.Magnification.AuditRoutes.LogWidthAdversary.logWidthAdversary_satisfies_diversity`
> at `pnp3/Magnification/AuditRoutes/LogWidthAdversary/Composition.lean:208`.

## Attack 1: Hidden-payload attack

- **status:** `no break found`
- **summary:** No `class`, `instance`, `Fact`, `opaque`, default
  instance, or typeclass-payload smuggling.  The proof is plain
  structural induction (`prefixAnd_support_card`,
  `prefixAnd_support_lt`) plus Finset arithmetic plus direct
  application of the two parametric reducers
  `adversary_support_unbounded` (S8) and
  `adversary_support_below_n_io` (S9).
- **evidence:**
    - Composition.lean uses no `class` or `instance` declarations
      (verified by `rg "^class |^instance " pnp3/Magnification/AuditRoutes/LogWidthAdversary/Composition.lean`).
    - `scripts/check.sh` Step 7 (`check_typeclass_payload_quarantine.sh`)
      runs across `pnp3/Magnification/AuditRoutes/` and stays green;
      the new module does NOT introduce a quarantined payload pattern.
    - The theorem's body is `⟨adversaryWitness_v_natlog2_support_unbounded,
      adversaryWitness_v_natlog2_support_below_n_io⟩` — a literal pair
      of two named lemmas, not a `Classical.choose`-driven existential
      smuggling argument.

## Attack 2: Hardwiring attack

- **status:** `no break found`
- **summary:** The candidate `adversaryWitness_v_natlog2` IS itself
  the hardwiring witness, but at the `prefixAnd`-on-log-width
  level rather than full `ttFormula`.  The Critic attack here would
  be "is the construction degenerate via a singleton-truth-table
  trick masking its real cost?".  It is not: the polynomial bound
  `polyBound n := 2*n + 1` is genuinely linear (not constant), the
  family is non-constant for `n ≥ 1` (the conjunction `x₀ ∧ x₁ ∧ … ∧
  x_{logWidth(n)-1}` evaluates non-trivially), and the size cap is
  proven, not asserted.
- **evidence:**
    - `adversaryFamily_v_natlog2_size_le` (Family_NatLog2.lean:89–97)
      gives `size (adversaryFamily_v_natlog2 n) = 2 * logWidth(n) + 1
      ≤ 2 * n + 1`, kernel-checked.
    - `adversaryFamily_v_natlog2_support_card`
      (Composition.lean:99–103) gives
      `(support (adversaryFamily_v_natlog2 n)).card = logWidth(n)`,
      kernel-checked.  Empty support would have killed unboundedness;
      it does not.
    - `correct := fun _ _ => rfl` in `adversaryWitness_v_natlog2`
      (Family_NatLog2.lean:104–109) is judgmental, not a `Classical`-
      mediated trick.  The language is *defined* as the family's
      `eval`, so semantic correctness is by reflexivity.

## Attack 3: KnownGuards-factorization attack

- **status:** `no break found`
- **summary:** The candidate under review here is the theorem
  `logWidthAdversary_satisfies_diversity`, an OBSTRUCTION — it
  proves a previously-proposed candidate provenance filter
  (`InSupportFunctionalDiversity`) is satisfied by a hardwiring
  shape and hence too coarse.  The KnownGuards-factorization
  attack asks whether a candidate provenance factors vacuously
  through `HardwiringGuard`; the candidate here is NOT a
  provenance proposal but its rejection witness, so the attack
  does not flag a defect.  The factorisation observation (that
  the rejected filter accepts a `HardwiringObstruction`-style
  family) IS the scientific content of the theorem, exposed by
  it rather than evading it.
- **evidence:**
    - `Composition.lean:208` proves
      `InSupportFunctionalDiversity adversaryWitness_v_natlog2`
      for a witness that is itself a polynomial-size truth-table-
      conjunction on a log-width window.
    - The existing `HardwiringObstruction` and `HardwiringGuard`
      (FixedParamsProbe.lean:92–113) document that
      `gapPartialMCSP_Language` admits truth-table hardwired
      `PpolyFormula` witnesses; the new theorem extends this to a
      family-level shape that ALSO satisfies the candidate filter,
      proving the filter is too coarse to exclude such shapes.
    - This is the formal lift of `outputs/nogolog.jsonl::NOGO-000003`:
      the new entry `NOGO-000004` (with `supersedes = "NOGO-000003"`)
      flips the status to `formalized` and pins the formal witness
      at `Composition.lean:208`.  No new candidate provenance is
      proposed here, so there is nothing to factor out vacuously.

## Attack 4: Natural-proof / relativization / algebrization barrier audit

- **status:** `attack not applicable`
- **summary:** The theorem is a Lean-internal kernel-checked
  obstruction against a CANDIDATE FILTER, not a proof of any
  complexity-class separation.  No oracle quantifier, no algebraic
  extension, no natural-property predicate is touched.  The three
  classical barriers are not in scope.
- **evidence:**
    - The theorem statement
      `InSupportFunctionalDiversity adversaryWitness_v_natlog2`
      contains no oracle, no algebrization parameter, and no
      natural-property predicate; it is a pure Finset cardinality
      claim composed with a polynomial size bound.

## Attack 5: Collapse-not-contradiction audit

- **status:** `no break found`
- **summary:** The theorem's conclusion is
  `InSupportFunctionalDiversity adversaryWitness_v_natlog2`, a
  positive statement about a specific witness — there is no
  `False`-conclusion that could be a vacuous collapse.  No part of
  the proof relies on `Classical.choose` of a non-trivial existential
  in a way that could pretend a stronger conclusion than what is
  proven.
- **evidence:**
    - The conclusion is constructive: `⟨h₁, h₂⟩` of two named
      lemmas, each of which has explicit witnesses
      (`logWidth_unbounded` and `logWidth_lt_self` produce
      concrete `n` values).
    - No `Classical.choice` is consumed beyond what the ambient
      Mathlib `Finset` API requires, and the axiom-surface dump
      (`scripts/check.sh` Step 14) records only `propext`,
      `Classical.choice`, `Quot.sound` — the standard kernel
      axiom set.

## Attack 6: Vacuity / source-theorem rephrasing audit

- **status:** `no break found`
- **summary:** The integration does not create or rephrase any
  `SourceTheorem_*` and does not introduce a bridge to
  `ResearchGapWitness`.  The seed pack §6 forbidden scope is
  respected: no `gap_from_*`, no FP-4 promotion, no
  `ProvenanceFilter_v1` flip from `informal` to `accepted`.
- **evidence:**
    - `rg "gap_from|SourceTheorem|ResearchGapWitness"
       pnp3/Magnification/AuditRoutes/LogWidthAdversary/`
      returns nothing.
    - `spec/known_guards.toml::guards.ProvenanceFilter_v1`
      remains at `status = "informal"`, `formal_name = ""`.
    - No `pnp3/Candidates/<id>/` directory created by this seed
      pack.

## Verdict

- **critic_status:** `pass`
- **next_recommended_action:** Begin FP-3b.3 — design a stronger
  filter `ProvenanceFilter_v2` that excludes log-width truth-
  table-shaped families.  The new bar is now formal and can be
  used as a self-attack target in the next seed pack.
