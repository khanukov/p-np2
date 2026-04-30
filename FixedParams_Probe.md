# FixedParams Probe — research plan

This is the **first** mathematical experiment of the project. It does
**not** start until Phase 0 cleanup PR 1–6 are merged and the verifier
shell exists.

The goal is to determine whether the route

```
FormulaSupportBoundsPartial_fromPipeline_fixedParams ac0 sb
```

can be salvaged **without** the overbroad uniform provenance condition
that currently makes it equivalent to the refuted route
`FormulaSupportBoundsPartial_fromPipeline`.

The leak theorem
`fixedParams_entails_old_under_uniformProvenance`
(`pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean` ≈ line 502)
shows the precise failure: combining `fixedParams ac0 sb` with the
overbroad uniform provenance recovers the refuted predicate. Any
salvage strategy must therefore weaken the provenance side without also
weakening the formula side back into hardwiring.

---

## 1. Setup and notation

Throughout this probe we use the symbols already in the active code:

- `ac0 : ThirdPartyFacts.AC0Parameters`
- `sb` — a switching/support-bound bundle as in
  `FormulaSupportBoundsPartial_fromPipeline_fixedParams`
- `OverbroadUniformFormulaProvenance ac0` — the overbroad provenance
  abbreviation defined in
  `pnp3/Magnification/UnconditionalResearchGap.lean`
- `Π` — a candidate replacement for `OverbroadUniformFormulaProvenance ac0`

We seek a `Π` for which

```
fixedParams ac0 sb ∧ Π → ResearchGapWitness
```

might still go through, while satisfying the four constraints in §2.

---

## 2. Constraints on Π

Π is admissible only if **all four** of the following hold:

1. **Π does not accept truth-table / singleton / hardwired witnesses.**
   Formally, the candidate must produce a Lean lemma of the shape

   ```
   Π_excludes_hardwiring :
     ¬ ∃ W, TruthTableHardwired W ∧ Π_holds_for W
   ```

   The exact form depends on Π; the important part is that hardwiring
   is structurally impossible under Π.

2. **Π is not stronger than `OverbroadUniformFormulaProvenance ac0`.**
   Formally:

   ```
   Π_strictly_weaker :
     OverbroadUniformFormulaProvenance ac0 → Π
     ∧ ¬ (Π → OverbroadUniformFormulaProvenance ac0)
   ```

   Strict weakening is required because if Π is at least as strong as the
   overbroad version, the leak theorem applies and the route reduces to
   the refuted predicate.

3. **`fixedParams ac0 sb ∧ Π` does not imply any of the six refuted
   predicates** in `spec/target.toml::[refuted_predicates]`. Stated
   negatively as a no-go check.

4. **Bridge.** There exists a non-trivial Lean proof of

   ```
   gap_from_FixedParamsProbe :
     fixedParams ac0 sb ∧ Π → ResearchGapWitness
   ```

   that is not a thin re-statement of the refuted route.

---

## 3. Outcomes

The probe terminates in exactly one of three outcomes, A / B / C.

### Outcome A — route dead

A formal lemma is produced of the shape

```
Π_route_dies_via_hardwiring :
  ∀ Π satisfying constraint (2),
    fixedParams ac0 sb ∧ Π → False  -- via hardwiring counterexample
```

or, more realistically, a counterexample family inhabiting a forbidden
shape that defeats every candidate Π in a stable region. Outcome A is
recorded as:

- a `NoGoLog` entry with `failure_class = "refuted_route"` or
  `"hardwiring"`,
- a regression test in `pnp3/Tests/FixedParams_Probe_NoGo.lean`,
- an entry under `[refuted_predicates]` in `spec/target.toml` if the
  argument generalizes to a stable family.

The route family is then blacklisted at the verifier level.

### Outcome B — non-dead but uninteresting

A Π satisfying constraints (1)–(3) exists, the bridge in (4) is
provable, but Π carries **no new mathematical content** with respect to
known guards. Outcome B is admitted only if **at least one** of the
following two reductions is formally proved.

- **B1 — equivalence to known guard combination.**

  ```
  Π_equiv_known :
    Π ↔ KnownGuardCombination
  ```

  where `KnownGuardCombination` is a conjunction/disjunction of guards
  drawn **only** from `spec/known_guards.toml` whose `status =
  "accepted"`.

- **B2 — factorization through a known guard.**

  ```
  Π_factors_through_known :
    fixedParams ac0 sb ∧ Π → ExistingKnownGuard
  ```

  where `ExistingKnownGuard` again must be in
  `spec/known_guards.toml::[guards.*]` with `status = "accepted"`.

If neither B1 nor B2 is provable, Outcome B is **not** the conclusion;
the candidate is `under-investigation`, not an audit artifact.

Outcome B is recorded as:

- a survivor-history entry with `final_status = "refuted"`,
- a `NoGoLog` entry with `failure_class = "vacuity"`,
- the formal reduction (B1 or B2) lives under
  `pnp3/Magnification/AuditRoutes/`.

### Outcome C — nontrivial provenance found

A Π satisfying constraints (1)–(4) exists, hardwiring is provably
excluded, and Π is **not** reducible to known guards (formally: neither
B1 nor B2 holds). In this case Π becomes a candidate `SourceTheorem`
or a non-trivial component of one.

Outcome C is recorded as:

- a survivor-history entry with `final_status = "survived"` (pending
  Critic attacks),
- a candidate package
  `pnp3/Candidates/fixed_params_probe/<id>/` with the standard layout
  (Rule 3),
- the bridge (4) becomes `gap_from_<id>` of that package.

Outcome C does **not** prove P ≠ NP. It produces a candidate that the
Critic phase of the project will then attempt to refute.

---

## 4. Prerequisites

The probe must not start before:

- `RESEARCH_CONSTITUTION.md` is merged and frozen.
- `spec/target.toml`, `spec/known_guards.toml`, and
  `spec/source_theorem_size_policy.md` are merged.
- Phase 0 PR 1 (doc-honesty linter) is merged.
- Phase 0 PR 2 (typeclass-payload quarantine) is merged.
- Phase 0 PR 3 (refuted-route renames) is merged.
- The verifier shell from Phase 0 PR 5 is in place.
- The provider audit annotations from Phase 0 PR 6 are in place.

Starting earlier is forbidden because the probe interacts directly with
the refuted predicates, the provenance shape, and the provider classes
that PR 1–6 quarantine.

---

## 5. Deliverables

1. `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean` (audit-only
   home for the leak / Outcome-A artifacts).
2. `pnp3/Tests/FixedParams_Probe_NoGo.lean` (regression test, Outcome A).
3. If Outcome B: a formal reduction file under
   `pnp3/Magnification/AuditRoutes/` plus a `NoGoLog` entry.
4. If Outcome C: a candidate package
   `pnp3/Candidates/fixed_params_probe/<id>/` with the Rule 3 layout.

In all three outcomes the probe ends with at least one Lean artifact
under verifier control. The probe is not "complete" until the verifier
has been re-run on a fresh worktree (Rule 13) and the artifact's hash
recorded against the active `attack_suite_version` (Rule 14).

---

## 6. Anti-goals

The probe must **not**:

- weaken or strengthen `ResearchGapWitness`,
- redefine `fixedParams`, `sb`, or `OverbroadUniformFormulaProvenance`,
- add a new refuted-route shortcut by renaming the leak theorem,
- introduce a `class`/`instance`/`Fact` carrying the provenance,
- claim Outcome C without the §3.C non-reducibility proof,
- declare Outcome B with an informal "this looks like a known guard"
  argument; only formal B1 or B2 reductions are accepted.

---

## 7. Failure modes that have been seen before

These should be screened out before any new attempt.

- **Renaming the predicate.** Replacing
  `OverbroadUniformFormulaProvenance` with a structurally identical
  `UniformFamilyProvenance` does not produce Outcome C; it produces a
  Rule-2 violation.
- **Quantifier shuffling.** Moving the universal over `PpolyFormula`
  inside a stronger predicate keeps the hardwiring witness alive; the
  Outcome A counterexample still applies.
- **Existential dressing.** Wrapping the predicate in
  `∃ family, family is AC0 ∧ ...` without excluding singleton families
  hits Outcome A immediately.

Each of these has appeared in informal explorations and should be
captured as `NoGoLog` entries the moment they re-appear.
