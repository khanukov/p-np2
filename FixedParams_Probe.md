# FixedParams Probe — research plan

> **FP-1 status: COMPLETE.**
>
> - `spec/known_guards.toml::guards.HardwiringGuard` is `accepted` and
>   points to `pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean:218`
>   (truth-table hardwiring construction, Probe 2 of the falsifiability
>   audit).
> - Audit-only surface lives at
>   `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean` and
>   exposes the canonical names `FixedParamsRoute`,
>   `OverbroadUniformProvenance`, `HardwiringObstruction`,
>   `HardwiringGuard`, `hardwiring_guard_holds`.
> - Smoke skeleton `pnp3/Tests/FixedParams_Probe_NoGo.lean` checks
>   that the audit names elaborate at the expected types.
>
> **FP-2 status: COMPLETE — Outcome A baseline only.**
>
> - The audit module now also exposes
>   `NoGo_FixedParamsRoute_with_OverbroadUniformProvenance`, a
>   re-export of `Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe.false_of_fixedParams_and_uniformProvenance`
>   under the canonical Outcome-A audit name.
> - `FixedParams_Probe_NoGo.lean::fp2_outcome_a_overbroad_baseline`
>   regression-tests the chain.
> - **Scope:** the FP-2 result kills the route only for the single
>   candidate provenance `Π = OverbroadUniformProvenance ac0`. It is
>   **not** a claim that the FixedParams route is dead in general for
>   every `Π`. An honest Outcome A for an arbitrary `Π` requires
>   additionally proving `Π → OverbroadUniformProvenance ac0`, which
>   is in general open and is the FP-3 / FP-4 entry point.
> - **What FP-2 does NOT claim:**
>     * No `gap_from_*` bridge.
>     * No `SourceTheorem_*`.
>     * No `ResearchGapWitness` constructor.
>     * No edits to `ResearchGapWitness`, `Complexity/Interfaces`,
>       `UnconditionalResearchGap.lean`, or
>       `FormulaSupportBoundsPartial_fromPipeline_fixedParams`.
>     * No new final endpoint.
>     * No Outcome B / C.
>     * The proof is `False`, not `P ≠ NP`.
>
> NoGo entry `NOGO-000001` recorded in `outputs/nogolog.jsonl` with
> `failure_class = "hardwiring"` and `regression_test =
> "pnp3/Tests/FixedParams_Probe_NoGo.lean"`.
>
> **FP-3 status: SURFACE ONLY (no formal claim).**
>
> - `spec/known_guards.toml::guards.ProvenanceFilter_v1` is now an
>   active *informal* entry (`status = "informal"`, `formal_name =
>   ""`, `outcome_b_usage = "not_admissible"`,
>   `standalone_factorization_target = false`).
> - `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean` carries a
>   docstring anchor naming this future predicate's home but
>   **defines no Lean `Prop`, `def`, `abbrev`, or `theorem`** under
>   that name.
> - **Promotion to `status = "accepted"` is forbidden** until ALL of
>   the four conditions in the registry's "informal → accepted"
>   checklist are met (real Lean artifact, genuinely conditional,
>   `standalone_factorization_target = true`, Foundational PR with
>   spec-version bump).
> - **What FP-3 surface DOES NOT claim:**
>     * No Lean predicate for `ProvenanceFilter_v1`.
>     * No `gap_from_*` bridge.
>     * No `SourceTheorem_*`.
>     * No `ResearchGapWitness` constructor.
>     * No new NoGoLog entry.
>     * No new regression test.
>     * No Outcome B / Outcome C — the surface is pre-Outcome work.
> - The first ACTUAL FP-3 step is a separate PR that proposes a
>   concrete Lean shape for `ProvenanceFilter_v1` together with a
>   non-tautology proof that it is not inhabited unconditionally.
>   That PR is OUT OF SCOPE for the FP-3-surface preparation here.
>
> **FP-3 actual status: C-CANDIDATE WITH CAVEATS (do NOT promote to FP-4).**
>
> One concrete Lean shape, `FP3Attempt.InSupportFunctionalDiversity`,
> is now committed to
> `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean` under the
> audit-only `FP3Attempt` namespace.  The four-test self-attack
> protocol gives:
>
> | Test | Result | Notes |
> | ---- | ------ | ----- |
> | 1. No hidden payload                  | PASS    | only `FormulaCircuit.support`, `Nat`, `InPpolyFormula` fields are referenced; no `ResearchGapWitness`, no `NP_not_subset_PpolyDAG`, no `P_ne_NP`, no `¬ PpolyDAG`, no separation. |
> | 2. Not a tautological hardwiring guard | PASS    | the candidate is a positive structural condition (support function unbounded but eventually sublinear), not `¬ TruthTableHardwired W`. |
> | 3. Hardwiring attack defeated         | PASS    | abstract Lean theorem `FP3Attempt.InSupportFunctionalDiversity_excludes_uniformPolyBound` proves any record with a uniformly-bounded `polyBound` violates the diversity condition.  The Probe-2 hardwired witness has `polyBound m = if m = n₀ then c₀_size else 1`, hence is bounded. |
> | 4. KnownGuards factorization          | PASS    | the candidate does not factor through `HardwiringGuard` (different shape — diversity vs Rule-5 exclusion).  Currently no other `accepted` guard exists in `spec/known_guards.toml`. |
>
> **Classification: Outcome C-candidate (formal).**
>
> But:
>
> 1. **Multi-slice hardwiring caveat.**  The Probe-2 hardwiring is
>    *single-slice*: hardwired only at `n = n₀`, `const false`
>    elsewhere.  An *alternating-slice* hardwired record (TT at every
>    second length, `const false` at the others) would have an
>    unbounded support function (large at hardwired lengths) AND
>    `support n < n` at the unhardwired lengths, satisfying the
>    candidate filter.  The active code base does NOT construct such a
>    record, so the `FP3Attempt` exclusion lemma still defeats every
>    hardwiring attack realised in code today, but the candidate is
>    NOT a structural exclusion of all conceivable hardwiring shapes.
> 2. **Bridge is not yet constructed.**  Constraint (4) of §2 requires
>    a non-trivial `gap_from_FixedParamsProbe :
>    fixedParams ac0 sb ∧ Π → ResearchGapWitness`.  No such bridge has
>    been attempted in this round; that work is FP-4 (candidate
>    package + bridge + barrier certificate).
> 3. **Vacuity proximity check (informal).**  The candidate filter
>    enforces `support` properties; the route `FixedParamsRoute ac0 sb`
>    concludes a polylog support bound on the matching AC0 family at
>    `n = partialInputLen p`.  These two `support` quantities are
>    semantically related but not directly equal; the candidate is
>    *not* simply a re-statement of the route's conclusion.  However,
>    a careless bridge construction could trivialise the conclusion's
>    support-bound part.  Any FP-4 bridge attempt MUST carry an
>    explicit non-vacuity argument (the conclusion has additional
>    parts: `LocalCircuitSmallEnough` and `support ≤ inputLen / 4`).
>
> **Therefore FP-4 is NOT started in this PR.**  The candidate stays
> audit-only under `FP3Attempt.*`; `spec/known_guards.toml::guards.ProvenanceFilter_v1`
> remains `status = "informal"` with `formal_name = ""`.  Promotion to
> `accepted` is forbidden until the multi-slice caveat is resolved
> (e.g. by strengthening the diversity condition to bound *both*
> directions of the support function — not only "support unbounded"
> but also "support density does not concentrate on TT-shaped
> lengths") and a non-vacuous bridge is exhibited.
>
> NoGo entry `NOGO-000002` recorded in `outputs/nogolog.jsonl` with
> `failure_class = "hardwiring"` (multi-slice caveat) and
> `regression_test = "pnp3/Tests/FixedParams_Probe_NoGo.lean"`,
> capturing the multi-slice hardwiring caveat as a known weakness of
> the candidate (the structural pattern is "alternating-slice
> hardwiring evades single-slice support filter"; the schema-allowed
> failure_class value `hardwiring` is used because the underlying
> attack family is still truth-table hardwiring, just at multiple
> slices).

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
  `spec/known_guards.toml::[guards.*]` with `status = "accepted"`
  AND `standalone_factorization_target = true`.

  > **Tautology caveat (added during v0.1 Machine Revalidation):**
  > `HardwiringGuard` is a Lean theorem proved unconditionally via
  > `Pnp3.Magnification.AuditRoutes.FixedParamsProbe.hardwiring_guard_holds`,
  > so its `standalone_factorization_target` flag in
  > `spec/known_guards.toml` is `false`. Any `Π → HardwiringGuard`
  > factorization is vacuous and is **not** an admissible Outcome B.
  > A real Outcome B requires a guard that is genuinely conditional
  > (a `Prop` whose body is NOT already a Lean theorem); see the
  > deferred `ProvenanceFilter_v1` placeholder in the registry.
  > `HardwiringGuard` may still appear in an Outcome B body, but
  > only conjoined with another non-tautological guard such that
  > the conjunction is itself non-trivial.

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

---

## 8. FP-3 actual report — `SupportFunctionalDiversity` candidate

This is the FP-3 actual self-attack report.  The candidate is
audit-only and is NOT promoted to `spec/known_guards.toml`.  See the
status block at the top of this document for the summary verdict
(C-candidate with caveats; do NOT start FP-4).

### 8.1 Proposed Lean shape

`pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean` defines, under
the experimental namespace `FP3Attempt`:

```lean
def InSupportFunctionalDiversity {L : Pnp3.ComplexityInterfaces.Language}
    (w : InPpolyFormula L) : Prop :=
  (∀ B : Nat, ∃ n, B < (FormulaCircuit.support (w.family n)).card) ∧
  (∀ N : Nat, ∃ n, N ≤ n ∧ (FormulaCircuit.support (w.family n)).card < n)
```

The two conjuncts say, respectively, that the support-cardinality
function `n ↦ |support (w.family n)|` is unbounded **and** eventually
sublinear in `n`.

The candidate is defined at the `InPpolyFormula` record level rather
than the existential `PpolyFormula L = ∃ _ : InPpolyFormula L, True`
because `Classical.choose` of the latter is opaque and gives no
handle on the underlying `family`.  Lifting to a Prop on
`PpolyFormula L` is straightforward (apply to `Classical.choose h`)
but the regression machinery operates at the record level.

### 8.2 What it forbids

The candidate excludes two degenerate shapes simultaneously:

* **Bounded-support shapes.**  The single-slice truth-table
  hardwired witness from Probe 2 has `family m = ttFormula L_{n₀}`
  at `m = n₀` (support cardinality `n₀`) and `family m = const false`
  elsewhere (support cardinality `0`).  Image of the support function
  is `{0, n₀}`, hence bounded by `n₀`.  The unboundedness conjunct
  fails, and the candidate excludes this shape.
* **Always-saturated shapes.**  A record with `family m = ttFormula
  L_m` at every length `m` (truth-table hardwired at every slice)
  has support cardinality `m` at every length, hence `support n < n`
  is never witnessed.  The eventually-sublinear conjunct fails, and
  the candidate also excludes this shape.

### 8.3 Why truth-table hardwiring should fail (Test 3 formal)

The key formal artifact is `FP3Attempt.InSupportFunctionalDiversity_excludes_uniformPolyBound`:

```lean
theorem InSupportFunctionalDiversity_excludes_uniformPolyBound
    {L} (w : InPpolyFormula L) (B : Nat)
    (hBound : ∀ n, w.polyBound n ≤ B) :
    ¬ InSupportFunctionalDiversity w
```

Proof sketch (5 lines):

```
support card ≤ size  (FormulaCircuit.support_card_le_size)
size ≤ polyBound n   (InPpolyFormula.family_size_le)
polyBound n ≤ B      (hypothesis)
⇒ support card ≤ B   (transitivity)
⇒ ∀ B', ∃ n, B' < support card  fails for B' = B  (omega)
```

The Probe-2 hardwired witness has `polyBound m = if m = n₀ then
c₀_size else 1`, hence is uniformly bounded by `max(c₀_size, 1)`.
Therefore the abstract lemma directly defeats the single-slice
hardwiring attack.

### 8.4 Why this is not hidden payload (Test 1 formal)

The candidate's body references only:

* `FormulaCircuit.support` (line 99 of `pnp3/Complexity/Interfaces.lean`)
* `Finset.card`
* `Nat`
* `InPpolyFormula.family` and `InPpolyFormula.polyBound` (record fields)

It does NOT reference `ResearchGapWitness`, `NP_not_subset_PpolyDAG`,
`P_ne_NP`, `P_ne_NP_unconditional`, `P_ne_NP_final`, `¬ PpolyDAG`,
nor any quantifier of the shape `∀ C : PpolyDAG, ...`.  No structure
field has type `ResearchGapWitness` or any Rule-16 hidden-payload
shape.  The verifier guard `scripts/check_candidate_rule16.sh` would
not flag this candidate (the file is under `pnp3/Magnification/AuditRoutes/`,
not `pnp3/Candidates/`, so the check does not technically run, but
the structural property holds).

### 8.5 Why this is not just KnownGuardCombination (Test 4 formal)

The only guard in `spec/known_guards.toml` with `status = "accepted"`
is `HardwiringGuard`, which states that every Partial-MCSP slice
admits *some* `PpolyFormula` witness.  `HardwiringGuard` carries the
tautology caveat (`outcome_b_usage = "obstruction_only"`,
`standalone_factorization_target = false`), so it is not an
admissible Outcome-B factorization target in the first place.

`InSupportFunctionalDiversity` is structurally distinct: it is a
property of an `InPpolyFormula` record, not a claim about all slices,
and it asserts *diversity* across input lengths rather than
*existence* at each length.  No reduction `Π ↔ HardwiringGuard ∧ ...`
or `Π → HardwiringGuard` factors `Π` through known guards in any
Outcome-B-admissible sense.

### 8.6 Expected bridge to FixedParams (constraint 4 of §2)

NOT exhibited.  This is intentional: the bridge `gap_from_FixedParamsProbe :
FixedParamsRoute ac0 sb ∧ Π → ResearchGapWitness` is FP-4 territory.
A plausibility argument:

* `FixedParamsRoute ac0 sb` concludes a polylog support bound on the
  AC0 family extracted from a `PpolyFormula` witness.
* `InSupportFunctionalDiversity` requires the underlying record's
  support function to be unbounded but eventually sublinear.
* These two are not directly composable: the route's conclusion is
  about the *AC0 family*, the candidate is about the *formula record*.

So a non-trivial bridge would need to pass through an
agreement-style hypothesis (the record's `family n` matches some
`Core.Family` element pointwise — exactly the shape that
`OverbroadUniformFormulaProvenance` provides, but THAT is the
overbroad shape we're trying to weaken).

The plausibility of a valid FP-4 bridge therefore reduces to the
question: can a non-overbroad agreement hypothesis be combined with
the candidate to yield AC0 separation?  This is, in spirit, a
restatement of the central P/poly research gap and is open.

### 8.7 Self-attack

Two known weaknesses, recorded as `NOGO-000002`:

* **Multi-slice / alternating-length hardwiring evades the filter.**
  An alternating-slice hardwired record (e.g. TT at every even length,
  `const false` at odd lengths) has unbounded support (large at
  evens) AND `support n < n` at odd lengths (where support = 0 < n).
  Both conjuncts of `InSupportFunctionalDiversity` are satisfied.
  The candidate does NOT structurally exclude this shape.  Mitigant:
  this multi-slice record is not constructed in the active code base,
  so the practical exclusion against currently-realised hardwiring
  attacks is intact, but the theoretical exclusion is incomplete.
* **Vacuity proximity to route conclusion.**  The route concludes,
  among other things, `support ≤ polylog (inputLen)`.  The candidate
  asserts a structural property of the support function.  These are
  not directly equal, but a careless FP-4 bridge could derive the
  route's support-bound part from the candidate's
  eventually-sublinear conjunct, trivialising part of the
  conclusion.  Any FP-4 bridge attempt MUST carry an explicit
  non-vacuity argument.

### 8.8 Classification

**Outcome C-candidate (formal Tests 1–4 PASS) with caveats — do NOT
promote to FP-4.**

The candidate is recorded in audit-only form:

* `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean::FP3Attempt.InSupportFunctionalDiversity`
* `pnp3/Magnification/AuditRoutes/FixedParamsProbe.lean::FP3Attempt.InSupportFunctionalDiversity_excludes_uniformPolyBound`
* `pnp3/Tests/FixedParams_Probe_NoGo.lean::fp3_actual_test3_hardwiring_attack_defeated`
* `outputs/nogolog.jsonl::NOGO-000002` (multi-slice hardwiring caveat
  + bridge-not-constructed note).

`spec/known_guards.toml::guards.ProvenanceFilter_v1` STAYS at
`status = "informal"` with `formal_name = ""`.  The candidate is NOT
promoted because:

1. The multi-slice hardwiring caveat is unresolved.
2. No bridge attempt is in scope for FP-3 actual.
3. The candidate has not survived a real Critic-style adversarial
   pass (Critic loop does not yet exist; see Autoresearch MVP block).

The next research step, if pursued, would be FP-3.b: strengthen
`InSupportFunctionalDiversity` to also exclude alternating-slice
hardwiring (e.g. by requiring a quantifier of the shape "support is
unbounded over *every* infinite arithmetic progression of lengths"
or similar).  Whether that strengthening introduces hidden payload
or factors through known guards is a separate self-attack pass.
