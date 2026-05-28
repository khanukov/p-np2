# Self-attack — hdx_locality

**Status: DRAFT.** Per Rule 12, a structured admission of likely
failures. Attacks 1 and 8 are blocking gates.

## Attack 1 — hardwiring  **(BLOCKING GATE)**

Does `SourceTheorem_hdx_locality` admit a truth-table hardwired witness?
The `NotHardwired P` conjunct is the Rule 5 defence; attack it with
`pnp3/Tests/FormulaSupportBoundsFalsifiabilityProbe.lean`.

Status: `not-attempted` → if `attack-succeeded`, `NoGoLog` `failure_class = "hardwiring"`.

## Attack 2 — refuted-predicate sneak-in

Walk the dependency closure for any `spec/target.toml::[refuted_predicates]`
(support-bounds / multi-switching) once parameters are instantiated.

Status: `not-attempted`

## Attack 3 — typeclass-payload channel

No `class`/`instance`/`Fact`/`opaque`/payload `noncomputable def`
(Rule 16). Skeleton clean; recheck after the inhabitant is written.

Status: `attack-failed` (skeleton clean; recheck post-inhabitant)

## Attack 4 — collapse-not-contradiction

Bridge must yield the separation directly, not a PH-collapse implication.

Status: `attack-failed` (by design; verify after bridge is retyped)

## Attack 5 — arbitrary-witness exploitation

Usefulness quantifies over the oracle-extended poly-DAG class, so the
`NotHardwired` exclusion lemma is mandatory (= Attack 1).

Status: `not-attempted`

## Attack 6 — prior-art duplication

Is this just HDX→SoS/PCP re-skinned? Structural difference must be
explicit: usefulness against *oracle-extended* circuits as a direct B4
counter (see `sketch.md`).

Status: `not-attempted`

## Attack 7 — size policy violation

`SourceTheorem_hdx_locality` + closure must fit `K_stmt = 40`,
`K_exp = 200` (Rule 4) once HDX notions are instantiated. The HDX
machinery is heavy — real risk of blowing the budget; narrow if so.

Status: `not-attempted`

## Attack 8 — oracle-target collision  **(BLOCKING GATE — attack-succeeded)**

Status: **`attack-succeeded`** (auditor refutation, May 2026)

Stronger version of the locality-collapse attack: the source theorem
is not merely hard, it is **unconditionally inconsistent** under the
B4 fact. `Docs/BARRIER_CATALOGUE.md §B4` records that Gap-MCSP admits
highly-efficient *oracle-extended* circuits. The shape above demands
both `(∀ f ∈ InPpolyDAGOracle, ¬P f)` and `P(GapMCSP)`, so under
`IsGapMCSP ⊆ InPpolyDAGOracle` the conjuncts contradict each other.

The conceptual root: the arrow was reversed. Beating B4 requires
usefulness against **plain** `PpolyDAG` via a technique that does
**not** extend to the oracle-augmented class — not usefulness against
the oracle-augmented class itself (which would *contradict* the B4
fact for the target).

Formal refutation lives in `proof.lean`:
`hdx_locality_current_shape_impossible`. Together with any inhabited
`IsGapMCSP` slice and the B4 fact, it derives `False` from
`SourceTheorem_hdx_locality`.

`NoGoLog` recommendation (operator-side): `failure_class =
"oracle_target_collision"` (propose new class — distinct from
`hardwiring` and `locality`); the structural pattern is "requiring
usefulness against a class that contains the target". Future candidates
must declare and check `IsGapMCSP ⊄ <usefulness class>` before
quantifying over that class.

Repair direction (not scaffolded — as hard as the main gap, see
`sketch.md` for the proposed corrected shape).
