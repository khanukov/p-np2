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

## Attack 8 — locality collapse  **(BLOCKING GATE)**

The deepest risk: once made concrete, the HDX `GlobalHardness` measure
turns out to be **local** (decomposes into small-fan-in checks), so it
extends to oracle-gate circuits and `(∀ f, InPpolyDAGOracle f → ¬P f)`
becomes unprovable / false. This is the locality barrier eating the
candidate from inside.

Status: `not-attempted`

If `attack-succeeded` → `NoGoLog`, `failure_class = "locality"` (propose
new class if absent); record precisely which decomposition makes the
measure local — that characterization is the deliverable's value.
