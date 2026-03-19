# Handoff for audit

> Note: the review request referenced frozen commit `1495c55`, but that commit is
> not present in this checkout. This handoff therefore freezes the currently
> available DAG-witness milestone at `aa3484b`, which already contains the
> structural DAG non-empty witness results listed below.

**Frozen commit:** `aa3484b`
**Suggested review range:** `af00e1d..aa3484b`

## What is actually proved in this milestone

This milestone closes the **earliest DAG-facing structural non-empty witness bridge**.

Key results:

* `Magnification.AC0LocalityBridge.semanticSingletonWitness`
* `Magnification.AC0LocalityBridge.coveredB_semanticSingletonWitness`
* `Magnification.AC0LocalityBridge.semanticSingletonWitness_err_zero`
* `Magnification.AC0LocalityBridge.semanticSingletonWitness_nonempty_of_exists_true`
* `Magnification.AC0LocalityBridge.semanticSingletonAtlas_exact_epsilon_with_witness`
* `LowerBounds.gapPartialMCSP_exists_yes_input`
* `LowerBounds.abstractGapTargetedSingletonDensityPayload_of_dag_with_baseWitness_provenance`
* `LowerBounds.dagCanonicalPayload`
* `LowerBounds.dagCanonicalPayload_baseWitness_eq_semanticSingletonWitness`
* `LowerBounds.dag_payload_baseWitness_nonempty_holds`
* `LowerBounds.dagNonemptyWitnessGoalProbe_holds`

## Mathematical meaning

For the canonical DAG-produced payload, this milestone proves:

* the stored witness `S` has explicit provenance;
* `S` agrees with the explicit semantic singleton witness;
* `S ≠ []`;
* therefore the earliest non-empty witness probe on the DAG route really holds.

Concretely, this closes the step:

`hDag -> dagCanonicalPayload hDag -> S ≠ [] -> nonemptyWitnessGoal`.

## What is **not** proved in this milestone

This milestone does **not** yet prove any unconditional separation theorem such as:

* `¬ PpolyDAG (gapPartialMCSP_Language p)`;
* `NP_not_subset_PpolyDAG`.

It also does **not** close the final semantic contradiction step over the witnessed payload.

**Milestone closes the structural DAG non-empty witness bridge, but does not yet prove unconditional `NP_not_subset_PpolyDAG`.**

## Exact remaining frontier

The next step is to convert the already proved structural witness step into a contradiction.

So the next theorem should be of one of the following kinds:

* build `cubeSeparatedGoal` for the witnessed canonical DAG payload;
* or build an equivalent semantic no-go consumer;
* and then derive `False` via the existing contradiction theorems.

In other words, this milestone stops at:

`dagNonemptyWitnessGoalProbe_holds`

and not at a separation theorem.

## Audit focus points

Please review the following especially carefully:

1. Whether the new route becomes too semantic/tautological because
   `semanticSingletonWitness := (semanticCircuit f).subcubes`, where
   `semanticCircuit f` is the truth-table DNF of an arbitrary function `f`.

2. The transport-sensitive steps:
   * `gapPartialMCSP_exists_yes_input`;
   * `dag_payload_baseWitness_nonempty_holds`;
   * use of `castBitVec` / `hsame`.

3. Whether the new entries in `Tests.AxiomsAudit` stay within the expected axiom
   profile (`propext`, `Classical.choice`, `Quot.sound`).

4. Whether `dagCanonicalPayload` really stabilizes the normal form and does not
   merely hide a mismatch between different `Classical.choice` representatives.

## What the next person should decide

The next reviewer / contributor should answer these concrete questions:

1. **Accept or reject the `semanticSingletonWitness` provenance route.**
2. If accepted, the next mathematical task is to build a **semantic contradiction
   over the same canonical witnessed payload**.
3. If rejected, the route should pivot back to a more honest family-level path
   through nontrivial families / anti-checker / capacity-gap, rather than through
   the singleton semantic witness.

## Repro

```bash
git checkout aa3484b
lake build LowerBounds.SingletonDensityContradiction
lake build Tests.AxiomsAudit
```
