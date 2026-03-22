# Gap-Target Stable-Restriction Route Status

Last updated: 2026-03-22.

This note records the current state of the
`LowerBounds.SingletonDensityContradiction` route after the following changes:

1. the gap-target payload hierarchy was extended with
   stable-restriction and locality contracts;
2. the formula/support-bounds line was connected to that new layer via a real
   producer theorem;
3. the DAG line was strengthened with selector-provenance / canonical-witness
   documentation-friendly interfaces.

The goal of this file is to keep the project documentation honest about:

* what is already formalized;
* which routes are merely architectural;
* which routes are already connected to a live source pipeline;
* what still blocks the DAG-side contradiction.

---

## 1. Current architecture

The active abstract gap-target route is now best read as the following tower:

```text
raw singleton-density package
    ↓
AbstractGapTargetedSingletonDensityPayload
    ↓
  (producer side can now branch)

  A. restriction/locality branch
     stableRestrictionGoal_of_abstractGapTargetedPayload
         ↔ AbstractGapStableRestrictionPayload
         ↓
     localityGoal_of_abstractGapTargetedPayload
         ↔ AbstractGapLocalityPayload
         ↓
     false_of_abstractGapLocalityPayload
     false_of_abstractGapStableRestrictionPayload

  B. witness/selector/cube branch
     AbstractGapWitnessedPayload
         ↓
     AbstractGapCubeSoundWitnessPayload
         ↓
     AbstractGapSelectorProvenancePayload
         ↓
     DAG canonical witness / provenance lemmas
```

The key point is that **the restriction/locality branch is now a real consumer
stack**, not just a planned interface:

* it has payloads,
* it has probe forms,
* it has packaging equivalences,
* it has contradiction theorems.

---

## 2. What is already achieved

### 2.1. Semantically fixed common target

The route no longer argues about arbitrary externally chosen targets.
Everything downstream of
`AbstractGapTargetedSingletonDensityPayload`
is pinned to the concrete gap language
`gapPartialMCSP_Language p`.

This payload is already realized from both:

* the formula-side singleton-density route;
* the strict DAG-side route.

So the remaining work is no longer "find any source package for the target" —
that part is already done.

### 2.2. Stable-restriction / locality consumer stack

The following abstract consumer-side objects now exist and are usable:

* `AbstractGapStableRestrictionPayload`;
* `AbstractGapLocalityPayload`;
* `stableRestrictionGoal_of_abstractGapTargetedPayload`;
* `localityGoal_of_abstractGapTargetedPayload`;
* packaging helpers and packaging equivalences;
* contradiction theorems reducing the route to
  `MCSPGapLocality.no_local_function_solves_mcsp`.

So the restriction route is now formally:

```text
stable restriction  →  alive-set locality  →  contradiction
```

### 2.3. First live producer into the stable-restriction layer

The new layer is no longer merely architectural.

The formula/certificate line now genuinely lands in
`stableRestrictionGoal_of_abstractGapTargetedPayload`
through the following chain:

```text
formulaRestrictionCertificateData_of_supportBounds
    ↓
formulaCertificateProvider_of_restrictionData
    ↓
stableRestrictionGoal_of_abstractGapTargetedPayload_of_formulaCertificate
    ↓
stableRestrictionGoal_of_abstractGapTargetedPayload_of_restrictionData
    ↓
stableRestrictionGoal_of_abstractGapTargetedPayload_of_supportBounds
```

This means the new restriction interface has at least one real producer already
living in the repository.

### 2.4. DAG selector-provenance normalization

The DAG line already provides a strong canonical normalization package:

* canonical DAG payload;
* equality between stored witness, dictionary, and selector witness;
* explicit witnessed and cube-sound DAG payloads;
* explicit selector-provenance payloads;
* consequences like `coveredB = gapTarget` on the chosen route.

So the DAG line is **not** blocked on witness provenance anymore.

### 2.5. Axioms audit coverage

`Tests.AxiomsAudit` now includes:

* the stable-restriction payload/probe/packaging layer;
* the contradiction theorems on that layer;
* the formula-certificate / restriction-data / support-bounds producer theorems;
* the selector-provenance / DAG canonical payload declarations.

---

## 3. What is still not achieved

### 3.1. No DAG producer into the stable-restriction layer yet

Although the formula/support-bounds route now factors through
`stableRestrictionGoal_of_abstractGapTargetedPayload`,
the strict DAG route does **not** yet provide a theorem of the form

```text
hDag → stableRestrictionGoal_of_abstractGapTargetedPayload (dagCanonicalPayload hDag)
```

or an equivalent packaged theorem returning
`AbstractGapStableRestrictionPayload`.

This is the main missing bridge if we want a unified consumer architecture for
the DAG side.

### 3.2. Leaves/subcubes are not yet connected through restriction

The intended architectural bridge is:

```text
leaf / subcube β
    ↓
factsRestrictionOfSubcube β
    ↓
stable restriction payload
    ↓
locality payload
    ↓
contradiction
```

The repository already has the crucial converter
`factsRestrictionOfSubcube`,
but the DAG/leaves side has not yet been pushed through that converter into the
new stable-restriction goal.

### 3.3. No final DAG contradiction from this branch

This branch still does **not** prove:

* `¬ PpolyDAG (gapPartialMCSP_Language p)`;
* `NP_not_subset_PpolyDAG`;
* unconditional `P ≠ NP`.

So all current progress here is best understood as:

* consumer cleanup,
* producer normalization,
* proof-search localization,
* but not yet final DAG separation.

---

## 4. Recommended next steps

### A. Stay inside the restriction architecture

The cleanest next theorem is still a DAG- or leaf-derived producer into
`stableRestrictionGoal_of_abstractGapTargetedPayload`.

The intended output should look like one of:

* a direct theorem producing
  `stableRestrictionGoal_of_abstractGapTargetedPayload (dagCanonicalPayload hDag)`;
* or a packaged theorem producing
  `AbstractGapStableRestrictionPayload`.

### B. Prefer restriction over a new bespoke consumer

The right target is **not** another leaf-only contradiction theorem.

Instead, if a future route extracts a good leaf / subcube / selector object,
it should be translated into a small restriction first, then fed to the already
proved restriction/locality consumer stack.

### C. Keep the formula route as the sanity-checked model

The formula/support-bounds route now serves as the reference implementation of
the new stable-restriction layer.

Any new DAG producer should be judged against the same target interface, not
against older endpoint-specific formulations.

---

## 5. Practical interpretation

As of this snapshot, the gap-target route has:

* a common semantically fixed payload;
* a live stable-restriction consumer stack;
* a live formula-side producer into that stack;
* a strong DAG witness/provenance normalization layer;
* but no DAG-side restriction producer yet.

That is the accurate frontier.
