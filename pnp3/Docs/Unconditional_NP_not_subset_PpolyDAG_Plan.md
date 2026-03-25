# Concrete plan to reach unconditional `NP ⊄ PpolyDAG`

Last updated: 2026-03-23.

This note turns the current DAG frontier into an explicit execution plan.
It is intentionally stricter than a generic research memo: every milestone
below is phrased so that we can tell, from the codebase alone, whether the
step is done or still open.

## Progress snapshot (2026-03-25)

The repository now includes the planned dedicated source file
`pnp3/LowerBounds/DAGStableRestrictionProducer.lean` with:

1. DAG-native certificate/invariant source contracts;
2. conversion into `dag_stableRestriction_producer`;
3. TM-level closure theorem for the invariant-provider route;
4. thin final wrappers and regression/audit wiring.

So the current mathematical blocker is exactly the source generator itself:

> construct `dagStableRestrictionInvariantProvider p` from strict DAG semantics
> (without additional bridge assumptions).

---

## 1. Exact end goal

The unconditional DAG lower-bound route is complete only when the repository
proves, without external hypotheses,

```text
ComplexityInterfaces.NP_not_subset_PpolyDAG
```

and therefore the final DAG wrappers in
`pnp3/Magnification/FinalResult.lean` no longer need an external
`hNPDag` argument.

At the current architecture boundary, the smallest theorem that would close the
DAG side is:

```text
∀ hDag : PpolyDAG (gapPartialMCSP_Language p),
  stableRestrictionGoal_of_abstractGapTargetedPayload (dagCanonicalPayload hDag)
```

because the repository already contains:

```text
hStable -> ¬ PpolyDAG (gapPartialMCSP_Language p)
```

and then the usual fixed-slice NP pullback to `NP ⊄ PpolyDAG`.

So the whole project now reduces to one producer problem:

> **Build a strict DAG-side producer of a small stable restriction for the
> canonical fixed gap payload.**

Everything below is organized around that statement.

---

## 2. What is already settled and must not be reopened

### 2.1. The consumer stack is finished

The downstream contradiction stack is already the right one:

```text
stable restriction
  -> alive-set locality
  -> contradiction with gap-locality lower bound
```

Therefore new work must target the stable-restriction interface, not invent a
parallel consumer.

### 2.2. The formula route is already a working model

The formula/support-bounds/certificate route already lands in the stable
restriction goal.  This means the repository already has one successful example
of the desired architecture:

```text
source certificate -> stable restriction -> contradiction
```

This route should be treated as the reference implementation for theorem shape,
transport lemmas, and regression tests.

### 2.3. The current DAG singleton route is diagnostically exhausted

The canonical DAG payload stores the witness
`semanticSingletonWitness`, and every member of that witness is already proved
point-like.  Hence the currently exported DAG witness family is a disguised
point case.

This has two consequences:

1. the current scenario-witness restriction candidate already has alive card
   `0`, so **smallness is not the blocker**;
2. the blocker is that the current route proves only one-sided forcing-to-YES,
   not global invariance `f (r.apply x) = f x`.

Therefore we should stop treating “better leaf semantics for the current
singleton selectors” as the main route to the final theorem.

### 2.4. `CommonPDT` is intentionally weak

`CommonPDT` records only:

* one tree,
* selector inclusion into leaves,
* one approximation bound.

It does **not** record semantic leaf facts like “each chosen leaf decides the
function” or “membership in a chosen leaf forces YES”.

Therefore any proof that uses stronger leaf semantics must either:

1. derive them from the provenance of the particular `CommonPDT`, or
2. strengthen the source-side structure to store those semantics explicitly.

---

## 3. Non-goals and routes we should explicitly avoid

These are not merely “probably unhelpful”; they are misaligned with the current
formal interface.

### 3.1. Do not aim at leaf-constancy as the main next theorem

A theorem of the form “`f` is constant on a selected leaf `β`” is too weak for
`stableRestrictionGoal_of_abstractGapTargetedPayload`, because the latter asks
for one global restriction `r` satisfying

```text
∀ x, f (r.apply x) = f x.
```

Constancy on one cube does not yield this global overwrite-invariance statement.

### 3.2. Do not spend more time polishing the current singleton witness family

The code already proves that the current DAG witness family lives inside the
truth-table singleton construction.  Improving comments or adding more local
facts about those selectors does not change the mathematical blocker.

### 3.3. Do not add another bespoke consumer endpoint

Any future DAG source theorem should be translated into the already existing
stable-restriction goal or a packaged equivalent.  A new endpoint theorem would
only duplicate a contradiction stack that is already formalized.

---

## 4. The only two mathematically coherent producer routes

There are exactly two routes compatible with the current architecture.

### Route A. DAG -> certificate bridge -> existing stable-restriction theorem

This route reuses the already proved theorem

```text
stableRestrictionGoal_of_abstractGapTargetedPayload_of_formulaCertificate
```

by constructing from a strict DAG solver a certificate object that has the same
operational content as the formula-side shrinkage certificate.

To make this route real, we would need:

1. a DAG-side certificate structure matching the data consumed by
   `ThirdPartyFacts.stableRestriction_of_certificate`;
2. a bridge from strict DAG solvers on the gap slice to that certificate;
3. either a direct generalization of the formula theorem from
   `FormulaCertificateProviderPartial` to a solver-agnostic certificate
   provider, or a DAG-specific wrapper theorem with the same conclusion.

**When to choose Route A:** only if the DAG interfaces already expose enough
certificate-compatible restriction data.  If we cannot build that bridge
without a large detour through a new circuit formalism, Route A is not the
mainline plan.

### Route B. Native DAG stable-restriction producer

This route proves the missing theorem directly on the DAG side:

```text
∀ hDag,
  stableRestrictionGoal_of_abstractGapTargetedPayload (dagCanonicalPayload hDag)
```

without reducing to the formula certificate API.

This route needs a new source-side object carrying:

1. a restriction `r`,
2. proof that `r.alive.card <= tableLen / 2`,
3. proof that `decide (r.apply x) = decide x` for all `x`,
4. a bridge transporting that statement from the solver's decision function to
   the fixed gap target stored in `dagCanonicalPayload hDag`.

**Recommended mainline:** Route B.  It matches the current strict DAG theorem
surface directly and does not depend on an unproved DAG-to-formula collapse.

---

## 5. Recommended execution plan (mainline = Route B)

This is the concrete plan we should implement unless a clean Route A bridge is
found almost immediately.

### Phase 0. Freeze the target API

Before adding any new math, create one very small DAG-frontier theorem stub in
planning documents and tests, with the exact target shape:

```text
theorem dag_stableRestriction_producer
  {p : GapPartialMCSPParams}
  (hDag : ComplexityInterfaces.PpolyDAG (gapPartialMCSP_Language p)) :
  stableRestrictionGoal_of_abstractGapTargetedPayload
    (dagCanonicalPayload hDag)
```

This theorem name is just a suggestion; the important thing is that the target
shape is frozen now.  Any intermediate work that does not obviously feed this
statement should be treated as secondary.

**Done criterion:** one canonical theorem statement is chosen and every new DAG
proof sketch is checked against it.

### Phase 1. Introduce an explicit DAG producer package

Add a new source-side structure, for example
`AbstractGapDAGStableRestrictionSource` or
`DAGStableRestrictionCertificate`, containing exactly the upstream data needed
for the probe theorem:

* `base : AbstractGapTargetedSingletonDensityPayload p`;
* `r : Facts.LocalityLift.Restriction (Models.partialInputLen p)`;
* `hAliveSmall : r.alive.card <= Models.Partial.tableLen p.n / 2`;
* `hStableDecide : ∀ x, decide (r.apply x) = decide x` for the source solver;
* `hLink : decide = gap target` in the same transported coordinate system.

Then prove a thin packaging lemma:

```text
DAGStableRestrictionCertificate ->
stableRestrictionGoal_of_abstractGapTargetedPayload base
```

This is important because it keeps all future heavy mathematics above a tiny,
inspectable conversion layer.

**Done criterion:** a new packaged producer object exists, and the conversion to
`stableRestrictionGoal_of_abstractGapTargetedPayload` is fully proved.

### Phase 2. Strengthen the source-side invariant to coordinate independence

The next proofs must target **global coordinate independence**, not cube
constancy.

The right intermediate theorem shape is one of the following equivalent forms:

```text
∀ x y, (∀ i ∈ alive, x i = y i) -> decide x = decide y
```

or

```text
∀ x, decide (r.apply x) = decide x.
```

This should be formalized as a named DAG-side invariant so that we can test it
independently of the final contradiction theorem.

A good implementation pattern is:

1. define a source-side notion of “surviving support” or “relevant coordinates”
   for the DAG under a restriction;
2. prove that evaluation depends only on those coordinates;
3. prove the support is at most half the table length;
4. turn that support into the alive set of a facts-side restriction.

The exact combinatorial definition may vary, but the invariant shape must stay
global.

**Done criterion:** there is a theorem proving a locality/stability statement
for the DAG solver itself, independent of `dagCanonicalPayload` packaging.

### Phase 3. Replace singleton provenance by genuine DAG provenance

The current canonical DAG payload is wired to
`semanticSingletonWitness`.  That was useful for diagnostics, but it is not the
right source object for the final stable-restriction producer.

We should therefore add a **new DAG provenance layer** that does not derive its
main witness family from truth-table singleton expansion.  The new layer should
expose data that can plausibly control global coordinate dependence, e.g.:

* a solver-derived restricted support set;
* a canonical restricted subgraph/tree;
* a semantic certificate extracted from the DAG computation itself;
* a support-preservation theorem under coordinate overwriting.

This phase is where the actual mathematical progress happens.  The existing
singleton provenance theorems remain valuable as a no-go/diagnostic layer, but
should no longer drive the main source object.

**Done criterion:** the main producer theorem no longer unfolds through
`semanticSingletonWitness` or point-subcube lemmas.

### Phase 4. Build the half-table bound on the same source object

The source object from Phase 3 must carry, or imply, a cardinality bound:

```text
alive.card <= Models.Partial.tableLen p.n / 2.
```

This should be proved on the same representation that yields global stability.
It is a mistake to prove smallness on one object and stability on another with
no tight bridge between them.

Concretely, the implementation should avoid the pattern:

```text
small leaf from object A
stable behavior from unrelated object B
```

unless there is a formally tiny equivalence theorem connecting A and B.

**Done criterion:** the theorem producing stability and the theorem producing
smallness share one common witness object.

### Phase 5. Prove the exact DAG stable-restriction theorem

Once Phases 1–4 are in place, prove the actual producer theorem:

```text
∀ hDag,
  stableRestrictionGoal_of_abstractGapTargetedPayload
    (dagCanonicalPayload hDag)
```

and immediately route it through the already existing corollaries:

```text
not_ppolyDAG_of_dag_stableRestriction
NP_not_subset_PpolyDAG_final_of_dag_stableRestriction_TM
P_ne_NP_final_of_dag_stableRestriction_TM
```

**Done criterion:** the repository derives `ComplexityInterfaces.NP_not_subset_PpolyDAG`
and then `ComplexityInterfaces.P_ne_NP` without external DAG lower-bound input.

---

## 6. Backup execution plan (Route A) if a certificate bridge appears viable

If, during Phase 1 or Phase 2, we discover that the strict DAG interfaces
already expose certificate-quality restriction data, then we should switch to a
shorter route:

1. define a solver-agnostic certificate provider interface (or a DAG-specific
   analogue);
2. generalize the formula bridge theorem from formula-only providers to the new
   provider shape;
3. prove that strict DAG solvers on the gap slice instantiate that provider;
4. recover the stable restriction goal through the existing consumer theorem.

This backup route is attractive only if the generalization is small and
preserves the existing formula proofs almost unchanged.

**Switch criterion:** Route A becomes mainline only if the total new code is
clearly smaller than building a native DAG support/locality theory.

---

## 7. Concrete engineering tasks to schedule now

These are the repository tasks that should be opened immediately.

### Task 1. Frontier theorem regression file

Add or strengthen a regression file that states, by type, the following public
surfaces:

* the formula bridge theorem into stable restriction;
* the DAG consumer `not_ppolyDAG_of_dag_stableRestriction`;
* the final wrappers specialized to DAG stable restriction.

The goal is to make the target signatures mechanically sticky.

### Task 2. New DAG producer namespace

Create a dedicated file for the missing source theorem, for example:

```text
pnp3/LowerBounds/DAGStableRestrictionProducer.lean
```

This file should contain only:

* the new source package,
* the solver-side locality/stability lemmas,
* the final bridge into
  `stableRestrictionGoal_of_abstractGapTargetedPayload`.

Do **not** bury the future producer inside `SingletonDensityContradiction.lean`.
That file should stay the consumer/integration layer.

### Task 3. Explicit no-go regression on singleton provenance

Keep one regression theorem or documentation note asserting that the old
canonical singleton-derived DAG route is point-like.  This prevents accidental
reversion to the wrong source layer.

### Task 4. Final API cleanup checklist

Prepare the endpoint cleanup in advance:

1. remove external `hNPDag` from default final wrappers once the producer is
   proved;
2. update `STATUS.md`, `TODO.md`, `CHECKLIST_UNCONDITIONAL_P_NE_NP.md`,
   `README.md`, and `AXIOMS_FINAL_LIST.md` in the same change;
3. re-run the full audit/test suite.

---

## 8. Acceptance criteria for “unconditional NP ⊄ PpolyDAG is done”

We should not claim success until all of the following are true at once.

1. There is a theorem in the repository with no external lower-bound inputs:

   ```text
   ComplexityInterfaces.NP_not_subset_PpolyDAG
   ```

2. That theorem is obtained through the existing stable-restriction consumer
   route rather than a duplicate bespoke endpoint.

3. The proof no longer unfolds through the current singleton witness family as
   its primary mathematical source.

4. `P_ne_NP_final*` default wrappers no longer require an external `hNPDag`.

5. Audit/regression files pin the new public signatures.

6. Status documents are updated to state unconditional DAG separation
   consistently.

---

## 9. Short version

If we compress the plan to one line, it is this:

> **Stop trying to upgrade the current singleton selectors; instead build a new
> DAG-native source package whose core theorem is a global small stable
> restriction, then feed that theorem into the already finished
> stable-restriction consumer stack.**

That is the shortest honest route from the current branch state to an
unconditional `NP ⊄ PpolyDAG` theorem.
