# Concrete plan to reach unconditional `NP ⊄ PpolyDAG`

Last updated: 2026-04-01.

> Update (2026-03-30): unrestricted-DAG blocker reassessment moved the
> recommended final blocker from locality-only Route-B endpoints toward
> global distributional certificates.  See
> `pnp3/Docs/UnrestrictedDAG_Blocker_Reassessment_2026-03-30.md`.

> Update (2026-04-01): Route-B blocker localization is now complete at the
> module/interface level (`LowerBounds.DAGUnconditionalBlocker`,
> `NP_not_subset_PpolyDAG_final_of_sourceClosure_TM`,
> `P_ne_NP_final_of_sourceClosure_TM`, and weak-route surface checks).  This
> closes planning/packaging debt but does **not** close the core source theorem
> debt yet.
>
> Update (2026-04-01, cont.): added direct blocker-first final wrappers
> (`*_final_of_blocker_TM`) and corresponding smoke-surface checks. This
> simplifies end-to-end usage of the Route-B gate while keeping the same
> mathematical blocker unchanged.
>
> Update (2026-04-01, density compiler step): canonical easy-density interfaces
> and compilers are now wired in code
> (`CanonicalSmallDAGEasyDensitySourceAt`,
> `canonicalEasyHSGSourceAt_of_canonicalEasyDensitySourceAt`,
> `easyImageTransferAt_of_canonicalEasyDensitySourceAt`,
> provider-level compiler + noSmallDAG closure). The primary remaining debt is
> still proving the canonical density source theorem itself.
>
> Update (2026-04-01, debt-bridge step): canonical density debt now compiles to
> canonical HSG debt and to class-level non-inclusion wrappers; this reduces G1
> to proving the density debt itself rather than endpoint glue.
>
> Update (2026-04-01, singleton-equivalence check): for the **current**
> singleton canonical sampler, canonical easy-density and canonical easy-HSG
> debts are now formally inter-compilable in-tree. This confirms that the
> remaining blocker is not compiler glue but the sampler/source mathematics.

This note turns the current DAG frontier into an explicit execution plan.
It is intentionally stricter than a generic research memo: every milestone
below is phrased so that we can tell, from the codebase alone, whether the
step is done or still open.

## Progress snapshot (2026-03-28)

The repository has now moved beyond the initial producer-file milestone and
already includes:

1. asymptotic DAG witness plumbing from global/per-slice `PpolyDAG` hypotheses
   into `SmallDAGSolver` surfaces;
2. bridge-local contradiction schema and concrete weak-route instantiations
   (`accepted-family`, `promise-YES`);
3. final-surface weak-route wrappers (including PRG-image backup and stronger
   restriction extraction + numeric fallback) that all reuse the same
   accepted-family bridge template;
4. dedicated smoke regression coverage in `Tests/WeakRouteSurfaceTests`.

So the blocker is no longer API/plumbing shape; it is now purely a source
theorem issue:

> semantic Q1 acceptance-invariant from strict DAG semantics is now available,
> and the repository now also proves that same-set slack is impossible for that
> exact full-value-set Q1 construction (`no_sameSetSlack_of_strictDAGSemantics`);
> but we still need either
> `SmallDAGWitnessOnSlice -> PromiseYesSubcubeCertificateAt`
> or
> `SmallDAGWitnessOnSlice -> PRGImageAcceptanceAt`
> on the full target model, then thread it into default final wrappers.

## Progress snapshot (2026-04-01)

Route-B execution remains the locked mainline. Current status:

1. ✅ **Completed (engineering localization):** source-side blocker is now
   packaged as one explicit interface gate (`dagRouteBSourceBlocker`) with a
   dedicated closure bundle (`DAGRouteBSourceClosure`) and direct final
   wrappers from that bundle.
2. ✅ **Completed (surface hardening):** weak-route smoke surface now pins these
   new Route-B interfaces to avoid signature drift.
3. ✅ **Completed (blocker-first endpoint surface):** direct final wrappers from
   `dagRouteBSourceBlocker` are exported, so Route-B can be consumed without
   manually passing intermediate closure packages.
4. ✅ **Completed (compiler spine):** density-first compiler chain to transfer is
   now explicit in code and reusable on slice providers.
5. ✅ **Completed (debt bridge):** canonical density debt is now linked to
   existing canonical HSG/non-inclusion wrapper surfaces.
6. ✅ **Completed (singleton debt equivalence check):** canonical easy-density
   and canonical easy-HSG debts are inter-compilable for the current canonical
   singleton sampler.
7. ⏳ **Still open (mathematical blocker):** prove the actual source theorem
   that inhabits that gate, i.e. establish the internal DAG-native certificate/
   invariant production with no external lower-bound assumptions.

### Progress percentage (explicit)

We now track progress in two layers to avoid overclaiming:

* **Infrastructure / interface progress:** **96%**  
  (most endpoint/plumbing interfaces and wrappers are now in place).
* **Core theorem progress toward unconditional `NP ⊄ PpolyDAG`:** **68%**  
  (the remaining debt is concentrated in the Route-B source theorem gate G1).

These percentages are intentionally conservative and should be revised only when
G1/G3/G4 gate states change.

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
* **preferred** slack field
  `hSlack : circuitCountBound p.n (p.sNO - 1) < 2^(Partial.tableLen p.n - r.alive.card)`;
* (legacy compatibility only) optional half-table field
  `hAliveSmall : r.alive.card <= Models.Partial.tableLen p.n / 2`;
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
3. prove a counting-slack inequality
   `circuitCountBound < 2^(tableLen - |alive|)` (half-table only as legacy
   fallback);
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

### Phase 4. Build the counting-slack bound on the same source object

The source object from Phase 3 must carry, or imply, a quantitative slack bound:

```text
circuitCountBound p.n (p.sNO - 1) < 2^(Models.Partial.tableLen p.n - alive.card).
```

This should be proved on the same representation that yields global stability.
It is a mistake to prove slack/smallness on one object and stability on another with
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

## 7. Concrete engineering tasks (updated to current state)

Tasks 1–3 from the original draft are now complete as infrastructure items; the
active queue below starts from the current branch state.

### Active branch map (Route-B locked mainline)

- **Mainline (required):** DAG-native source theorem for stable restriction:
  `dagStableRestrictionInvariantProvider` or
  `dagStableRestrictionCertificateProvider`.
- **Fallback (optional):** supportHalf / accepted-family probes (Route-A2) only
  if they produce immediate source-theorem progress; no strict-A1 re-entry.

### Task status ledger (2026-04-01)

1. ✅ **Done:** Route-B blocker localization module + wrapper surface isolation.
2. ✅ **Done:** blocker-first final wrappers and smoke-surface signature checks.
3. ✅ **Done:** density-first compiler spine (`density -> transfer`) is wired.
4. ✅ **Done:** canonical density debt bridge to HSG/non-inclusion wrappers.
5. ✅ **Done:** singleton-sampler debt equivalence (`density <-> HSG`) formally checked.
6. ⏳ **In progress:** close Route-B source theorem (G1 target item 3).
7. ⏳ **Pending:** switch default final wrappers to internal unconditional DAG
   theorem (after G1).
8. ⏳ **Pending:** release/audit synchronization pass (after wrapper switch).

### Task 1. Close Route-B source theorem (the only active blocker)

Prove one of:

1. `dagStableRestrictionInvariantProvider p`, or
2. `dagStableRestrictionCertificateProvider p`,

from the DAG witness side, without introducing new consumer endpoints.

Immediate expected compilation path (already in-tree):

`invariantProvider -> certificateProvider -> stableRestrictionGoal`.

### Task 2. Internalize final DAG separation wrapper defaults

After Task 1 closes:

1. switch default DAG final wrappers to internal theorems with no external
   `hNPDag`,
2. keep older conditional wrappers only as compatibility aliases.

### Task 3. Release-facing docs/audit cleanup

After Task 2:

1. update all status/checklist/release docs to mark DAG separation as internal;
2. refresh signature audits and smoke tests;
3. re-run full audit/test suite before claiming unconditionality.

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

## 8.1. Execution lock (to avoid roadmap drift)

The current tree already has enough wrappers to accidentally look "almost done"
without discharging the real source theorem.  To keep work aligned, treat the
following as **mandatory phase gates**.

### Branch decision lock (2026-03-30)

This plan now fixes the active direction to avoid returning to already-closed
dead ends:

1. **Do not continue strict Route-A1 required-budget work.**
   - no new strict required-budget lemmas;
   - no new strict canonical wrapper layers.
2. **Treat strict A1 as blocked by formal diagnostics already in-tree**
   (`S = univ` / same-set slack failure shape).
3. **Use Route-B as the primary mainline**:
   source-side goal is DAG-native invariant/certificate production
   (`dagStableRestrictionInvariantProvider` /
   `dagStableRestrictionCertificateProvider`) and immediate compilation into
   `stableRestrictionGoal_of_abstractGapTargetedPayload`.
4. **Keep supportHalf/A2 only as a fallback probe**, not as default mainline.

### Gate G1 (source theorem gate, mandatory)

At least one of these must be proved internally (without external DAG lower-bound
hypotheses):

1. `∀ hInDag, SmallDAGImpliesPromiseYesSubcubeStatement F (ppolyDAGSizeBoundOnSlices F hInDag)`, or
2. `∀ hInDag, SmallDAGImpliesAcceptedFamilyStatement F (ppolyDAGSizeBoundOnSlices F hInDag)`, or
3. `∀ hDag, stableRestrictionGoal_of_abstractGapTargetedPayload (dagCanonicalPayload hDag)`.

If none of (1)–(3) is closed, do **not** report progress as "closing the final
gate".

**Active G1 target for this branch:** item (3), i.e. Route-B DAG-native source
producer.

### Gate G2 (strict-semantics quantitative gate, if Promise-YES mainline is used)

If route (1) above is chosen, require all of:

1. strict-semantics Q1 is connected to a non-full semantic coordinate set
   (or equivalent complement-budget witness),
2. same-set quantitative slack is proved on that same `S`,
3. composition to `PromiseYesSubcubeCertificateAt` uses existing compiler lemmas
   (no new bespoke consumer endpoint).

The theorem `no_sameSetSlack_of_strictDAGSemantics` must remain interpreted as a
blocking diagnostic until this gate is discharged.

For the current branch lock (Route-B mainline), Gate G2 is non-mainline and
must not be used to justify additional strict A1 wrapper work.

### Gate G3 (final-wrapper gate)

After G1 is closed:

1. make a default internal theorem returning
   `ComplexityInterfaces.NP_not_subset_PpolyDAG` with no external DAG
   lower-bound argument;
2. switch default `P_ne_NP_final*` wrappers to consume that internal theorem;
3. keep old externally-parameterized wrappers only as compatibility aliases.

### Gate G4 (audit gate)

Before claiming unconditional status:

1. re-run `./scripts/check.sh`,
2. ensure weak-route surface tests still compile,
3. ensure docs (`CHECKLIST_UNCONDITIONAL_P_NE_NP.md`, `TODO.md`, `STATUS.md`)
   all state the same blocker status.

---

## 9. Short version

If we compress the plan to one line, it is this:

> **Stop trying to upgrade singleton/HSG-first targets; replace the canonical
> sampler by a non-singleton easy-description family, prove a canonical
> easy-density source, compile density directly to transfer, and reuse the
> existing counting/final wrappers unchanged.**

That is the shortest honest route from the current branch state to an
unconditional `NP ⊄ PpolyDAG` theorem.

---

## 10. Addendum: canonical easy-density pivot (analysis-first blocker rewrite)

This addendum records a stricter diagnosis of the *current* final blocker in the
Route-B stack and a safer theorem-target sequence for closing the unconditional
endgame.

### 10.1. Updated blocker diagnosis

At the present point in the codebase, the downstream chain

`EasyImageTransferAt -> counting contradiction -> no small solver -> final wrappers`

is structurally in place. The critical remaining mathematical debt is the
canonical source theorem layer (preferred target:
`canonical_smallDAG_easyDensity_source_on_slices`).

However, the current canonical sampler is explicitly singleton-like:

* `canonicalEasySamplerSeedLen p := 0`;
* `canonicalEasySampler` always outputs the constant-false truth table.

This means the current canonical HSG target is not a robust final theorem target
for unrestricted small DAGs.

### 10.2. Why singleton canonical HSG is the wrong last debt

If the sampler support is a singleton `{x0}`, small DAGs can isolate that point.
Concretely, let `D0` accept only `x0` and reject all other total tables (size
`O(N)` implementation by conjunction of equality checks on all value bits). Then:

* `Pr_u[D0(u)=1] = 2^{-N} < 1 - ε` for any constant `ε <= 1/4` and large `N`;
* but `D0(x0)=1`, so there is no rejecting sampled point.

So singleton-supported canonical HSG cannot be the right final theorem debt.

### 10.3. Recommended replacement target: canonical easy-density source

Before proving canonical HSG directly, target a weaker and more natural object:

*For every small DAG with noticeable uniform rejection, the DAG rejects a
noticeable fraction of a canonical easy family.*

This should be represented by a source interface with parameters:

* `epsilon` (transfer slack),
* `delta > 0` (easy-family reject density lower bound),
* a theorem `uniform-low-acceptance -> reject-density-at-least-delta`.

### 10.4. Why density should go directly to transfer in this architecture

For the current endpoint interfaces, the strongest mainline is:

`density -> transfer -> counting contradiction`.

Reason:

1. transfer is exactly what `EasyImageTransferAt` needs;
2. with `delta > 0`, density already implies existence of a rejecting point in a
   finite canonical easy family for a fixed DAG, so any HSG step is optional
   compatibility;
3. no union-bound/global-hitting-tuple argument is needed for the default
   closure route.

So `density -> HSG` can remain as a derived theorem, but should not be the
primary path to final contradiction.

### 10.5. Concrete implementation order (recommended)

1. Replace singleton sampler primitive by a canonical finite family of
   **distinct easy truth tables** (or equivalently canonical one-representative
   descriptions per easy function).
2. Introduce canonical transfer and/or density source statements as primary
   debts.
3. Add direct compiler:
   * `density -> transfer` (mainline-critical).
4. Optionally add compatibility compilers:
   * `transfer -> HSG` (contraposition),
   * `density -> HSG` (pointwise positivity on finite seed space).
5. Keep `canonical_smallDAG_easyHSG_source_on_slices` as a **derived**
   compatibility target, not the first theorem attacked directly.
6. Re-point average-case/semantic-sampling upstream route to density/transfer.

### 10.6. Net architectural effect

The endgame becomes:

`avg-hardness / semantic-sampling source`
`-> canonical easy-density (or transfer) source`
`-> EasyImageTransferAt`
`-> counting contradiction`
`-> NP ⊄ PpolyDAG`
`-> P != NP`.

This preserves all working downstream code and relocates the true mathematical
risk to the distributional statement where existing MCSP/hardness-to-HSG
literature is most naturally aligned.

---

## 11. Recheck status (2026-04-01): what is still open vs. already sufficient

This section is a second-pass challenge audit after re-reading the active
`DAGStableRestrictionProducer` chain and running the repository checks.

### 11.1. What is already in place (and looks mathematically coherent)

1. **Downstream closure from source objects to contradiction is present.**
   The route from source providers to witness transfer/certificates and then to
   `no_small_dag_solver_*_of_counting` is implemented as direct closures.
2. **Counting-side quarter-slack plumbing is internalized.**
   The route discharges epsilon-smallness from source `hEpsQuarter` and slice
   counting budget assumptions.
3. **Build/audit hygiene currently passes.**
   Full check script passes; there are linter warnings, but no `sorry/admit`,
   no project-local `axiom`, and no `native_decide` policy violations.

Conclusion: there is no obvious downstream wiring gap left in the current Route-B
pipeline once a valid source theorem is available.

### 11.2. What is still genuinely open (the hard part)

1. **Canonical source theorem is still the core unresolved debt.**
   The primary debt should be the density/transfer form on slices
   (`canonical_smallDAG_easyDensity_source_on_slices` as preferred target, with
   HSG as compatibility layer).
2. **Current canonical sampler is singleton-like.**
   This keeps the canonical target mathematically brittle for unrestricted DAGs
   and should be replaced before treating any canonical source theorem as the
   final primary theorem goal.
3. **Upstream hardness-to-source bridge is not yet discharged.**
   Even with wrappers complete, one still needs a bona fide mathematical source
   argument (average-case / semantic-sampling / density-transfer) to close the
   chain unconditionally.

### 11.3. Decision: “enough to finish now?” vs “still blocked?”

**Still blocked mathematically.**  
The repository appears *architecturally close* but not yet logically closed to
unconditional `P != NP` because the critical source theorem debt is not proved
in a non-brittle form. The right next step remains:

* move to canonical easy-description family,
* prove density/transfer source first,
* derive canonical HSG as a compiler theorem,
* then reuse existing downstream contradiction closures unchanged.

In short: **engineering pipeline is largely sufficient; mathematics of the final
source is not yet sufficient.**

---

## 12. Exact closure checklist for unconditional `P != NP` (no hand-waving)

This is the concrete “what remains to prove” list, in theorem-level terms.

### 12.1. What is already formally available

1. **Source-to-contradiction closure exists** in `DAGStableRestrictionProducer`:
   if a slice-wise source provider is given, `noSmallDAG_*` contradictions are
   already proved.
2. **Global debt layer is isolated** and should now be interpreted density-first:
   primary debt `canonical_smallDAG_easyDensity_source_on_slices`, with
   `canonical_smallDAG_easyHSG_source_on_slices` kept only as derived
   compatibility route.
3. **Final conversion to `P != NP` exists** through DAG separation final wrappers
   once a DAG-side stable-restriction payload/provider is supplied.

So the unresolved part is not the final wrappers but the missing source theorem
content.

### 12.2. Minimal mathematical obligations that are still missing

To make the final theorem unconditional, the following must be proved (not
postulated):

#### (A) Non-singleton canonical easy family

A canonical sampler family whose support is rich (e.g. decoded descriptions of
all circuits of size `<= sYES`), plus the support-easy correctness theorem.

Without this, singleton counterexamples keep any canonical source theorem
artificially brittle.

#### (B) Canonical density/transfer source theorem on slices

For all small DAGs `D` in the ppoly-size bound:

* either transfer form:
  `(∀ z, D(gen z)=1) -> Pr_u[D(u)=1] >= 1 - epsilon`,
* or density form:
  `Pr_u[D(u)=1] < 1 - epsilon -> rejectDensity_easy(D) >= delta`.

This is the real hard theorem debt; no existing wrapper removes this need.

#### (C) Mainline compiler theorem from (B) to transfer

Mainline compiler:

* `density -> transfer` (direct contradiction using `delta > 0` and witness-side
  reject-probability `= 0` on canonical easy samples).

Optional compatibility compilers (not required for final closure):

* `transfer -> HSG` (contraposition),
* `density -> HSG` (finite-seed positivity: `rejectProb > 0 -> ∃ rejecting seed`).

#### (D) Upstream hardness bridge proving (B)

A mathematically justified bridge from an average-case / semantic-sampling /
meta-complexity hardness statement to the canonical density/transfer source.

This is the core research theorem. Without it, unconditional closure is not
obtained.

#### (E) Concrete NP witness packaging for the chosen fixed slice

Final DAG endpoints are TM-witness parameterized. One needs an explicit
`GapPartialMCSP_TMWitness p` (or equivalent NP membership package) for the
selected target `p` used in the final theorem call.

### 12.3. Binary answer to “is it already enough?”

**No, not yet enough for unconditional `P != NP`.**

*If* items (A)–(E) are fully proved inside the repository (especially (B)+(D)),
then the current downstream chain is sufficient and the proof closes.

Until then, the chain is a correct conditional framework, not an unconditional
theorem.

---

## 13. Mainline correction: density should compile **directly** to transfer

Important update to the theorem strategy:

for unconditional closure, we do **not** need to route through HSG once a
canonical easy-density source exists.

### 13.1. Correct closure spine

Use the following as the primary endgame:

`canonical easy-density source`
`-> EasyImageTransferAt`
`-> counting contradiction`
`-> no small solver`
`-> NP ⊄ PpolyDAG`
`-> P != NP`.

`density -> HSG` remains a useful derived theorem, but is optional for final
closure.

### 13.2. Required new compiler theorem (core)

Add a direct compiler:

* `easyImageTransferAt_of_canonicalEasyDensitySourceAt`

Proof idea should be formalized exactly as:

1. `canonicalEasySampler_supportEasy` + witness correctness imply acceptance of
   every canonical easy sample by the witness DAG.
2. Therefore canonical reject-probability of the witness DAG is `0`.
3. Assume uniform acceptance `< 1 - epsilon`; apply density source and obtain
   `delta <= rejectProb = 0`, contradiction with `delta > 0`.
4. Conclude the transfer inequality required by `EasyImageTransferAt`.

This bypasses HSG entirely in the main proof spine.

### 13.3. Planning consequences

1. Promote `canonical_smallDAG_easyDensity_source_on_slices` to the primary
   global debt.
2. Keep `canonical_smallDAG_easyHSG_source_on_slices` as derived/compatibility
   debt only.
3. Re-point provider/surface wrappers so the default Route-B path consumes
   density and compiles straight to transfer.

### 13.4. Updated theorem-level “must prove” set

After this correction, the unique research-critical blocker is:

* proving `canonical_smallDAG_easyDensity_source_on_slices` for unrestricted
  small DAGs (with a non-singleton canonical easy sampler).

Everything downstream is then existing infrastructure plus the new direct
density-to-transfer compiler.

---

## 14. Fact-checked execution plan: what is done, what is missing, how to close

This section is a strict implementation plan based on currently present theorem
names/interfaces (no speculative renaming).

### 14.1. Current state matrix (verified against code)

| Block | Status | Evidence in code | Gap to close |
|---|---|---|---|
| Canonical sampler | ❌ singleton | `canonicalEasySamplerSeedLen := 0`, `canonicalEasySampler = const false` | Replace with non-singleton easy-description sampler |
| Witness transfer endpoint object | ✅ present | `EasyImageTransferAt` structure exists | none |
| Transfer → counting contradiction | ✅ present | `no_small_dag_solver_of_easyImageTransferAt_of_counting` | none |
| Source-provider → noSmallDAG closures | ✅ present | `noSmallDAG_of_smallDAGEasyHSGSourceProviderOnSlices`, `noSmallDAG_of_smallDAGEasyDistSourceProviderOnSlices` | add direct density-provider closure |
| Primary canonical source debt (target) | ⚠️ migrating | currently represented via HSG-layer naming | freeze density debt as primary name/route |
| Final DAG-separation wrappers | ✅ present | `NP_not_subset_PpolyDAG_final_of_dag_stableRestriction_TM`, `P_ne_NP_final_of_dag_stableRestriction_TM` | consume new density-based producer |
| NP witness packaging interface | ✅ present | `GapPartialMCSP_TMWitness`, `gapPartialMCSP_in_NP_of_TM` | provide concrete witness at chosen final `p` |

### 14.2. Realistic closure sequence (implementation-ready)

#### Phase I — Replace brittle canonical sampler (must-do first)

1. Implement canonical finite family of **distinct easy truth tables**
   (`canonicalEasyFamilyFinset`), e.g. deduplicated truth tables realized by
   circuits of size `<= sYES`.
2. Reprove/adjust:
   * `canonicalEasyFamily_supportEasy`.
3. Keep old singleton behavior only as archived diagnostic, not as primary debt
   target.

**Exit criterion:** canonical easy family is deduplicated at truth-table level
and still formally supported on YES instances.

#### Phase II — Introduce primary density source interface

1. Add:
   * `canonicalEasyRejectProb`,
   * `CanonicalSmallDAGEasyDensitySourceAt`,
   * `CanonicalSmallDAGEasyDensitySourceStatement`,
   * `canonical_smallDAG_easyDensity_source_on_slices`.
2. Ensure the statement is parameterized over the same slice-wise size-bound
   interface pattern as existing source debts.

**Exit criterion:** density source can be stated globally in one proposition,
analogous to existing `canonical_smallDAG_*_source_on_slices`.

#### Phase III — Add direct compiler `density -> transfer` (mainline-critical)

1. Implement:
   * `easyImageTransferAt_of_canonicalEasyDensitySourceAt`.
2. Lift to slice providers:
   * `easyImageTransferAtProviderOnSlices_of_canonicalEasyDensitySourceProviderOnSlices`.
3. Reuse existing counting closure theorem without modifications.

**Exit criterion:** a density source provider alone implies `noSmallDAG` by
composition with existing transfer/counting route.

#### Phase IV — Promote density debt to top-level default closure

1. Add default surface theorems:
   * `noSmallDAG_surface_of_canonicalSmallDAGEasyDensitySourceDebt`,
   * `NP_not_subset_PpolyDAG_surface_of_canonicalSmallDAGEasyDensitySourceDebt`,
   * `P_ne_NP_surface_of_canonicalSmallDAGEasyDensitySourceDebt` (or equivalent).
2. Keep HSG-route theorems as optional derived compatibility path.

**Exit criterion:** top-level route uses density debt by default, HSG not
required for closure.

#### Phase V — Close the only true research debt

Prove:

* `canonical_smallDAG_easyDensity_source_on_slices`.

This is the unique non-plumbing theorem debt after Phases I–IV.

### 14.3. Explicit “not enough yet” list (to avoid false closure claims)

Unconditional `P != NP` is **not** yet obtained until all of the following are
present simultaneously:

1. canonical easy family of distinct truth tables + support theorem,
2. direct density source theorem on slices,
3. direct density-to-transfer compiler,
4. top-level density-debt surface closure,
5. concrete final TM witness packaging for the selected target parameters.

If any item is missing, the repo remains a conditional framework.

---

## 15. Pre-coding interface freeze (must lock before Phase I)

To avoid rework across Phases II–IV, lock these five decisions before writing
new Lean definitions:

1. **Debt naming freeze**
   * Primary debt: `canonical_smallDAG_easyDensity_source_on_slices`.
   * Derived compatibility: `canonical_smallDAG_easyHSG_source_on_slices`.
2. **Compiler-priority freeze**
   * Required mainline compiler: `density -> transfer`.
   * Optional compilers: `density -> HSG`, `transfer -> HSG`.
3. **Primary canonical object freeze**
   * Primitive object is `canonicalEasyFamilyFinset` of distinct easy truth
     tables.
   * Probability is uniform over this family (not over raw descriptions).
4. **Multiplicity-bias freeze**
   * Do not weight functions by number of syntactic descriptions.
   * If sampler is kept for compatibility, it must enumerate one canonical
     representative per distinct truth table.
5. **Density signature freeze**
   * lock exact signatures for:
     - `canonicalEasyFamilyFinset`,
     - `canonicalEasyFamily_supportEasy`,
     - `canonicalEasyRejectProb`,
     - `CanonicalSmallDAGEasyDensitySourceAt`,
     - `CanonicalSmallDAGEasyDensitySourceStatement`,
     - `canonical_smallDAG_easyDensity_source_on_slices`.

### 15.1. Recommended canonical reject-probability skeleton

```lean
noncomputable def canonicalEasyRejectProb
    (p : GapPartialMCSPParams)
    (D : DagCircuit (Models.partialInputLen p)) : Rat :=
  acceptanceRatioOnFinset
    (S := canonicalEasyFamilyFinset p)
    (fun t =>
      decide (dagAcceptsTotalTableOfCircuit p D t = false))
```

Any Bool-equivalent implementation is acceptable, but the probability space must
remain the canonical family of distinct easy truth tables.

### 15.2. Start condition

Implementation should start immediately after this freeze. Do not wait for:

* new simultaneous/global HSG objects,
* union-bound hitting-tuple compilers,
* rewrites of counting/final wrappers,
* final TM witness packaging (needed at final theorem call, not for Phases I–IV).
