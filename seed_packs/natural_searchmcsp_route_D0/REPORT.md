# Natural SearchMCSP route D0

## 1) Candidate target

**Candidate:** `treeMCSPSearchWeakLowerBoundTarget` from
`pnp4/Pnp4/Frontier/SearchMCSPConcreteTargets.lean`, instantiated with:

- `problem := treeMCSPSearchProblem threshold encoding`
- `circuitClass := C_DAG` (the frontier DAG adapter class)
- `sizeBound := nearLinearBound` (e.g., `n * log (n+2)`-scale schedule, or any
  explicitly fixed weak-size regime we choose to attack)

So the D0 candidate is:

```text
target := treeMCSPSearchWeakLowerBoundTarget threshold encoding C_DAG nearLinearBound
```

where the promise remains the existing semantic MCSP promise:

```text
treeMCSPPredicate n (threshold n) tt
```

and witnesses are concrete encoded circuits through
`TreeCircuitWitnessCodec` / `TreeMCSPSearchWitnessEncoding`.

---

## 2) Why natural

This candidate is natural in the repository sense (not synthetic/self-referential)
because:

1. **It is already the concrete frontier surface** formalized in pnp4.
   We are not inventing an ad-hoc language: we reuse the shipped
   `treeMCSPSearchProblem` / `treeMCSPSearchWeakLowerBoundTarget` objects.

2. **The promise is semantic MCSP structure, not a diagonalized parser trick.**
   The YES condition is “has a small tree circuit,” i.e., a standard
   compression-style search predicate.

3. **Witnesses are object-level circuit encodings, not singleton artifacts.**
   A witness must decode to a circuit with both size and truth-table correctness,
   so this is not a one-off payload route.

4. **It aligns with the frontier contract direction** (`SearchMCSPWeakCircuitLowerBoundTarget`
   + `SearchMCSPMagnificationContract`) instead of legacy pnp3 asymptotic
   route families that were audited/refuted.

---

## 3) What is `hWeak`

For this target, `hWeak` is exactly:

```text
SearchMCSPWeakCircuitLowerBound target
```

i.e. a proof of:

```text
target.noBoundedSolver
```

which unfolds to:

> no non-uniform bounded search solver family in `C_DAG` with per-output-bit
> size bounded by `nearLinearBound n` solves the promised tree-MCSP search
> relation at every length.

Operationally: for each output witness bit, the solver gets one bounded DAG
circuit; collectively they must always output a valid encoded small-circuit
witness on promised instances. `hWeak` says such a bounded family does not
exist.

---

## 4) What is `hMag`

`hMag` is the magnification contract object:

```text
SearchMCSPMagnificationContract target
```

with field:

```text
magnifiesToVerifiedDAGSource : target.noBoundedSolver → VerifiedNPDAGLowerBoundSource
```

So `hMag` is the explicit bridge theorem package from the weak search lower
bound to the required verified NP-vs-PpolyDAG source.

Important: by design this is a **separate obligation** from `hWeak`.
The repository architecture already enforces this split.

---

## 5) Is `hWeak` known / plausible / main-gap-hard?

### Status classification: **main-gap-hard**

- **Known?** No in-repo theorem currently provides this no-bounded-solver result
  for a natural DAG class/weak-size regime on the concrete tree-MCSP search
  target.
- **Plausible?** Plausible as a research direction (it is a standard
  search/compression hardness shape), but not currently discharged.
- **Difficulty bucket:** main-gap-hard. This is substantive lower-bound
  mathematics, not wrapper plumbing.

In other words: wrapper and target surface are available; proving `hWeak`
remains the central mathematical bottleneck.

---

## 6) Does target avoid the known failure modes?

### (a) Anti-singleton triviality

**Yes, structurally better than singleton routes.**
The relation requires a full valid decoded circuit witness for the given truth
table under size threshold, not a single hardwired accepting payload.
This avoids the exact singleton/provenance-style weakness pattern.

### (b) Self-referential artificiality

**Yes.**
No self-encoding diagonal promise is built into the target definition.
It is an external semantic search task (find small circuit witness), not a
self-referential contradiction gadget.

### (c) FormulaCertificate route

**Yes.**
This target lives in pnp4 frontier SearchMCSP surfaces and does not depend on
`FormulaCertificateProviderPartial`-style channels that STATUS marks as ex-falso.

### (d) isoStrong route

**Yes.**
No dependence on `AsymptoticIsoStrongRoute` / canonical asymptotic route
family. The target is separate from the refuted canonical isoStrong chain.

### (e) support/filter NoGos

**Largely yes (by design separation), with caveat.**
The target itself is not a support-cardinality/filter predicate route.
However, any future proof attempt must still be checked to avoid reintroducing
those NoGo patterns indirectly through helper lemmas.
At D0 target-definition level, the candidate avoids them.

---

## 7) First Lean L0 task

Even though this D0 deliverable is markdown-only, the most useful next Lean L0
is **infrastructure, not lower-bound proof**:

1. Instantiate a concrete `TreeCircuitWitnessCodec` stub interface package for a
   chosen threshold schedule with explicit encoding conventions (statement-level,
   no fake completeness).
2. Define a named concrete target constant:

   ```text
   def naturalTreeSearchTarget : SearchMCSPWeakCircuitLowerBoundTarget :=
     treeMCSPSearchWeakLowerBoundTarget threshold encoding C_DAG nearLinearBound
   ```

3. Add surface tests/audit checks (`#check` / `#print axioms`) for this named
   target package so the mainline object is stable and reviewable.

This L0 does **not** attempt `hWeak` or `hMag`; it lands the clean target pin.

---

## 8) Verdict

**OPEN_TARGET_L0**

Rationale:
- A non-artificial, route-policy-compliant mainline target already exists and
  can be concretized cleanly.
- The remaining challenge is not wrapper mismatch but proving the weak lower
  bound (`hWeak`) and then magnification (`hMag`), i.e. true main-gap work.
