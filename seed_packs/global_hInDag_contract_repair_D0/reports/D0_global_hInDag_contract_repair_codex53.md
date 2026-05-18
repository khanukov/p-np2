# D0 Global hInDag Contract Repair (codex53)

## 1. Executive verdict

**REPAIR_POSSIBLE_WITH_GLOBAL_WITNESS**.

The current route contracts are not mathematically vacuous, but their `hInDag` quantification is too weak to encode the intended “small DAG” regime because it permits slice-by-slice hardwiring with no coherence across `(n, β)`. A repaired contract can be achieved by replacing local slice-membership hypotheses with a single global-family witness (or an equivalent coherent witness that proves derivation from one family).

## 2. What is wrong with current hInDag

Current route surfaces quantify over:

- `∀ n β, InPpolyDAG (gapPartialMCSP_Language (...paramsOf n β))`.

That statement is satisfied by the probe witness:

- `fixedSlice_gapPartialMCSP_in_PpolyDAG` (fixed-slice hardwiring), and
- `hInDag_for_canonicalAsymptoticHAsym` (pointwise lifting over all slices).

The issue is semantic: each slice gets its own unrelated DAG family and its own polynomial constant. Since `InPpolyDAG` is per-language and per-input-length polynomiality, a truth-table DAG on the single active encoded length plus constant-false elsewhere is legal at each slice. Therefore `hInDag` does not force one global polynomial-size constructor to explain the whole asymptotic family.

Consequence: downstream size bounds (`ppolyDAGSizeBoundOnSlicesEventually`) can inherit huge slice-dependent constants `K_(n,β)` (e.g., exponential in encoded length), defeating the intended “uniformly small” interpretation.

## 3. Desired repaired hypothesis

### Preferred surface (B): Global family witness

```text
structure GlobalAsymptoticDAGWitness (hAsym) where
  family : Nat → DagCircuit
  boundPoly : Nat → Nat
  bound_is_poly : IsPoly boundPoly
  correct_global :
    ∀ {n β} {x},
      PromiseSliceOf hAsym n β x →
      DagEval (family (x.length)) x =
        gapPartialMCSP_Language ((eventualGapSliceFamily_of_asymptotic hAsym).paramsOf n β) x
  size_global : ∀ N, DagCircuit.size (family N) ≤ boundPoly N
  slice_extraction :
    ∀ n β, InducedSliceInPpolyDAGFromFamily family boundPoly
```

Interpretation: one nonuniform DAG family indexed by input length, with one global polynomial bound, whose induced behavior simultaneously supports all eventually-relevant slices.

### Acceptable alternative (C): Coherent slice witness

```text
structure CoherentSliceDAGWitness (hAsym) where
  hInDag : ∀ n β, InPpolyDAG (...paramsOf n β)
  global_exponent : Nat
  global_coeff : Nat
  global_bound_controls_slices :
    ∀ n β, extractedPolyBound n β ≤ (fun N => global_coeff * N^global_exponent)
  derived_from_single_global_family :
    ∃ G, GlobalFamilyRealizer G hInDag
```

Key point: coherence is not “same exponent only”; it must include derivation from a single global family (or an equivalent global realizer theorem).

## 4. Hardwiring self-test

### Test against `hInDag_for_canonicalAsymptoticHAsym`

- For current routes: **passes** (bad), because the witness is exactly built from per-slice hardwiring.
- For proposed `GlobalAsymptoticDAGWitness`: **fails to instantiate** from current hardwired proof data.

Why it fails:
1. Hardwired construction provides different DAG families per slice parameter `p`; no single `family : Nat → DagCircuit` is supplied that is correct for all slice instances simultaneously.
2. The size certificate is slice-local constant `K_p`; no proof that one polynomial `(global_coeff, global_exponent)` bounds all extracted slice families.
3. Existing witness exploits language being false off one encoded length per slice; this does not produce coherence across different slice encodings.

Hence the hardwiring loophole is blocked.

## 5. Route rewrite proposal

### Current

- `AsymptoticIsoStrongRoute hAsym := ∀ hInDag, IsoStrongFamilyEventually ...`
- `AsymptoticPromiseYesCertificateRoute hAsym := ∀ hInDag, ...`
- `AsymptoticPromiseYesWeakRouteEventually hAsym := ∀ hInDag, ...`

### Repaired

- `AsymptoticIsoStrongRoute_global hAsym :=
   ∀ hGlobal : GlobalAsymptoticDAGWitness hAsym,
      IsoStrongFamilyEventually_global ... hGlobal`

- `AsymptoticPromiseYesCertificateRoute_global hAsym :=
   ∀ hGlobal : GlobalAsymptoticDAGWitness hAsym,
      ∃ β0, ... PromiseYesCertificateAt ... (globalBound hGlobal)`

- `AsymptoticPromiseYesWeakRouteEventually_global hAsym :=
   ∀ hGlobal : GlobalAsymptoticDAGWitness hAsym,
      ∃ ε β0, ... PromiseYesWeakAt ... (globalBound hGlobal)`

Primary delta: quantify over one global witness, not over unconstrained families of slice witnesses.

## 6. Endpoint compatibility

Endpoints:

- `NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute_withAntiChecker`
- `NP_not_subset_PpolyDAG_final_of_asymptotic_promiseYesCertificateRoute_withAntiChecker`

Assessment: **adaptable without trust-root change**.

Reason: final target objects (`NP_not_subset_PpolyDAG`, `P_ne_NP`) need not change. Route hypotheses can be strengthened/retyped via local wrappers:

- introduce `*_global` route variants,
- prove adapter lemmas from `GlobalAsymptoticDAGWitness` to the internal obligations used by existing combinatorial lemmas,
- keep endpoint conclusions unchanged.

This is local theorem-surface refactoring, not a semantic redefinition of frozen interfaces.

## 7. Size-bound semantics

Current bad semantics:

- For each slice `(n,β)` there exists its own polynomial bound (often constant-in-input-length), i.e. `K_(n,β)`.
- `K_(n,β)` may be as large as full truth-table DAG size at that slice.

Desired semantics:

- There exists one polynomial `q(N)` and one DAG family `G_N` such that for all relevant slices and all lengths `N` used in the route, `size(G_N) ≤ q(N)` and correctness holds.

Needed theorem shape (exact intent):

```text
global_bound_controls_route :
  ∃ q, IsPoly q ∧
  ∃ G : Nat → DagCircuit,
    (∀ N, DagCircuit.size (G N) ≤ q N) ∧
    (∀ n β x, PromiseSliceOf hAsym n β x →
       DagEval (G x.length) x = SliceLang hAsym n β x)
```

Any route-side bound used in `PromiseYes*` / `IsoStrong*` must be derived from this same `q`.

## 8. What Lean probe should come next?

First Lean task:

```text
global_hInDag_contract_L0:
  (1) define GlobalAsymptoticDAGWitness,
  (2) prove projection lemma GlobalAsymptoticDAGWitness → (∀ n β, InPpolyDAG ...),
  (3) prove non-derivability from current fixed-slice hardwiring witness schema
      unless an additional uniformity/coherence axiom is supplied,
  (4) refactor one route (`AsymptoticPromiseYesWeakRouteEventually`) to *_global
      and establish compatibility wrapper.
```

This is the minimal kernel-checked confirmation that the repair blocks known trivial witnesses while preserving endpoint plumbing.

## 9. TMVerifier recommendation

**pause_until_global_contract_repaired**.

Rationale: current TMVerifier effort can only feed route contracts whose `hInDag` gate remains trivially satisfiable by per-slice hardwiring. Contract repair should precede further verifier sessions aimed at final DAG-side closure claims.

## 10. Final recommendation

**open_global_contract_L0**.

---

### Notes on required reading availability

Referenced files in this repo support the diagnosis and rewrite direction:

- `pnp3/Tests/HInDagTrivialityProbe.lean`
- `pnp3/Magnification/FinalResultMainline.lean`
- `pnp3/Magnification/CanonicalAsymptoticTrackData.lean`
- `pnp3/Magnification/CanonicalAsymptoticDecider.lean`
- `pnp3/Tests/CanonicalIntegrationTests.lean`
- `RESEARCH_CONSTITUTION.md`
- `STATUS.md`

The requested post-PR13 markdown `seed_packs/post_pr13_provider_retarget_D0/reports/D0_provider_retarget_opus47.md` was not present in the working tree during this D0 report run.
