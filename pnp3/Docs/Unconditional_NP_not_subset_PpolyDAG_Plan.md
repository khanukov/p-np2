# Concrete plan to reach unconditional `NP ⊄ PpolyDAG` (density-first)

Last updated: 2026-04-01.

This document is the **single source of truth** for the current endgame plan.
All older stable-restriction-first / HSG-first narratives are superseded here.

---

## 1) Final verdict (current state)

### 1.1 What is already closed in code

The downstream contradiction spine is already present:

```text
EasyImageTransferAt
  -> no_small_dag_solver_of_easyImageTransferAt_of_counting
  -> noSmallDAG
  -> NP_not_subset_PpolyDAG wrappers
  -> P_ne_NP wrappers
```

So the blocker is **not** counting or final wrappers.

### 1.2 What is not closed

Unconditional closure is still blocked by a source theorem.

Current canonical sampler in code is singleton-like (`seedLen = 0`, constant-false
output), so HSG-first phrasing is brittle for unrestricted DAGs.

---

## 2) Non-negotiable architecture decisions (frozen)

### D1. Primary global debt

```text
canonical_smallDAG_easyDensity_source_on_slices
```

### D2. Derived compatibility debt only

```text
canonical_smallDAG_easyHSG_source_on_slices
```

HSG is not required in the mainline closure.

### D3. Primary canonical probability space

Probability must be uniform over a canonical finite family of **distinct easy
truth tables** (or equivalently one canonical representative per easy function),
not over all syntactically valid descriptions.

### D4. Mainline compiler priority

Required compiler:

```text
density -> transfer
```

Optional compatibility compilers:

```text
transfer -> HSG
density -> HSG
```

No union-bound/simultaneous-global-HSG machinery is required for default
closure.

---

## 3) Primary mathematical objects (to implement)

## 3.1 Canonical easy family

```lean
noncomputable def canonicalEasyFamilyFinset
    (p : GapPartialMCSPParams) :
    Finset (Core.BitVec (Models.Partial.tableLen p.n))
```

Intended meaning: canonical finite family of **distinct** easy truth tables.

## 3.2 Support theorem

```lean
theorem canonicalEasyFamily_supportEasy
    (p : GapPartialMCSPParams) :
    ∀ t ∈ canonicalEasyFamilyFinset p,
      PartialMCSP_YES p (totalTableToPartial t)
```

## 3.3 Reject-probability primitive

```lean
noncomputable def canonicalEasyRejectProb
    (p : GapPartialMCSPParams)
    (D : DagCircuit (Models.partialInputLen p)) : Rat :=
  acceptanceRatioOnFinset
    (S := canonicalEasyFamilyFinset p)
    (fun t => decide (dagAcceptsTotalTableOfCircuit p D t = false))
```

---

## 4) Primary source interface (density)

```lean
structure CanonicalSmallDAGEasyDensitySourceAt
    {p : GapPartialMCSPParams}
    (SizeBound : Rat → Nat → Prop) where
  epsilon : Rat
  delta   : Rat
  hEpsQuarter : epsilon ≤ (1 / 4 : Rat)
  hDeltaPos   : 0 < delta
  hRejectDensity :
    ∀ {εslice : Rat} (D : DagCircuit (Models.partialInputLen p)),
      SizeBound εslice (DagCircuit.size D) →
      dagUniformAcceptanceProbOnTotalsOfCircuit p D < 1 - epsilon →
      delta ≤ canonicalEasyRejectProb p D
```

Global debt form:

```lean
abbrev CanonicalSmallDAGEasyDensitySourceStatement ...
abbrev canonical_smallDAG_easyDensity_source_on_slices ...
```

---

## 5) Mainline compiler theorem (required)

```lean
def easyImageTransferAt_of_canonicalEasyDensitySourceAt
    {p : GapPartialMCSPParams}
    {SizeBound : Rat → Nat → Prop}
    {εslice : Rat}
    (src : CanonicalSmallDAGEasyDensitySourceAt (p := p) SizeBound)
    (W : SmallDAGWitnessOnSlice p SizeBound εslice) :
    EasyImageTransferAt W
```

Proof skeleton (must be the one implemented):

1. From `canonicalEasyFamily_supportEasy` and witness correctness:
   all `t ∈ canonicalEasyFamilyFinset p` are accepted by `W.C`.
2. Hence `canonicalEasyRejectProb p W.C = 0`.
3. If `Pr_u[W(u)=1] < 1 - src.epsilon`, density gives
   `src.delta ≤ canonicalEasyRejectProb p W.C = 0`, contradiction with
   `src.hDeltaPos`.
4. Therefore obtain `1 - src.epsilon ≤ dagUniformAcceptanceProbOnTotals W`, i.e.
   `EasyImageTransferAt W`.

---

## 6) End-to-end proof spine (final)

```text
canonical_smallDAG_easyDensity_source_on_slices
  -> easyImageTransferAtProviderOnSlices
  -> no_small_dag_solver_of_easyImageTransferAt_of_counting
  -> noSmallDAG
  -> NP_not_subset_PpolyDAG
  -> P_ne_NP
```

HSG route is optional and derived.

---

## 7) Implementation phases (real execution plan)

### Phase I

- Add `canonicalEasyFamilyFinset`.
- Add `canonicalEasyFamily_supportEasy`.
- Remove singleton sampler from primary route.

### Phase II

- Add `canonicalEasyRejectProb`.
- Add `CanonicalSmallDAGEasyDensitySourceAt`.
- Add density debt abbreviations on slices.

### Phase III

- Add `easyImageTransferAt_of_canonicalEasyDensitySourceAt`.
- Add provider-level lift to `easyImageTransferAtProviderOnSlices`.

### Phase IV

- Add density-debt top-level surfaces:
  - `noSmallDAG_surface_of_canonicalSmallDAGEasyDensitySourceDebt`,
  - `NP_not_subset_PpolyDAG_surface_of_canonicalSmallDAGEasyDensitySourceDebt`,
  - `P_ne_NP_surface_of_canonicalSmallDAGEasyDensitySourceDebt`.

### Phase V (only research blocker)

- Prove `canonical_smallDAG_easyDensity_source_on_slices`.

---

## 8) What is and is not a blocker

### Blockers now

1. proving density source theorem on unrestricted small DAGs;
2. implementing the direct `density -> transfer` compiler and wiring it to
   existing provider surfaces;
3. final TM witness packaging for the chosen fixed-slice theorem call.

### Not blockers now

- new global/simultaneous HSG object;
- union-bound hitting-tuple theorem;
- rewriting counting contradiction;
- rewriting existing final wrappers.

---

## 9) Binary closure condition

The repository reaches unconditional closure when all are true:

1. canonical easy family primitive is deduplicated by truth table;
2. density source debt on slices is proved;
3. `density -> transfer` compiler is in place;
4. existing counting/final wrappers are connected to density route;
5. final theorem is instantiated with concrete TM witness package.

If any item is missing, status remains conditional.
