# Task: global_hInDag_contract_repair_D0

## 1. Executive verdict

**REPAIR_POSSIBLE_WITH_GLOBAL_WITNESS**.

Current contracts can be repaired without trust-root changes by tightening route hypotheses from
`∀ n β, InPpolyDAG (slice n β)` to a single global-language/global-family witness whose polynomial
bound is shared across slices.

---

## 2. What is wrong with current hInDag

The current surface accepts:

- `hInDag : ∀ n β, InPpolyDAG (gapPartialMCSP_Language (...paramsOf n β))`.

This is too weak because it allows independent per-slice constructions with no coherence and no
shared complexity budget across slice index.

The triviality probe already gives explicit witnesses:

- `fixedSlice_gapPartialMCSP_in_PpolyDAG`
- `hInDag_for_canonicalAsymptoticHAsym`

These are obtained by fixed-length truth-table hardwiring (full lookup at one encoded length,
`constFalseDag` elsewhere). The resulting bound is polynomial in input length `n` only in the
vacuous sense “constant in n for each fixed slice”, with slice-dependent constant `K_p` that may be
exponential in the slice’s encoded length.

Therefore current `hInDag` does **not** encode a global polynomial-size family for the asymptotic
bridge language; it encodes only independent local solvability of each slice.

---

## 3. Desired repaired hypothesis

I recommend adopting **Shape B** (global family witness) and deriving A/C as wrappers.

### Primary contract (B)

```text
structure GlobalAsymptoticDAGWitness (hAsym) where
  family : Nat → DagCircuit
  exponent : Nat
  coeff : Nat
  size_bound : ∀ n, (family n).size ≤ coeff * n^exponent + coeff
  decides_global : decides family (eventualCanonicalBridge_of_asymptotic hAsym).L
  slice_extraction : ∀ n β, derivesSliceDecider family (paramsOf n β)
```

Key point: one `family`, one `(coeff, exponent)` pair, all lengths.

### Equivalent wrapper (A)

```text
Hglobal : InPpolyDAG (eventualCanonicalBridge_of_asymptotic hAsym).L
```

provided the chosen definition of `eventualCanonicalBridge_of_asymptotic` really means a single
uniform language over all valid lengths.

### Optional compatibility wrapper (C)

```text
structure CoherentSliceDAGWitness (hAsym) where
  hInDag : ∀ n β, InPpolyDAG (...paramsOf n β...)
  global_exponent : Nat
  global_coeff : Nat
  global_bound_controls_slices : ...
  derived_from_single_global_family : ...
```

C is acceptable only if it includes `derived_from_single_global_family` (otherwise it re-admits
hardwiring).

---

## 4. Hardwiring self-test

Test candidate hypotheses against `hInDag_for_canonicalAsymptoticHAsym`.

### Current hypothesis (`∀ n β, InPpolyDAG ...`)

- **Satisfied** by the hardwired witness.
- **Reject** as too weak.

### A: global bridge-language witness

- Not implied by `hInDag_for_canonicalAsymptoticHAsym` alone.
- Blocker for hardwiring: must provide one language-level DAG family with one polynomial bound;
  per-slice isolated truth tables do not compose automatically into one globally bounded family.

### B: `GlobalAsymptoticDAGWitness`

- **Not satisfied** by the known hardwiring witness as currently formalized.
- Blocker: hardwiring proof gives per-slice constants `K_p`; B requires shared `(coeff, exponent)`
  independent of slice.

### C: coherent slice witness (with derivation from one family)

- **Not satisfied** unless one can prove a single global family behind all slices.
- If `derived_from_single_global_family` is dropped, C degenerates to current weak hypothesis and
  fails the test.

Conclusion: only A/B/C-with-derivation survive the self-test.

---

## 5. Route rewrite proposal

### Current (conceptual)

- `AsymptoticIsoStrongRoute hAsym := ∀ hInDag, IsoStrongFamilyEventually F hInDag`
- `AsymptoticPromiseYesCertificateRoute hAsym := ∀ hInDag, PromiseYes... hInDag`
- downstream weak/eventual route inherits same `∀ hInDag` quantification

### Repaired (conceptual)

- `AsymptoticIsoStrongRoute_global hAsym :=
   GlobalAsymptoticDAGWitness hAsym → IsoStrongFamilyEventually_global F`
- `AsymptoticPromiseYesCertificateRoute_global hAsym :=
   GlobalAsymptoticDAGWitness hAsym → PromiseYesCertificateEventually_global`
- `AsymptoticPromiseYesWeakRouteEventually_global hAsym :=
   GlobalAsymptoticDAGWitness hAsym → PromiseYesWeakEventually_global`

Difference: consumer now takes a **single global contract** as input; no universal quantification
over arbitrary slice-local `InPpolyDAG` witnesses.

---

## 6. Endpoint compatibility

Endpoints considered:

- `NP_not_subset_PpolyDAG_final_of_asymptotic_isoStrongRoute_withAntiChecker`
- `NP_not_subset_PpolyDAG_final_of_asymptotic_promiseYesCertificateRoute_withAntiChecker`

Assessment: **adaptable without trust-root change**.

Reason:

- Trust-root objects (`P`, `NP`, `PpolyDAG`, `NP_not_subset_PpolyDAG`) stay unchanged.
- Only route-local hypotheses are strengthened.
- Likely implementation shape: local wrapper theorems that consume
  `GlobalAsymptoticDAGWitness` (or global bridge-language `InPpolyDAG`) and then feed existing
  downstream machinery after extracting slice facts.

So this is a local theorem-surface retarget, not a foundational semantic change.

---

## 7. Size-bound semantics

Current bad semantics:

- For each slice `p`, existence of some polynomial bound in input length, realized as constant
  `K_p`; no control over growth of `K_p` across slices.

Desired semantics:

- Existence of **one** family `D_n` and fixed polynomial `q(n)=a*n^k+a` such that for all lengths
  `n`, `size(D_n) ≤ q(n)` and `D_n` decides the global bridge language at length `n`.

Exact theorem needed (conceptual):

```text
global_polyBound_controls_all_slices :
  ∃ (D : Nat → DagCircuit) (a k : Nat),
    (∀ n, size (D n) ≤ a * n^k + a) ∧
    decides D (eventualCanonicalBridge_of_asymptotic hAsym).L ∧
    ∀ n β, sliceLanguage n β is obtained from D at the corresponding encoded length.
```

This theorem is the anti-hardwiring gate: it forces one global polynomial budget.

---

## 8. What Lean probe should come next?

First Lean task:

```text
global_hInDag_contract_L0 :
  (1) define GlobalAsymptoticDAGWitness
  (2) prove: hardwired fixedSlice witness does not automatically instantiate it
      (unless an additional global-bound lemma is supplied)
  (3) prove: GlobalAsymptoticDAGWitness ⇒ current hInDag
      with explicit extracted bound semantics
```

Deliverables should include one non-instantiation lemma that pinpoints the missing global bound
coherence, not a heuristic argument.

---

## 9. TMVerifier recommendation

**pause_until_global_contract_repaired**.

Rationale: continuing TMVerifier work against the current weak `hInDag` surface risks optimizing a
route whose assumption gate is known to accept hardwired per-slice witnesses.

---

## 10. Final recommendation

**open_global_contract_L0**.

---

## Output format block

Task: global_hInDag_contract_repair_D0
Handle: codex53
Branch: main
Commit before: (captured by git history at landing time)
Commit after: (captured by git history at landing time)
Changed files:
- seed_packs/global_hInDag_contract_repair_D0/README.md
- seed_packs/global_hInDag_contract_repair_D0/WORKER_PROMPT_D0.md
- seed_packs/global_hInDag_contract_repair_D0/reports/.gitkeep
- seed_packs/global_hInDag_contract_repair_D0/failures/.gitkeep
- seed_packs/global_hInDag_contract_repair_D0/reports/D0_global_hInDag_contract_repair_codex53.md

Outcome:
  REPORT_LANDED

Executive verdict:
  REPAIR_POSSIBLE_WITH_GLOBAL_WITNESS
Hardwiring self-test:
  CURRENT_hInDag_REJECTED; GLOBAL_CONTRACT_PASSES_TEST
Repaired hypothesis:
  GlobalAsymptoticDAGWitness (preferred), with bridge-language wrapper
Endpoint compatibility:
  ADAPTABLE_WITH_LOCAL_WRAPPERS_NO_TRUST_ROOT_CHANGE
Next Lean task:
  global_hInDag_contract_L0
TMVerifier recommendation:
  pause_until_global_contract_repaired
Scope violations:
  none
