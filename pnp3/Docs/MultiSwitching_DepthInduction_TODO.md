# Multi-switching depth>2: what must be formalised for the polylog bound

Global checklist for unconditional `P ≠ NP`:
`/root/p-np2/CHECKLIST_UNCONDITIONAL_P_NE_NP.md`.
This file covers only the local multi-switching / depth sub-process.

File status: working TODO / roadmap for the depth>2 sub-process.
This file is not the source of the global project status; for the
overall state, see `STATUS.md` and `TODO.md`.

This document pins **the concrete list of lemmas and constructions**
that have to be implemented in order to obtain, **without axioms**,

```
t ≤ (log₂(M+2))^(d+1)
```

and to build `AC0MultiSwitchingWitness` / `AC0PolylogBoundWitness` for
**general depth `d > 2`**.

Context: at present the depth-2 piece and the small-alphabet encoding
are closed constructively, but **the depth induction and the
CCDT-probabilistic layer are missing**.  The exact missing steps follow.

---

## 0) Existing foundations (already in the code)

1. **Encoding / injection + counting** for the canonical CCDT:
   - `AC0/MultiSwitching/Encoding.lean` (small alphabet, decoder,
     injective);
   - `AC0/MultiSwitching/Counting.lean` (cardinality bound → ∃ good
     restriction).
2. **Transition: good restriction → PartialCertificate**:
   - `AC0/MultiSwitching/ShrinkageFromGood.lean`.
3. **Stage-pipeline inputs** in `AC0/MultiSwitching/Main.lean`:
   - Stages 1–3 in the form of lemmas like
     `exists_good_restriction_*`.
4. **Numerical scaffolding for the depth trace** in
   `AC0/MultiSwitching/DepthInduction.lean`:
   - `level_le_maxSteps`, `totalSteps_le_mul_maxSteps`,
     `maxSteps_le_totalSteps`
     (the "sum ↔ maximum" coupling per level).

👉 **Problem**: this entire layer is built for depth-2 (CNF family),
and for depth>2 there is **no depth induction** and **no probabilistic
model**.

---

## 1) CCDT for depth>2 (inductive algorithm)

A **general CCDT construction** for depth-d formulas is needed; it must:

1. decompose a depth-(d+1) formula into CNF/DNF sub-processes,
2. return a canonical trace for each level,
3. allow applying the encoding at every step.

Minimal requirements:

* **CCDT algorithm type** for depth `d`:
  ```lean
  CCDTAlgorithm (n k ℓ t : Nat) (F : FormulaFamily n k)
  ```
  must exist not only for CNF (depth-2) but also for general depth-d
  formulas.

* **Trace structure**: the sequential composition of "local traces"
  (`Trace` for each level) must be formalised as an inductive type.

---

## 2) Depth induction (multi-switching)

A **real induction** is needed:

* **Base (depth-2)**: already proved constructively.
* **Step (d → d+1)**:
  - from a good restriction at level `d+1`, build a family of
    depth-`d` formulas;
  - apply the induction hypothesis for depth-`d`;
  - glue the resulting PDTs / PartialCertificates into a single
    shrinkage certificate.

This requires:

1. **Composition of CCDT + encoding** at every level.
2. **A shrinkage "gluing" lemma**:
   - combine shrinkage for sub-formulas into shrinkage for the whole
     formula;
   - control the depth (`t`) and the ε-error under gluing.

---

## 3) Probabilistic layer (formalising the counting bound)

The polylog bound needs a **probabilistic interpretation** or an
equivalent deterministic counting argument (encoding / injection).

What is required formally:

1. **Restriction parameters**: choice of `p`, `s`, `t` as functions of
   `M`, `d`.
2. **An inequality** of the form:
   ```
   |Bad ∩ R_s| ≤ |R_{s−t}| * B^t
   ```
   and its conversion into `∃ ρ ∈ R_s, ¬BadEvent ρ`.
3. **Parameter alignment** at depth `d+1`: with fixed `t`, `ℓ`, `B`,
   obtain `t ≤ (log₂(M+2))^(d+1)`.

Without this the **polylog bound** cannot be proved.

---

## 4) Final object: AC0MultiSwitchingWitness

A construction is needed:

```lean
def ac0MultiSwitchingWitness_of_depthInduction
  (params : AC0Parameters) (F : Family params.n)
  (hF : FamilyIsAC0 params F) :
  AC0MultiSwitchingWitness params F := ...
```

This lemma must:

1. Build `Shrinkage` (from the induction),
2. Prove `depth_le_polylog` exactly in the form:
   ```
   t ≤ (log₂(M+2))^(d+1)
   ```
3. Carry over `family_eq`, `epsilon_nonneg`, `epsilon_le_inv`.

After this:
* `ac0PolylogBoundWitness_of_multi_switching` becomes provable;
* Stage 6 (`partial_shrinkage_for_AC0_with_polylog`) becomes fully
  constructive without external axioms.

---

## 5) Bottom line: what blocks the depth>2 case right now

* **No CCDT induction for depth>2** — only depth-2.
* **No formal "gluing" of shrinkage** for the depth step.
* **No proved polylog bound** for `t` as a function of `M`, `d`.

Until these three steps are implemented, **a constructive polylog
witness for depth>2 does not exist**.

---

## 6) Recommended implementation order

1. Implement the CCDT induction at the type level (trace → encoding).
2. Prove the "gluing" lemma for shrinkage at depth d+1.
3. Plug in the counting bound and obtain `∃ good restriction`.
4. From the induction, build `AC0MultiSwitchingWitness`.
5. Wire the end-to-end proof in `Facts_Switching.lean`.

---

## 7) Related files (places for implementation)

* `pnp3/AC0/MultiSwitching/Main.lean` — Stage-pipeline + induction.
* `pnp3/AC0/MultiSwitching/Trace*.lean` — trace types and composition.
* `pnp3/AC0/MultiSwitching/DepthInduction.lean` — base types for
  depth-indexed traces.
* `pnp3/AC0/MultiSwitching/Counting.lean` — counting and bounds.
* `pnp3/ThirdPartyFacts/Facts_Switching.lean` — final witness.

---

## 8) Open questions for closing the plan (answers needed)

Please clarify these points — without them the depth induction and
the polylog bound cannot be completed correctly:

1. **Exact form of the induction step**:
   - Should the induction glue *one common* CCDT for depth-(d+1), or
     is it acceptable to use `d` separate shrinkage witnesses (one per
     layer) and combine them via `PartialCertificate`?
2. **Preferred base object for the induction**:
   - `Shrinkage` (a full PDT) or `PartialCertificate` (trunk + tails)?
   This affects the gluing lemmas and the depth control.
3. **Formalisation of the probabilistic step**:
   - Is a deterministic counting argument (encoding / injection) at
     each level enough, or does an explicit probability space `R_s`
     need to be built?
4. **Parametrisation of t, s, p**:
   - Must we pin exactly the classical Håstad / Servedio–Tan
     parameters, or is an "approximate" (but correct) scheme yielding
     `t ≤ (log₂(M+2))^(d+1)` with larger constants acceptable?
5. **CNF/DNF kernel of the induction**:
   - Do we keep the CNF pipeline canonical and route DNF through
     negation, or do we need a symmetric (dual) induction step?
6. **Per-depth ε budget**:
   - Do we finally pin the linear budget
     `ε_level ≤ 1/((d+1)(n+2))`, or do we need a different
     (geometric) profile?
7. **Certificate gluing**:
   - Which formula for the total depth is preferred:
     `depth_total = ℓ + t + max(depth_tail)`, or a sum over levels?
8. **LeafPartition for the canonical CCDT**:
   - Do we embed `LeafPartition` into the shrinkage certificates as a
     field, or do we keep it as a separate lemma applied locally?

---

## 9) Success criterion (for fixing DoD)

When the working checklist A0–A8 for depth>2 is closed:

* `AC0MultiSwitchingWitness` / `AC0PolylogBoundWitness` are built
  **inside the project**, without external facts;
* `partial_shrinkage_for_AC0` and `shrinkage_for_localCircuit` become
  internal theorems;
* the external dependency on witness-backed switching / shrinkage
  facts is removed in the active formula chain.

If the goal is a fully constructive status of the active chain, the
plan additionally requires closing branch B (the localised bridge /
NP-hardness layer).
