# Worker prompt — fp3b3_4 M2 (meta-barrier Lean formalisation)

> Send this entire file as the prompt body to one independent
> research engineer (human + LLM session).  M2 is a **Lean
> formalisation** slot.  M1 (markdown candidate statement) must
> already have landed and been operator-reviewed.  M3 (audit-route
> integration) is GATED on M2 landing and operator review.

---

You are working on slot **M2** of seed pack
`fp3b3_4_v2_a_normalise_meta_barrier/`.  The pack opened to
investigate whether there is a formal meta-barrier theorem
closing the V2-A.1 design space (cf. fp3b3_3 seed pack which is
currently STALLED pending this slot).

M1 worker `m1nova` shipped a candidate statement and proof-strategy
preview (`candidates/M1_m1nova.md`).  Operator review
(`audits/M1_m1nova_operator_review.md`) verified m1nova's argument
against trust-rooted Lean facts and promoted M1.  Your task is to
formalise the meta-barrier theorem in Lean.

## 0. Repository setup

```bash
git clone <repo-url> p-np2
cd p-np2
git checkout claude/research-governance-phase0-lmZBP
export PATH="$HOME/.elan/bin:$PATH"
lake build PnP3 Pnp4
./scripts/check.sh
```

Baseline must be GREEN before you start.

## 1. Required reading (in order)

1. `seed_packs/fp3b3_4_v2_a_normalise_meta_barrier/README.md` —
   slot overview.
2. `seed_packs/fp3b3_4_v2_a_normalise_meta_barrier/candidates/M1_m1nova.md` —
   the candidate statement, predicate class, counterexample
   analysis, and proof-strategy preview your formalisation
   should follow.
3. `seed_packs/fp3b3_4_v2_a_normalise_meta_barrier/audits/M1_m1nova_operator_review.md` —
   operator-level verification of m1nova's argument and the
   strengthenings required for M2.  In particular, §6 specifies
   the mandatory `StructuralNormaliser` fields including the
   explicit `NoInventsMixedGatesOnAndOnly`-style field.
4. **Trust-rooted Lean facts your proof will cite:**
   * `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/NonVacuity.lean:24-40` —
     `seedGate`, `seededPrefixAndFamily` definitions.
   * `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/ExcludesPrefixAnd.lean:29-43` —
     `orGateCount_prefixAnd = 0`, `notGateCount_prefixAnd = 0`.
   * `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/ExcludesPrefixAnd.lean:46-63` —
     the template proof structure for using V2-A's mixed-gate
     clause to contradict zero-OR/zero-NOT at support ≥ 2.
   * `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/Filter.lean:138-162` —
     V2-A's filter predicate including the mixed-gate clause.
5. **Audit-route barrier template** (for the formal style your
   theorem should match):
   `pnp3/Magnification/AuditRoutes/SupportCardinalityBarrier/Barrier.lean`.
6. **The fp3b3_3 design-space closure decision** (background
   context, NOT something you act on):
   `seed_packs/fp3b3_3_v2_a_1_minimal_normalisation/audits/T1_retry_pause_post_M1.md`.
7. **The trust root** (READ-ONLY):
   `pnp3/Complexity/Interfaces.lean` for `FormulaCircuit`, `eval`,
   `support`, `size`, `orGateCount`, `notGateCount`, `andGateCount`,
   `booleanGateCount`, `depth`.
8. `RESEARCH_CONSTITUTION.md` — Rules 0, 1, 9, 12, 16.

## 2. Slot M2 goal

Produce the Lean module

```
pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_NormaliseMetaBarrier/Barrier.lean
```

containing:

### 2.1 The `StructuralNormaliser` predicate class

Following m1nova's M1 §A formalisation, with operator review §6
strengthenings.  Required fields (worker may rename, may split
across helper structures):

```lean
structure LocalFormulaOps where
  mkNot : ∀ {n}, FormulaCircuit n → FormulaCircuit n
  mkAnd : ∀ {n}, FormulaCircuit n → FormulaCircuit n → FormulaCircuit n
  mkOr  : ∀ {n}, FormulaCircuit n → FormulaCircuit n → FormulaCircuit n
  mkNot_eval : ∀ {n} (C : FormulaCircuit n) (x : Bitstring n),
    FormulaCircuit.eval (mkNot C) x = FormulaCircuit.eval (FormulaCircuit.not C) x
  mkAnd_eval : ∀ {n} (A B : FormulaCircuit n) (x : Bitstring n),
    FormulaCircuit.eval (mkAnd A B) x = FormulaCircuit.eval (FormulaCircuit.and A B) x
  mkOr_eval  : ∀ {n} (A B : FormulaCircuit n) (x : Bitstring n),
    FormulaCircuit.eval (mkOr A B) x = FormulaCircuit.eval (FormulaCircuit.or A B) x
  mkNot_size : ∀ {n} (C : FormulaCircuit n),
    FormulaCircuit.size (mkNot C) ≤ FormulaCircuit.size (FormulaCircuit.not C)
  mkAnd_size : ∀ {n} (A B : FormulaCircuit n),
    FormulaCircuit.size (mkAnd A B) ≤ FormulaCircuit.size (FormulaCircuit.and A B)
  mkOr_size  : ∀ {n} (A B : FormulaCircuit n),
    FormulaCircuit.size (mkOr A B) ≤ FormulaCircuit.size (FormulaCircuit.or A B)
  -- NEW (operator review §6): structural simplifier cannot invent
  -- OR/NOT from AND-only / input-only children.
  mkAnd_orGateCount_pres : ∀ {n} (A B : FormulaCircuit n),
    orGateCount A = 0 → orGateCount B = 0 → orGateCount (mkAnd A B) = 0
  mkAnd_notGateCount_pres : ∀ {n} (A B : FormulaCircuit n),
    notGateCount A = 0 → notGateCount B = 0 → notGateCount (mkAnd A B) = 0

def foldFormula (ops : LocalFormulaOps) : ∀ {n}, FormulaCircuit n → FormulaCircuit n
  | _, FormulaCircuit.const b => FormulaCircuit.const b
  | _, FormulaCircuit.input i => FormulaCircuit.input i
  | _, FormulaCircuit.not C   => ops.mkNot (foldFormula ops C)
  | _, FormulaCircuit.and A B => ops.mkAnd (foldFormula ops A) (foldFormula ops B)
  | _, FormulaCircuit.or A B  => ops.mkOr (foldFormula ops A) (foldFormula ops B)

structure StructuralNormaliser where
  ops              : LocalFormulaOps
  normalise        : ∀ {n}, FormulaCircuit n → FormulaCircuit n
  normalise_eq_fold : ∀ {n} (C : FormulaCircuit n),
    normalise C = foldFormula ops C
```

The `eval_pres` and `size_le` derived theorems should be lemmas
on `StructuralNormaliser`, not extra fields, since they follow from
`normalise_eq_fold` + the per-constructor lemmas.

### 2.2 The meta-barrier theorem

```lean
theorem v2_a_structural_normalisation_meta_barrier
    (𝒩 : StructuralNormaliser)
    (hSeed : ∀ {n} (h : 1 ≤ n),
      𝒩.normalise (seedGate n h) = FormulaCircuit.const true)
    (hAndTrue : ∀ {n} (C : FormulaCircuit n),
      𝒩.ops.mkAnd C (FormulaCircuit.const true) = C) :
    ¬ ProvenanceFilter_v2_V2_A_gpt55_Filter
        (normalisedWitness 𝒩 seededPrefixAndWitness)
```

where `normalisedWitness 𝒩 w` applies `𝒩.normalise` pointwise to
`w.family` (you define this; the construction is the same as fp3b3_3
README §T2 sketch but in a fresh namespace).

The theorem says: any structural normaliser satisfying the
HARD-minimum seed elimination and AND-with-true reduction makes
V2-A reject V2-A's own seeded non-vacuity witness.  This is the
formal closure of V2-A.1's design space.

### 2.3 Proof outline (follow m1nova §D + operator review §1-2)

```
1. Define normalisedWitness 𝒩 w.
2. Unfold the V2-A filter predicate on normalisedWitness 𝒩 seededPrefixAndWitness.
3. Pick n = 2 (or any n ≥ 2 where prefixAnd_support_card kicks in).
4. Apply 𝒩.normalise_eq_fold and the foldFormula clauses to compute
   𝒩.normalise (seededPrefixAndFamily 2)
     = 𝒩.ops.mkAnd (foldFormula 𝒩.ops prefixAnd) (foldFormula 𝒩.ops seedGate).
5. Rewrite foldFormula 𝒩.ops seedGate to const true via hSeed (recall
   seedGate n h = or (input ⟨0,h⟩) (not (input ⟨0,h⟩)); fold gives
   ops.mkOr (input ⟨0,h⟩) (ops.mkNot (input ⟨0,h⟩)) which 𝒩.normalise
   composes with seedGate → const true via hSeed; the fold equation
   makes this propositional).
6. Apply hAndTrue at C := foldFormula 𝒩.ops prefixAnd.
7. Conclude 𝒩.normalise (seededPrefixAndFamily 2) = foldFormula 𝒩.ops prefixAnd.
8. Use orGateCount_prefixAnd + notGateCount_prefixAnd + the
   ops.mkAnd_orGateCount_pres / mkAnd_notGateCount_pres fields,
   propagated through fold, to conclude
   orGateCount (𝒩.normalise (seededPrefixAndFamily 2)) = 0
   notGateCount (𝒩.normalise (seededPrefixAndFamily 2)) = 0.
9. Use support preservation: derive
   support_card (𝒩.normalise (seededPrefixAndFamily 2)) ≥ 2 from
   support_card prefixAnd = 2 (via eval-preservation + an
   appropriate support-via-eval argument), OR
   if this is hard in general, prove a custom
   support_card_normalise_prefixAnd lemma.
10. Apply V2-A filter's mixed-gate clause via hMix 2 hSupport.
11. Derive orGateCount > 0 or notGateCount > 0.
12. Contradict step 8.
```

The hardest step is likely **step 9** (support preservation
through the fold).  M2 worker may either:

* prove a general lemma `support_normalise : support (𝒩.normalise C)
  = support C` from eval-preservation (this is mathematically
  correct: support is determined by eval), OR
* prove a concrete `n = 2` support computation directly, sidestepping
  the general lemma.

Operator preference: try the general lemma first.  If it requires
heavy machinery, fall back to the concrete `n = 2` route.

### 2.4 Auxiliary lemmas

Worker should expect to prove:

* `normalise_eval : eval (𝒩.normalise C) x = eval C x` — derived
  from `normalise_eq_fold` + per-constructor eval preservation
  via structural induction.
* `normalise_size_le : size (𝒩.normalise C) ≤ size C` — derived
  similarly.
* `support_normalise : support (𝒩.normalise C) = support C` —
  derived from `normalise_eval` and the trust-root support
  definition.  This is the key lemma for step 9.
* `foldFormula_prefixAnd_orGateCount_zero` and
  `_notGateCount_zero` — by induction on the prefixAnd
  recursion using the new `ops.mkAnd_*_pres` fields.

### 2.5 Sanity-inhabitant

To demonstrate the class is non-trivially inhabited, prove an
existence theorem:

```lean
theorem identity_structuralNormaliser_exists :
    ∃ (𝒩 : StructuralNormaliser),
      ∀ {n} (C : FormulaCircuit n), 𝒩.normalise C = C
```

The identity normaliser (using `mkNot := not`, `mkAnd := and`,
`mkOr := or`) trivially satisfies the class without satisfying
`EliminatesSeedGate`.  This sanity-inhabitant ensures the
meta-barrier theorem is not vacuously true.

(NOTE: the identity normaliser does NOT trigger the meta-barrier
because its `hSeed` antecedent fails — `normalise seedGate = seedGate
≠ const true`.  So this is non-vacuity of the **class**, not
non-vacuity of the **conclusion**.)

## 3. File-path convention

Pick `<YOUR-HANDLE>`.  Your single Lean file:

```
pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_NormaliseMetaBarrier/Barrier.lean
```

Note: this is **one Lean module shared across M2 workers** (unlike
fp3b3_3 which used `V2_A_1_<HANDLE>/` per-worker directories).
Reason: the meta-barrier theorem is a single audit-route artifact;
multiple worker attempts should not produce parallel barrier
theorems.  If your attempt collides with a previously-landed M2
attempt, ship a `failures/M2_<HANDLE>_blocked_on_prior_M2.md`
report with one section: "M2 already landed at commit `<hash>`;
no new work needed."

Wire the new module into `lakefile.lean` under the existing
`Glob.one ...` list.  Add an optional smoke test at
`pnp3/Tests/AuditRoutes_V2_A_NormaliseMetaBarrier_Smoke.lean`
checking the theorem typechecks and the identity inhabitant exists.

## 4. Allowed / forbidden scope

### Allowed

* New Lean module under
  `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_NormaliseMetaBarrier/`.
* New smoke test under `pnp3/Tests/`.
* `lakefile.lean` edit to wire the new module.
* Reading any existing file in the repo.

### Forbidden (HARD)

* Editing any V2-A module under
  `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/`.
* Editing the trust root (`pnp3/Complexity/Interfaces.lean`).
* Editing fp3b3_3 files.
* `axiom`, `opaque`, `Fact`, `sorry`, `admit` anywhere in the
  committed module.
* `Classical.choose` anywhere in the committed module.
* Truth-table reconstruction or `ttFormula`-style decision
  procedures in the proof (these are exactly the techniques the
  meta-barrier is about ruling out for the class — using them
  in the proof would be incoherent).
* Promoting any guard or candidate.
* Editing `outputs/nogolog.jsonl` (operator may add NOGO-000009
  post-M2 landing; that is operator-scope).
* Editing `outputs/attempts.jsonl`.
* Editing `spec/known_guards.toml`.
* `gap_from_*` / `SourceTheorem_*` / final endpoint language.
* P ≠ NP / ResearchGapWitness / unconditional separation claims.

## 5. Acceptance checklist

- [ ] `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_NormaliseMetaBarrier/Barrier.lean`
      exists with no `sorry`/`admit`/`axiom`/`opaque`/`Fact`.
- [ ] `LocalFormulaOps` structure defined per §2.1.
- [ ] `foldFormula` defined per §2.1.
- [ ] `StructuralNormaliser` structure defined per §2.1.
- [ ] `v2_a_structural_normalisation_meta_barrier` theorem proven
      per §2.2.
- [ ] `identity_structuralNormaliser_exists` sanity-inhabitant
      proven per §2.5.
- [ ] `lakefile.lean` wires the new module.
- [ ] `lake build PnP3 Pnp4` green.
- [ ] `./scripts/check.sh` green.
- [ ] No forbidden constructs in proof.

## 6. Failure mode — meta-barrier not formalisable

If after honest attempt the meta-barrier statement turns out to
be vacuous, false, or formalisable only under a class that
excludes the intended T1 normaliser (i.e. excludes g55-style
structural simplifiers), ship a structured failure report at

```
seed_packs/fp3b3_4_v2_a_normalise_meta_barrier/failures/M2_<HANDLE>.md
```

with EXACTLY four sections:

1. **What was attempted.**  Class formalisation, theorem statement,
   key lemmas attempted.
2. **Where it broke.**  Specific Lean error or counterexample.
   Paste error verbatim.
3. **Local vs global obstruction.**  Local: this class
   formalisation didn't work; another might.  Global: the
   meta-barrier hypothesis is structurally false, V2-A.1 design
   space is alive after all.
4. **What an integrator must know.**  If Global: fp3b3_3 design
   space reopens; T1 retry track may unpause.  If Local: revised
   class formalisation suggestion.

## 7. Output format (response back to operator)

```
Slot: M2
Handle:
Branch:
Commit:
File: pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_NormaliseMetaBarrier/Barrier.lean

Outcome:
  THEOREM_LANDED | FAILURE_REPORT

If theorem landed:
  theorem name:
  LOC of new module:
  key auxiliary lemmas:
  identity sanity-inhabitant proven: YES/NO

If failure report:
  failure file:
  local/global classification:
  shortest explanation:

lake build: green/red
./scripts/check.sh: green/red
Scope violations: none / list
```

## 8. Work style

* Do not ask the operator questions.
* Do not stop on `needs_review`.
* Do not invent additional infrastructure beyond what §2 requires.
* Do not edit the V2-A trust-root files.  If your proof seems to
  need that, your class formalisation is wrong.
* Cite specific line numbers when referencing existing Lean code.
* Pre-empt obvious objections — the operator review of M1 already
  flagged the `NoInventsMixedGatesOnAndOnly` field and the
  support-preservation step as the load-bearing technical bits.
* If you must mark a sub-lemma as `[OPEN]`, do so in a top-of-file
  comment, but the main theorem MUST land with all sub-lemmas
  proven.  No partial landings.

The deliverable is a single Lean theorem closing the V2-A.1
design space.  Operator post-landing actions: add NOGO-000009,
archive fp3b3_3, refresh V2-A.2 / V2-B / V2-D priorities.  M3
(audit-route-suite integration) is operator-discretion after M2
review.
