# Asymptotic repair plan for the P≠NP formalization pipeline

This document translates the current repository state into an execution-ready roadmap with:

1. **What can be done immediately without extra inputs**.
2. **What requires additional mathematical/product decisions**.
3. **Concrete deliverables, risks, and validation checks**.

> Scope: Lean formalization in `pnp3/` with emphasis on `Partial MCSP`, magnification, and Stage 4 shrinkage.

---

## 0) Executive summary

The current bottleneck is **not** the final logical glue `NP ⊄ P/poly ⇒ P ≠ NP`, but rather:

- finite-length modeling of Partial-MCSP in the final layer,
- non-polytime NP-hardness interface,
- Stage 4 proof path where `hgood` is not structurally required to obtain useful bounds.

So the practical strategy is:

1. Repair modeling (asymptotic language).
2. Repair reduction types (polytime / randomized polytime).
3. Repair Stage 4 dependency on `Good`.
4. Then reconnect final theorem as a clean conditional asymptotic statement.

---

## 1) What we can implement now (no extra inputs required)

These tasks are engineering/formalization tasks and can be started immediately.

### 1.1 Add asymptotic Partial-MCSP language profile

**Files:**
- `pnp3/Models/Model_PartialMCSP.lean`

**Implementation:**
- Add `GapPartialMCSPProfile` with `sYES, sNO : Nat → Nat` and gap monotonicity constraints.
- Add decoder for lengths of form `N = 2 * 2^m`.
- Add `gapPartialMCSP_Language_profile : GapPartialMCSPProfile → Language` defined on all input lengths.

**Why this is safe now:**
- Fully internal data-model refactor.
- No dependence on unresolved external theorem choices.

### 1.2 Split reduction interfaces into logical vs complexity-aware

**Files:**
- `pnp3/Complexity/Reductions.lean` (or new `ReductionsPoly.lean`)

**Implementation:**
- Keep only complexity-aware reductions in active code:
  `PolyTimeManyOneReducibleLanguage` and `RandPolyTimeManyOneReducibleLanguage`.
- Keep NP-hardness interfaces `Is_NP_Hard_poly` and `Is_NP_Hard_rpoly`.
- Remove legacy purely-logical many-one layer from active modules.

**Why this is safe now:**
- Backwards-compatible layering.
- Allows progressive migration without breaking older files.

### 1.3 Refactor FinalResult into explicit asymptotic conditional theorem

**Files:**
- `pnp3/Magnification/FinalResult.lean`
- optional legacy split: `FinalResult_FiniteSanity.lean`

**Implementation:**
- Replace fixed `n := 8` pipeline in final theorem by profile-parameterized theorem.
- Keep finite sanity theorem separately for regression/experiments.

**Why this is safe now:**
- Primarily theorem signature and plumbing changes.
- Can preserve old statements under renamed theorem for continuity.

### 1.4 Stage 4 hardening: make `hgood` proof-relevant

**Files:**
- `pnp3/AC0/MultiSwitching/TraceBridge.lean` (new or extended)
- `pnp3/AC0/MultiSwitching/ShrinkageFromGood.lean` (new or extended)

**Implementation:**
- Add `trace → depth` and `¬trace → depth` bridge lemmas.
- Make shrinkage constructor use those lemmas so depth bound cannot be obtained without `hgood`.
- Remove default fallback pathways equivalent to brute-force all-point subcubes.

**Why this is safe now:**
- Purely internal proof-quality tightening.
- Improves correctness even before selecting external hardness assumptions.

### 1.5 Add regression tests against vacuity

**Files:**
- `test/` (new Lean tests)

**Implementation ideas:**
- compile-fail style checks (or equivalent theorem non-provability patterns) for trivialized AC0/local predicates;
- tests that Stage4 theorem applications fail if `hgood` is replaced by trivial inhabitant.

**Why this is safe now:**
- Protects against future accidental re-vacuification.

---

## 2) What needs additional inputs/decisions

These are blocking choices where multiple mathematically valid directions exist.

### 2.1 Exact machine model for polytime reductions in this repo

**Need from maintainers:**
- Decision: which TM/function-computation encoding to standardize on for reductions.

**Why needed:**
- `PolyTimeManyOneReducibleLanguage` must match the complexity model used by `P`, `NP`, `P/poly` interfaces already imported.

### 2.2 Deterministic vs randomized reduction track in third-party theorem wrappers

**Need from maintainers:**
- Decision: include randomized reduction type now (`Is_NP_Hard_rpoly`) or keep deterministic shell with explicit assumption bridge.

**Why needed:**
- Randomized-polytime many-one statements should not be encoded as deterministic without explicit annotation.

### 2.3 Policy for external results: axiom vs imported theorem object

**Need from maintainers:**
- Decision on acceptable trust boundary:
  - keep as explicit axiom with source citation,
  - or integrate verified external package/theorem artifact.

**Why needed:**
- Impacts theorem naming, module boundaries, and CI policy.

### 2.4 Stage 4 target strength

**Need from maintainers:**
- Decide minimum acceptable bound shape for first milestone:
  - strict polylog depth,
  - or intermediate nontrivial bound with clear TODO.

**Why needed:**
- Controls whether we block merge on full multi-switching strength vs incremental integration.

---

## 3) Proposed phased execution plan

### Phase A — Modeling correctness (short)

- Deliver profile-based asymptotic Partial-MCSP language.
- Keep fixed-length language only as legacy/testing artifact.
- Update all final-layer imports to asymptotic language.

**Exit criterion:** no final theorem relies on single fixed input length.

### Phase B — Reduction semantics (medium)

- Add polytime many-one interface.
- Create compatibility wrappers from old logical reductions where needed.
- Re-type NP-hardness-facing statements in magnification files.

**Exit criterion:** final asymptotic theorem references only complexity-aware NP-hardness notions.

### Phase C — Stage 4 non-vacuity (medium/high)

- Add TraceBridge lemmas linking bad traces and DT depth.
- Rebuild shrinkage-from-good theorem so `hgood` is indispensable.
- Add regression tests to guard this contract.

**Exit criterion:** proof breaks if `hgood` is removed; depth bound remains nontrivial.

### Phase D — Final theorem cleanup (short)

- Reassemble final theorem as explicit conditional asymptotic glue:
  assumptions → `NP ⊄ P/poly` → `P ≠ NP`.
- Keep unresolved mathematical assumptions explicit and quantified over `m`.

**Exit criterion:** theorem statement is mathematically honest, asymptotic, and non-finite.

---

## 4) Validation checklist

For each phase, run:

- `lake build` (full build)
- target tests in `test/` for regressions
- focused rebuild of modified modules

Additional checks:

- Ensure no hidden fallback terms recover exponential-depth trees while claiming shrinkage.
- Ensure final theorem has no hardcoded concrete `n` in the proof path.

---

## 5) Risk map

- **High risk:** integrating polytime (or randomized polytime) reductions with existing imported complexity interfaces.
- **High risk:** proving robust TraceBridge lemmas if canonicalDT and Good/Bad encodings drift.
- **Medium risk:** arithmetic normalization for length decoder `N = 2 * 2^m`.
- **Low risk:** final theorem signature/plumbing cleanup.

---

## 6) Definition of done (pragmatic)

A PR can be considered successful when:

1. Final theorem is asymptotic and does not hinge on fixed `n`.
2. NP-hardness type in final path is complexity-aware (polytime or randomized-polytime, explicitly named).
3. Stage 4 shrinkage theorem cannot be proved without `hgood` and outputs explicit useful depth bound.
4. Regression tests cover vacuity failures.
