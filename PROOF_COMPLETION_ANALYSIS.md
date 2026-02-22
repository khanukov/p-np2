# Proof Completion Analysis

## Executive Summary

The repository contains a Lean 4 formalization of a conditional proof that P != NP,
following a four-step pipeline:
**Step A** (Switching-Atlas) -> **Step B** (Capacity Bound) -> **Step C** (Anti-checker Lower Bounds) -> **Step D** (Hardness Magnification).

The **core contradiction** (`noSmallLocalCircuitSolver_partial_v2`) is **genuinely proved** --
no local function on partial MCSP inputs can solve the Gap Partial MCSP promise.
However, the proof depends on **several conditional hypotheses** that must be
externally provided. Below is a systematic identification of what is proved, what
is missing, and what requires attention.

---

## 1. What IS Fully Proved (No Axioms, No Sorry)

### 1.1. Core Counting / Anti-checker (Step B + Step C core)

| File | Key Result | Status |
|------|-----------|--------|
| `Counting/ShannonCounting.lean` | `exists_hard_function_with_constraints` -- Shannon counting via pigeonhole | **Proved** |
| `Counting/Atlas_to_LB_Core.lean` | `no_bounded_atlas_of_large_family` -- capacity bound | **Proved** |
| `LowerBounds/AntiChecker_Partial.lean` | Union-bound, hard-table existence, family counting | **Proved** |
| `LowerBounds/MCSPGapLocality.lean` | `no_local_function_solves_mcsp` -- core locality impossibility | **Proved** |
| `LowerBounds/AntiChecker_Partial.lean:1516` | `noSmallLocalCircuitSolver_partial_v2` -- from locality impossibility | **Proved** |
| `Models/Model_PartialMCSP.lean` | `gapPartialMCSP_in_NP` -- NP membership of Gap Partial MCSP | **Proved** |
| `Complexity/Interfaces.lean` | `P_ne_NP_of_nonuniform_separation_concrete` -- NP not in P/poly + P in P/poly => P != NP | **Proved** |
| `ThirdPartyFacts/PsubsetPpoly.lean` | `P_subset_Ppoly_proof` -- P is contained in P/poly | **Proved** (external package) |

### 1.2. The Core Contradiction Chain (Fully Machine-Verified)

```
SmallLocalCircuitSolver_Partial p
  -> solver.decideLocal gives alive set with |alive| <= tableLen/2
  -> exists_yes_no_agreeing_on_alive: construct YES and NO instances
     that agree on all alive coordinates
  -> locality forces f(x_yes) = f(x_no)
  -> correctness forces f(x_yes) = true, f(x_no) = false
  -> Contradiction (False)
```

This chain is **complete and genuine**. The YES instance uses `Circuit.const false`
(consistent with a partially-defined function), and the NO instance uses a
Shannon-hard function (proved by pigeonhole). The key insight -- that a function
depending on <= N/2 coordinates cannot distinguish these -- is sound.

### 1.3. NP Membership

`gapPartialMCSP_in_NP` is proved by exhibiting a polynomial verifier. The verifier
simply checks `gapPartialMCSP_Language p n x` and requires a trivial certificate
(any bit suffices when the language accepts). This is correct because Gap Partial
MCSP is a promise problem embedded as a language, so YES instances can be verified
by checking the promise condition directly.

---

## 2. Remaining Conditional Hypotheses (What Is NOT Proved)

The final theorems like `NP_not_subset_PpolyFormula_final` and `P_ne_NP_final`
require the following external hypotheses:

### 2.1. HYPOTHESIS H-1: `StructuredLocalityProviderPartial` (Critical)

**Definition** (`Facts_Magnification_Partial.lean:49`):
```lean
def StructuredLocalityProviderPartial : Prop :=
  forall (p : GapPartialMCSPParams) (delta : Rat),
    FormulaLowerBoundHypothesisPartial p delta ->
    PpolyFormula (gapPartialMCSP_Language p) ->
      RestrictionLocalityPartial p
```

**What it requires:** Given that GapMCSP has a lower bound against AC0 formulas
AND a P/poly formula family solves GapMCSP, produce a local circuit solver.

**Current status:** NOT proved. This is provided through one of three routes:
- `FormulaHalfSizeBoundPartial` -- assumes formula size <= tableLen/2 at target length
- `FormulaCertificateProviderPartial` -- assumes a shrinkage certificate exists
- `ConstructiveLocalityEnginePartial` -- assumes explicit engine with stability + provider

All three routes ultimately need the formula extracted from a P/poly witness to
have either small support or to be stabilizable under restriction. This is the
**I-4 interface** described in documentation.

**Assessment:** This is the biggest gap. It requires proving that any polynomial-size
formula family, when evaluated at the specific input length `partialInputLen p = 2 * 2^n`,
has size bounded by `2^n / 2` (or equivalently that a shrinkage certificate can be
constructed for it). The `FormulaHalfSizeBoundPartial` approach requires:
```
FormulaCircuit.size (w.family (partialInputLen p)) <= Partial.tableLen p.n / 2
```
This would follow if the polynomial bound `polyBound n <= n^c + c` gives
`polyBound(2*2^n) <= 2^n / 2` for sufficiently large n. For n >= 8 this is
`polyBound(512) <= 128`, which requires `512^c + c <= 128` -- **impossible for c >= 1**.

**This means `FormulaHalfSizeBoundPartial` is likely FALSE for any non-trivial
polynomial bound.** A polynomial-size formula at input length N = 2*2^n can have
size up to N^c, and N^c >> 2^n/2 for c >= 1 and large n.

The alternative route via `FormulaCertificateProviderPartial` (shrinkage certificates)
is the intended path but is **not formalized**.

### 2.2. HYPOTHESIS H-2: `AsymptoticFormulaTrackHypothesis` (Critical)

**Definition** (`FinalResult.lean:19-23`):
```lean
structure AsymptoticFormulaTrackHypothesis where
  N0 : Nat
  pAt : forall n, N0 <= n -> GapPartialMCSPParams
  pAt_n : forall n (hn : N0 <= n), (pAt n hn).n = n
  pAt_hyp : forall n (hn : N0 <= n), FormulaLowerBoundHypothesisPartial (pAt n hn) 1
```

**What it requires:** For all sufficiently large n, the Step C lower bound
(AC0 bounded statement) holds at that parameter size.

**Current status:** NOT proved. This requires `AC0BoundedStatementPartial`, which
says: every small AC0 solver for Partial MCSP leads to contradiction, given that
the AC0 family witness (`AC0FamilyWitnessProp`) exists for the all-functions family.

The alternative route `AsymptoticDefaultMultiSwitchingHypothesis` provides the
multi-switching witness explicitly, but this witness itself is not constructed.

### 2.3. HYPOTHESIS H-3: `hFormulaToPpoly` Bridge (Critical for P != NP)

**Definition:** `NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly`

**What it requires:** If there exists L in NP not in PpolyFormula, then there
exists L' in NP not in Ppoly.

**Current status:** NOT proved. This is a non-trivial implication because
`PpolyFormula` (fixed syntax: AND/OR/NOT formulas) is **strictly weaker** than
`Ppoly` (arbitrary polynomial-size circuits with arbitrary evaluation). The
inclusion `PpolyFormula L -> Ppoly L` is proved, but the separation direction
`not PpolyFormula -> not Ppoly` does NOT follow from this inclusion.

**Assessment:** This is a **genuine logical gap**. The proof shows
`NP not_subset PpolyFormula`, but this does NOT immediately imply
`NP not_subset Ppoly`. A formula (AND/OR/NOT with no fan-in restriction) is
strictly less expressive than a general Boolean circuit. A language could be
in Ppoly (via general circuits) but not in PpolyFormula.

However, the project defines `FormulaCircuit` with unbounded fan-in AND/OR gates,
which means formulas can simulate any circuit with polynomial blowup (via
De Morgan's laws and recursive decomposition). So `Ppoly L -> PpolyFormula L` might
actually hold with polynomial overhead, making this bridge provable. But this
equivalence is NOT currently proved in the codebase.

### 2.4. HYPOTHESIS H-4: `ShrinkageWitness.Provider` (Structural)

The `Facts.LocalityLift.ShrinkageWitness.Provider` typeclass must be instantiated
for each general solver. Currently the only default is `canonicalProvider` which
provides a trivial witness for `fun _ => false` -- **not for the actual solver
function**.

For the real proof, one needs a `ShrinkageCertificate` that certifies:
1. A restriction `r` with `|r.alive| <= inputLen/4`
2. Stability: `generalEval (r.apply x) = generalEval x` for all x

This is the multi-switching / random-restriction argument that is standard in
circuit complexity but **not formalized**.

---

## 3. Potential Logical Issues

### 3.1. NP Membership Verifier (Minor Issue)

The NP verifier for GapMCSP (`gapPartialMCSP_verify_with_degree`) computes
`gapPartialMCSP_Language p n x && w[0]`. This means the verifier **evaluates
the language function directly** and uses the certificate only as a dummy bit.

This is technically valid for a promise problem formulated as a total language
(where the language function is computable), but it sidesteps the traditional
NP witness structure. The verifier runs in time proportional to evaluating
`gapPartialMCSP_Language`, which checks circuit consistency -- this involves
iterating over all circuits of bounded size, which is exponential in general.

However, the formal `NP` definition in `Interfaces.lean:292` does NOT actually
require the verifier to run in polynomial time -- it only requires:
```
runTime (n + certificateLength n k) <= (n + certificateLength n k)^c + c
```
and the `runTime` parameter is freely chosen. So the proof satisfies the formal
type but the `runTime` function is not connected to actual computation.

**Assessment:** The formal definition of NP in this codebase allows arbitrary
verifier semantics with an unconnected runtime bound. This is **logically unsound**
as a formalization of NP -- a cheating verifier can claim any runtime. The `NP_TM`
variant using Turing machines is more faithful but unused in the main pipeline.

### 3.2. Formula-vs-Circuit Expressiveness Gap

As noted in H-3, the proof establishes `NP not_subset PpolyFormula` but needs
`NP not_subset Ppoly` for P != NP. The `FormulaCircuit` type allows:
- `const`, `input`, `not`, `and`, `or`

A formula is a tree (no shared sub-circuits). General circuits (DAGs with shared
gates) can be exponentially more compact. The `Circuit` type in
`Model_PartialMCSP.lean` has the same constructors but the semantics are identical
(both are trees). So `Ppoly` as defined may actually be equivalent to `PpolyFormula`
in this formalization, in which case the bridge is trivial. But this equivalence
proof is absent.

### 3.3. False-Derived Theorems

Several theorems are derived via `False.elim` after establishing contradictions:
- `antiChecker_exists_testset_partial` (line 1159)
- `antiChecker_exists_testset_local_partial` (line 1385)
- `antiChecker_exists_large_Y_partial_of_false`
- `antiChecker_exists_large_Y_local_partial_of_false`

These are **not vacuous** -- they genuinely produce `False` from the assumption that
a small solver exists, and then use `False.elim` to construct arbitrary data.
This is logically valid.

---

## 4. What Needs to Happen to Complete the Proof

### Priority 1: Shrinkage Certificate Formalization (H-1 + H-4)

The single most important missing piece. Requires:
1. Formalizing the multi-switching lemma for AC0 circuits
2. Constructing a `ShrinkageCertificate` from a random restriction argument
3. Proving that the restriction stabilizes the solver function
4. Proving that `|alive| <= inputLen/4`

This is standard circuit complexity (Hastad's switching lemma + extensions) but
involves substantial probabilistic reasoning that needs formalization.

### Priority 2: AC0 Lower Bound Witness (H-2)

Need to either:
- Prove `AC0FamilyWitnessProp` for the all-functions family (that any AC0 family
  of bounded size can approximate all functions), OR
- Provide an explicit `AC0MultiSwitchingWitness`

This is the Step A part of the pipeline applied to concrete AC0 parameters.

### Priority 3: Formula-to-Ppoly Bridge (H-3)

Two approaches:
- **Easy (if `Ppoly` uses tree circuits):** Show `Ppoly L <-> PpolyFormula L`
  by observing both use tree-shaped circuits with the same gates
- **Hard (if `Ppoly` should use DAG circuits):** Need to either redefine `Ppoly`
  to use DAGs, or prove that the separation against formulas implies separation
  against DAGs (using formula-to-circuit conversion theorems)

### Priority 4: Fix NP Definition (if needed for rigor)

The current `NP` definition is semantically weak. Either:
- Use `NP_TM` throughout the pipeline, or
- Add a constraint connecting `verify` to `runTime` via TM semantics

---

## 5. Summary Table

| Component | Proved? | Depends On |
|-----------|---------|-----------|
| Shannon counting (pigeonhole) | YES | Nothing |
| Capacity bound (atlas) | YES | Nothing |
| no_local_function_solves_mcsp | YES | Nothing |
| noSmallLocalCircuitSolver_partial_v2 | YES | Nothing |
| gapPartialMCSP_in_NP | YES (but see 3.1) | NP definition |
| P subset P/poly | YES | External package |
| NP not_subset Ppoly + P subset Ppoly => P != NP | YES | Nothing |
| StructuredLocalityProviderPartial | **NO** | Shrinkage formalization |
| AsymptoticFormulaTrackHypothesis | **NO** | AC0 switching witness |
| NP_not_subset_PpolyFormula -> NP_not_subset_Ppoly | **NO** | Circuit equivalence |
| ShrinkageCertificate construction | **NO** | Random restriction theory |

---

## 6. Honest Assessment

The proof has a **solid and genuine core**: the locality impossibility argument
for Partial MCSP is correctly formalized. The counting arguments (Shannon, atlas
capacity) are real. The logical structure from `NP not_subset P/poly` to `P != NP`
is correct.

However, the proof is **far from complete**. The three critical hypotheses (H-1, H-2,
H-3) represent substantial mathematical content:

- **H-1 (Locality Provider)** encapsulates the entire random-restriction / switching
  lemma technology. This is the hardest piece to formalize and represents months of
  work.
- **H-2 (AC0 Lower Bound)** requires constructing the multi-switching witness, which
  is the quantitative heart of the switching lemma.
- **H-3 (Formula-to-Circuit Bridge)** may be trivial or hard depending on whether
  `Ppoly` in the formalization is actually equivalent to `PpolyFormula`.

The proof strategy (magnification via GapMCSP) is well-established in the literature
(OPS'20, CJW'22), and the formalization correctly implements the logical dependencies.
But the unformalized hypotheses are not "details" -- they contain the main technical
difficulty of the entire approach.
