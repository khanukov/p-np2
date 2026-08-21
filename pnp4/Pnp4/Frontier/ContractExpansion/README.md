# ContractExpansion — verified conditional decision→search extraction

This directory formalizes a **verified, conditional** chain that, from a
`PpolyDAG` membership of a prefix-extension language, extracts a polynomial-size
bounded *search* solver, and contrapositively yields `¬ PpolyDAG`; together with a
growth-assumption reduction, an NP-membership interface, and a concrete-codec
construction, it assembles a `VerifiedNPDAGLowerBoundSource` from three explicit
inputs.

## Why this exists

The pnp4 mainline (`Frontier/SearchMCSPMagnification.lean`,
`Frontier/CompressionMagnification.lean`) reduces a search-MCSP weak lower bound to
`VerifiedNPDAGLowerBoundSource` through one abstract field,

```
SearchMCSPMagnificationContract.magnifiesToVerifiedDAGSource :
  target.noBoundedSolver → VerifiedNPDAGLowerBoundSource
```

which is an *unexplained jump*.  The modules here **replace that jump with a
machine-checked conditional chain**, so that the only remaining mathematics is a
small set of explicit, clearly-typed hypotheses — not a hidden contract field.

> **Honest status.** This directory **does not prove `P ≠ NP`**, and **does not
> prove `NP ⊄ PpolyDAG` unconditionally**. Every headline result is *conditional*
> on explicit hypotheses (a weak lower bound, an NP verifier witness, and a
> concrete codec / witness-growth premise). What is achieved is the **replacement
> of the abstract magnification jump by a verified conditional chain** that exposes
> the exact remaining obligations. Green CI / `./scripts/check.sh` are hygiene
> checks, not progress on the open mathematics.

All headline theorems are tracked in `pnp4/Pnp4/Tests/AxiomsAudit.lean`; the
arithmetic/structural results are `Classical`-free (`[propext, Quot.sound]`), and
the results touching the (classical) `PrefixExtensionLanguage` additionally use
`Classical.choice`.

## The chain at a glance

```
PpolyDAG (PrefixExtensionLanguage (treeMCSPConcretePrefixParser threshold codec))
   │  decider family for the prefix-query language
   ▼  greedy query circuits + bundle  (per-output-bit shared DagBundle)
BoundedSearchSolver (treeProblem codec) C_DAG (extracted schedule)         [forward, Block 9b]
   │  contrapositive
¬ (bounded search solver at every extracted schedule)  ⇒  ¬ PpolyDAG       [Block 9c]
   │  polynomial reconciliation, under growth assumptions
NoPolynomialBoundedSearchSolver codec  ⇒  ¬ PpolyDAG                        [Block 9d]
   │  + NP-membership of the language        + growth from one witness premise
VerifiedNPDAGLowerBoundSource                                              [Blocks 9e / capstone]
   ▼  existing pnp3 bridge
NP ⊄ PpolyDAG     (and thence  P ≠ NP)        — both kept strictly conditional
```

## Module map

### Prefix-extension language and semantics
- `PrefixExtensionLanguage.lean` — `PrefixInput`, `PrefixParser`,
  `PrefixExtendable` / `PrefixExtendableInput`, and the (classical, noncomputable)
  language `PrefixExtensionLanguage parser : Pnp3.ComplexityInterfaces.Language`,
  with acceptance characterizations (`PrefixExtensionLanguage_accepts_iff`, …).
- `PrefixExtendableSplit.lean` — pure semantics of extending a prefix by one bit
  (`witnessPrefixExtendable_split` and the "other-bit-forced" lemmas).
- `PrefixParserConvention.lean` — the concrete tree-MCSP serialization
  (`treeMCSPConcretePrefixParser`, `treeMCSPPrefixM`, `tagLen`/`gammaLen`/`idxWidth`/
  `bitLength`, the field encoder/parser and its round-trip).
- `PrefixExtensionLanguageNP.lean`, `PrefixExtensionLanguageRuntime.lean` —
  **obligation records** (parser/verifier/runtime budgets, `RuntimeAware…`). These
  enumerate sub-tasks; they are *not* NP-membership proofs.

### DAG decider adapter and query composition
- `C_DAG_Adapter.lean` — the `C_DAG : CircuitFamilyClass` adapter
  (`Family n = DagCircuit n`) and the `InPpolyDAG → C_DAG`-decider bridge.
- `QueryBuilder.lean`, `QueryComposition.lean`, `PrefixQueryBuilder.lean` — generic
  query-circuit builder interface and composition with a DAG decider
  (`composeDeciderWithQuery`), with eval/size accounting.

### Query circuits for the tree-MCSP prefix language
- `TreeMCSPPrefixSerializer.lean`, `TreeMCSPZeroPrefixBuilder.lean`,
  `TreeMCSPPrefixQueryCircuits.lean`, `TreeMCSPPrefixStateQueryCircuits.lean`,
  `TreeMCSPTrueExtensionQuery.lean` — concrete query-bit circuits realizing the
  prefix-state and true-extension queries `(i, p ++ true)` over the truth-table
  input, with eval/size lemmas.

### Greedy bounded-search-solver construction
- `TreeMCSPGreedyExtendable.lean` — the greedy prefix (`greedyPrefix`,
  `greedyTrueBundleUpTo`), `CorrectNextBitDecider`, and `greedyPrefix_extendable`.
- `TreeMCSPGreedyBundleStep.lean`, `TreeMCSPGreedyBundleFold.lean` — shared-bundle
  greedy step / fold (linear-size accounting, avoiding the naive `2^i` blow-up).
- `TreeMCSPGreedyOutputCircuits.lean`, `TreeMCSPGreedyTrueOutputCircuits.lean` —
  per-output-bit circuits and their size/eval bounds.
- `TreeMCSPDeciderCorrect.lean` — `DecidesPrefixExtensionLanguage` and
  `correctNextBitDecider_of_decidesLanguage`.
- `TreeMCSPGreedySolves.lean` — `greedyTrueOutputCircuit_solves` (the solver's
  `solves` obligation, given a correct decider).
- `NaiveGreedySizeSpike.lean` — the size-recurrence spike showing the naive per-bit
  composition blows up, motivating the shared bundle.

### Bounded search solver + forward bridge
- `TreeMCSPBoundedSolver.lean` — `boundedSearchSolver_of_deciderFamily`.
- `BoundedSolverFromPpoly.lean` — `boundedSearchSolver_of_PpolyDAG_prefixExtension`
  (Block 9b): `PpolyDAG (PrefixExtensionLanguage …) → ∃ c, BoundedSearchSolver …`.

### Contrapositive and polynomial reconciliation
- `NoSolverContrapositive.lean` (Block 9c) — `NoExtractedScheduleSolver` and
  `not_PpolyDAG_prefixExtension_of_noExtractedScheduleSolver`.
- `ExtractedScheduleGrowth.lean` (Block 9d) — the `PolyBoundedInTable` API,
  `TreeMCSPExtractionGrowthAssumptions`, `NoPolynomialBoundedSearchSolver`, and
  `not_PpolyDAG_prefixExtension_of_noPolynomialBoundedSearchSolver`.

### Growth-assumption reduction (Block 10a)
- `WitnessGrowthReduction.lean` — `treeMCSPExtractionGrowthAssumptions_of_witnessPoly`
  derives the full growth assumptions from the **single** premise
  `PolyBoundedInTable codec.witnessBits` (the ambient half is proved), packaged as
  the minimal interface `PolynomialWitnessCodec` with `.toGrowthAssumptions`.

### NP-membership interface (Block 11a)
- `PrefixExtensionNPWitness.lean` — `PrefixExtensionNPWitness parser` bundles a
  concrete verifier TM, a polynomial runtime bound, and a certificate-correctness
  equivalence; `prefixExtensionLanguage_in_NP_of_witness` repackages it into
  `NP (PrefixExtensionLanguage parser)`. This is an **interface** (mirroring the
  repo's `GapPartialMCSP_TMWitness` idiom), **not** a proof of NP membership.

### Conditional verified source
- `ConditionalVerifiedSource.lean` (Block 9e) —
  `verifiedSource_of_noPolynomialBoundedSearchSolver` (growth + no-poly-solver + NP
  ⇒ `VerifiedNPDAGLowerBoundSource`), and the `NP ⊄ PpolyDAG` wrapper.
- `ExplicitConditionalSource.lean` (capstone) —
  `verifiedSource_of_explicit_interfaces` assembling the source from the three
  explicit interfaces (`PolynomialWitnessCodec`, `NoPolynomialBoundedSearchSolver`,
  `PrefixExtensionNPWitness`), and `NP_not_subset_PpolyDAG_of_explicit_interfaces`.

### Verifier semantics and tape layout (NP-verifier track)
- `TreeMCSPPrefixSemanticVerifier.lean` — the computable `Bool`-valued verifier
  `treePrefixSemanticAccepts` (parse the query, slice the witness prefix out of the
  certificate, check prefix agreement + codec verification) and its correctness
  `treePrefixSemanticAccepts_correct`: the **mathematical core** of the NP-membership
  obligation at `k = 1`. It builds **no** Turing machine and proves **no** runtime
  bound; the `TM.accepts (concatBitstring x w) = treePrefixSemanticAccepts …` bridge
  is still missing. The module is generic in the codec (it does **not** import
  `ConcreteTreeCodec` / `ThresholdGrowth`); the directed regression checks at the
  concrete `thresholdPoly 1` codec live in
  `Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean`
  (`TreeMCSPPrefixSemanticVerifierSurface`).
- `TreeMCSPPrefixVerifierLayout.lean` — data-independent tape arithmetic for that
  future machine: input length / certificate start, the `concatBitstring` bit
  projections, the start-tape reading lemmas, the query field offsets, and the
  gamma payload-read geometry. Layout facts only; the offset/fit lemmas are
  `Classical`-free, the `concatBitstring` projections and the tape-reading lemmas
  built on them inherit `Classical.choice` from the noncomputable `concatBitstring`
  itself. Every theorem of both modules has its own `#print axioms` line in
  `Pnp4/Tests/AxiomsAudit.lean` and its own `#check` in the surface tests.

These are infrastructure for a future NP-membership proof: no lower bound, no change
to `SearchMCSPMagnificationContract`, and no `P ≠ NP` claim follows from them.

### The length-blindness obstruction and the content-truthful language `L'`
The `pnp3` TM model is **length-blind**: `initialConfig` loads the input and pads with
the blank `false`, so a word and its zero-extension induce the *same* tape, while
`PrefixExtensionLanguage` gates membership on the **physical** input length (the
parser's `m = treeMCSPPrefixM codec n` check). A length-blind machine cannot observe
that gate, so `PrefixExtensionNPWitness.correct` looks out of reach for the planned
idle-sink machine class. **This is a review of the definitions, not a Lean theorem**:
no impossibility result is formalized anywhere in this directory. The response
replaces the *language*, not the chain — four modules, in dependency order:

- `ContentPrefixExtension.lean` — `padRead` / `padWord` (the blank-padded tape read),
  `contentHeader?` (the gamma header decoded on the `2N+1`-padded word),
  `contentInput?` (the **existing** strict parser re-run on the window of the
  *content-computed* length, so the parser's physical-length gate is satisfied by
  construction), `contentWitness`, `ContentAccepts`, the language
  `ContentPrefixExtensionLanguage` (`L'`), and the NP-witness interface
  `ContentPrefixExtensionNPWitness`. Definitions plus the `accepts_iff` unwrapping;
  the interface is a **hypothesis**.
- `ContentPrefixExtensionCoincidence.lean` — reader monotonicity under ambient
  widening (`readBit?_mono`, `readNatBE_mono`, `decodeGammaAux?_mono`), parse
  inversion (`parseTreeMCSPPrefixInput_inversion`), the two window computations on a
  concatenated word, and the headline
  `ContentPrefixExtensionLanguage_eq_of_parse`: on every query the strict parser
  accepts at its convention length, `L'` agrees with the length-gated language.
- `ContentPrefixExtensionTransfer.lean` — the decision→search extraction transferred
  to `L'` (the greedy machinery only ever queries deciders on constructed, parseable
  queries), ending in
  `not_PpolyDAG_contentPrefixExtension_of_noPolynomialBoundedSearchSolver`: the
  **same** open lower-bound hypothesis pins `L'` outside `PpolyDAG`. This is the same
  one-way `PpolyDAG → BoundedSearchSolver` direction as the length-gated chain; **no
  converse** is proved.
- `ContentConsolidatedSource.lean` — `verifiedSourceCT_of_noPolynomialBoundedSearchSolver`
  (generic), `verifiedSourceCT_treePoly` and `NP_not_subset_PpolyDAG_treePolyCT`: the
  consolidated conditional source re-routed through `L'`, still depending on exactly
  two explicit hypotheses (`NoPolynomialBoundedSearchSolver` — input (1), unchanged —
  and `ContentPrefixExtensionNPWitness` — input (2)). The original length-gated chain
  is left intact for reference.

What this does **not** establish, stated explicitly because the module names invite
the opposite reading:

- **No padding-stability result.** The design intent is that `L'` depend only on the
  blank-padded tape, but no lemma proving that (`ContentAccepts` invariant under
  padding to a larger physical length, or under equality of padded tapes) is present
  in this directory. Without it, the gain over the length-gated language is
  *definitional* — `ContentAccepts` never mentions the physical length — and nothing
  more. The obstruction is not formally shown to be evaded.
- **No non-vacuity / satisfiability.** Nothing proves that any word is
  `ContentAccepts`-accepted, or that `L'` is non-empty.
- **No verifier.** No Turing machine, no runtime bound, and no
  `TM.accepts … = ContentAccepts …` bridge for `L'` is constructed anywhere.
  Whether a polynomial-time verifier for `L'` exists is open, and
  `ContentPrefixExtensionNPWitness` remains an unproved interface.
- **No separation.** Both open inputs stay explicit arguments of every source in
  `ContentConsolidatedSource.lean`; no `P ≠ NP` claim follows.

Every theorem of the four modules has its own `#print axioms` line in
`Pnp4/Tests/AxiomsAudit.lean` and its own `#check` in
`Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean`
(`ContentPrefixExtensionSurface`).

### Concrete codec (constructed)
- `ConcreteCodecGap.lean` (Block 12a) — the audit verdict (no concrete
  `TreeCircuitWitnessCodec` existed *at that time*) + the proved packing reduction
  `SelfDelimitingCircuitCode.toCodec` (a self-delimiting encoder with a width bound
  ⇒ a fixed-width codec, by zero-padding).
- `CircuitTreeBridge.lean` (Block 12b) — `toTree`/`fromTree` between
  `Pnp3.Models.Circuit` and the isomorphic `CircuitTree`, the native encoder/decoder
  `encodeCircuit`/`decodeCircuit`, and the native round-trip
  `decodeCircuit_encodeCircuit`.
- `CircuitEncodingLength.lean` (Block 12c) — `length_encodeCircuit_le`:
  `(encodeCircuit width h_width c).length ≤ (width + 4) * Circuit.size c`.
- `CircuitDecodeDepthFree.lean` (Block 12d) — `length_encodeCircuit_ge` (matching lower
  bound) and the depth-budget-free decoder `decodeCircuitFull` with its all-`n`
  round-trip `decodeCircuitFull_encodeCircuit`.
- `ConcreteTreeCodec.lean` (Block 12e) — **the concrete codec itself**:
  `treeSelfDelimitingCode`, `treeCircuitWitnessCodec`, `polyBoundedInTable_bitLength`,
  `polyBoundedInTable_treeWitnessBits_of_thresholdPoly`, and the packaged
  `treePolynomialWitnessCodec`.  The "no concrete codec" gap recorded in 12a is closed.
- `ConcreteTreeCodecSource.lean` (Block 12f) —
  `verifiedSource_of_treeCodec_noPolynomialBoundedSearchSolver` and
  `NP_not_subset_PpolyDAG_of_treeCodec_interfaces`: the conditional source instantiated
  at the concrete codec.

### Threshold growth and consolidation
- `ThresholdGrowth.lean` (Block 13a) — `thresholdLinear` / `thresholdQuadratic` /
  `thresholdPoly` and their growth discharges `polyBoundedInTable_thresholdLinear` /
  `_thresholdQuadratic` / `_thresholdPoly`.
- `ConsolidatedTreeSeparation.lean` (Block 13b) — `verifiedSource_treePoly` and
  `NP_not_subset_PpolyDAG_treePoly`: the collapsed two-hypothesis form at
  `thresholdPoly k`.

## What is proved vs. open

**Proved (all conditional, machine-checked, no `sorry`):**
- the forward extraction `PpolyDAG → BoundedSearchSolver` and its contrapositive;
- the polynomial reconciliation `NoPolynomialBoundedSearchSolver + growth ⇒ ¬ PpolyDAG`;
- the assembly of `VerifiedNPDAGLowerBoundSource` (hence conditional `NP ⊄ PpolyDAG`)
  from three explicit interfaces;
- the growth reduction (two growth premises → one);
- the concrete-codec packing reduction, the `Circuit ↔ CircuitTree` bridge with an
  **all-`n`** round-trip, and matching encoding-length upper and lower bounds;
- the **first concrete `TreeCircuitWitnessCodec`** (`treeCircuitWitnessCodec`,
  `ConcreteTreeCodec.lean`) — closing the "no concrete codec" gap — and its
  instantiation of the conditional source (`ConcreteTreeCodecSource.lean`);
- `PolyBoundedInTable` for the canonical polynomial thresholds
  (`thresholdLinear/Quadratic/Poly`, `ThresholdGrowth.lean`), which **discharges**
  the growth leg for those thresholds;
- the **consolidated** conditional separation at a concrete polynomial threshold
  (`verifiedSource_treePoly` / `NP_not_subset_PpolyDAG_treePoly`,
  `ConsolidatedTreeSeparation.lean`): at `thresholdPoly k` only the two genuinely-hard
  inputs below remain as hypotheses.

**Open — for a concrete polynomial threshold, exactly two inputs:**
1. **`NoPolynomialBoundedSearchSolver (treeCircuitWitnessCodec (thresholdPoly k))`** —
   a genuine `P/poly` circuit lower bound for the concrete tree-MCSP search problem.
   The hard, research-level mathematics; **not** a Lean engineering task.
2. **`PrefixExtensionNPWitness (treeMCSPConcretePrefixParser …)`** — a concrete
   verifier Turing machine with a polynomial runtime bound and certificate
   correctness (the NP / runtime track; engineering-heavy but in-principle closable).
   For the length-gated language this input runs into the length-blindness review
   above. The `L'` route offers an alternative target,
   **`ContentPrefixExtensionNPWitness (treeCircuitWitnessCodec (thresholdPoly k))`**,
   whose language carries no physical-length gate. That is a definitional difference
   only: no padding-stability lemma, verifier TM, runtime bound, or `TM.accepts`
   bridge is proved for `L'` either, so input (2) is an unproved interface on **both**
   routes.

(For an *arbitrary* threshold there is a third input, `PolyBoundedInTable threshold`;
it is proved for the canonical polynomial thresholds, so it disappears there.)

### Runtime model behind input (2)

`NP` here is the repository's `NP_TM` (`pnp3/Complexity/Interfaces.lean`) over the
machine model `Pnp3.Internal.PsubsetPpoly.TM`
(`pnp3/Complexity/PsubsetPpolyInternal/TuringEncoding.lean`).  That model is:

* a **deterministic single-tape** machine over the binary alphabet, with no separate
  read-only input tape, and a fixed tape length `n + runTime n + 1` (`TM.tapeLength`);
* equipped with `runTime : ℕ → ℕ` as a **structure field**, not a derived step count;
* accepted by `TM.accepts`, which is evaluated **at exactly step `runTime n`** — `TM.run`
  iterates `stepConfig` exactly `M.runTime n` times and then checks
  `state = M.accept`.  There is no halting predicate and no "within `t` steps"
  quantifier.

Because the declared budget is also the evaluation point, the
`PrefixExtensionNPWitness.runTime_poly` field is a genuine restriction on the machine,
not a self-certification.  What is **not** formalized is any cross-model
runtime-robustness statement: nothing here relates this single-tape, exact-step model to
multi-tape or read-only-input-tape models.  Input (2) is therefore an obligation *in this
model*, and should be cited that way.

### Honest caveat — this is a reduction, not a magnification win

The decision→search extraction is formalized in **one direction only**:

```text
PpolyDAG (prefix-extension language) → polynomial-size bounded search solver
```

i.e. `boundedSearchSolver_of_PpolyDAG_prefixExtension` (`BoundedSolverFromPpoly.lean`),
together with its contrapositive, which exists in two forms (see the module map above):

* `not_PpolyDAG_prefixExtension_of_noExtractedScheduleSolver`
  (`NoSolverContrapositive.lean`, Block 9c) — the direct contrapositive at the *exact*
  extracted size schedule `extractedSolverSizeBound codec c`, with no growth premise;
* `not_PpolyDAG_prefixExtension_of_noPolynomialBoundedSearchSolver`
  (`ExtractedScheduleGrowth.lean`, Block 9d) — the polynomial-target form, derived from
  the exact-schedule one via `noExtractedScheduleSolver_of_noPolynomial` and therefore
  carrying the extra premise `TreeMCSPExtractionGrowthAssumptions codec`.

Both are the *same* single direction restated; neither is a converse.  The converse
(solver ⇒ `PpolyDAG`) is **not** formalized — this directory contains no `Iff` between
`PpolyDAG` and a solver, and no `PpolyDAG_of_boundedSearchSolver` declaration — so the
chain is a one-way reduction, **not** an equivalence.

Because the instance length is `tableLen n = 2^n`, the no-solver input is therefore
**at least as strong as** the full `P/poly` lower bound — "this concrete NP language is
not in `P/poly`" — and, absent the converse, possibly strictly stronger.  It is **not**
a weak/local bound amplified by a hardness-*magnification* theorem.  The chain makes the
target precise, concrete, and verified-conditional; it does **not** make the open
mathematics easier, and **no** magnification theorem is formalized here.

This directory adds **no** unconditional claim, does **not** modify
`SearchMCSPMagnificationContract`, and adds **no** `P ≠ NP` endpoint wrapper.
