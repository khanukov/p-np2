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

### The physical-length gate and the content-truthful language `L'`
`PrefixExtensionLanguage` gates membership on the **physical** input length (the
parser's `m = treeMCSPPrefixM codec n` check), while `initialConfig` loads the input
into the first `n` tape cells and blanks the rest — so a word and its zero-extension
induce tapes whose *contents* agree cell-by-cell wherever both are defined. The
planned idle-sink verifier reads only that loaded content, so it has no way to
replicate the gate, and `PrefixExtensionNPWitness.correct` looks out of reach **for
that machine class**.

This is emphatically *not* a statement that the `pnp3` model is length-blind — it is
not. `TM.tapeLength n = n + TM.runTime n + 1`, so a word and its zero-extension run on
tapes of *different* lengths; `runTime : ℕ → ℕ` is an arbitrary structure field, hence
length-dependent in general; and `TM.accepts` is evaluated at exactly step
`runTime n`, which again moves with the input length
(`pnp3/Complexity/PsubsetPpolyInternal/TuringEncoding.lean`). A machine in this model
can in principle depend on `n`; what the planned idle-sink construction cannot do is
recover the gate from the loaded content alone. **The whole argument is a review of
the definitions, not a Lean theorem**: no impossibility result is formalized anywhere
in this directory. The response replaces the *language*, not the chain — eight modules,
in dependency order:

- `ContentPrefixExtension.lean` — `padRead` / `padWord` (the blank-padded tape read),
  `contentHeader?` (the gamma header decoded on the `2N+1`-padded word),
  `contentInput?` (the **existing** strict parser re-run on the window of the
  *content-computed* length `M n'`; the parser re-decodes its own header from that
  narrower window and gates on `m = M n_dec`, so the gate is *intended* to compare
  `M n'` with itself and never reject — **intended, not proved**: that needs
  `n_dec = n'`, i.e. the narrowing direction of the decode, whereas only the widening
  lemma `decodeGammaAux?_mono` exists), `contentWitness`, `ContentAccepts`, the
  language `ContentPrefixExtensionLanguage` (`L'`), and the NP-witness interface
  `ContentPrefixExtensionNPWitness`. Definitions plus the `accepts_iff` unwrapping;
  the interface is a **hypothesis**.
- `ContentParseFieldRecovery.lean` — FEAS-0 slice, part 1 (`VERIFIER_RETARGET_PLAN.md` §1.0): the
  parser field recovery the feasibility route needs and the parse inversion below does **not**
  provide. `parseTreeMCSPPrefixInput_x_slice` re-walks the same success cascade as
  `parseTreeMCSPPrefixInput_inversion` but keeps the `x` branch, pinning `input.x` to the canonical
  `x`-slice of its own ambient vector; `contentInput?_x_apply` is the content-side pointwise form,
  `pr.2.x j = padRead z (tagLen + cg + j)`. The gamma width is carried **symbolically** — both
  conjuncts share one existential `consumed`, and neither statement identifies it with
  `gammaLen input.n` nor relates `pr.2.n` to the header value `pr.1`, so no injectivity of
  `treeMCSPPrefixM codec` and no gamma canonicity is used (plan stop/go F0b). Both entries are
  axiom-light: `[propext, Quot.sound]`, no `Classical.choice`. Scope is recovery only; the separate
  part-2 module below proves the target bound. It gives no satisfiability of `ContentAccepts` and
  constructs no verifier TM, runtime bound or `TM.accepts` bridge.
- `ContentTargetSizeBound.lean` — FEAS-0 slice, part 2 and outcome (a). It computes the concrete
  all-blank witness decode at zero and positive parsed targets, uses the input-zero projection to
  force a supported truth-table cell and `tableLen r ≤ N`, and proves
  `contentAccepts_target_poly_treePoly`. The proof works at `r := pr.2.n`, transports only through
  `treeMCSPPrefixM codec n_header = treeMCSPPrefixM codec r`, and uses the existing
  `PolyBoundedInTable` / `powAdd` chain; it has no I1 dependency and never infers
  `r = n_header`. This freezes the content target, but remains Infrastructure: no verifier TM,
  runtime theorem, non-vacuity result, NP-membership proof, or lower-bound obligation is discharged.
- `ContentPrefixExtensionCoincidence.lean` — reader monotonicity under ambient
  widening (`readBit?_mono`, `readNatBE_mono`, `decodeGammaAux?_mono`), parse
  inversion (`parseTreeMCSPPrefixInput_inversion`), the two window computations on a
  concatenated word, the proposition-level
  `ContentPrefixExtendable_iff_of_parse`, and the Boolean-language headline
  `ContentPrefixExtensionLanguage_eq_of_parse`: for
  `y : PrefixBitVec (treeMCSPPrefixM codec n)`, under **both** `hparse`
  (`parseTreeMCSPPrefixInput … y = some input`) and `hn : input.n = n`, `L'` agrees
  with the length-gated language at `treeMCSPPrefixM codec n`. `hn` is a genuine
  second hypothesis: inversion yields only
  `treeMCSPPrefixM codec input.n = treeMCSPPrefixM codec n`, and injectivity of
  `treeMCSPPrefixM codec` is not proved.  The proposition-level theorem is the direct specification
  coincidence and does not route through either classical Boolean language wrapper.
- `ContentPrefixExtensionPadding.lean` — the specification-side obligation the modules
  above leave open: **padding stability**. `padRead_padWord_of_le` /
  `padWord_padWord_of_le` (blank padding past the support is idempotent),
  `readNatBE_padWord_transfer` (fixed-width read transfer **both** ways between
  paddings — the shrinking direction the monotonicity lemmas above cannot give),
  `decodeGammaAux?_padWord_support` (the **blank-tail** lemma: a successful gamma scan
  on a padded word has its terminator strictly inside the support, since every cell
  past the support reads blank), `decodeGammaAux?_padWord_canonical` (the canonical
  re-run; its fuel side condition `N + 1 ≤ fuel' + zeros` is an **explicit hypothesis** of
  the statement — what is *proved* is that the induction preserves it, and that both
  callers discharge it at their concrete fuel `2 * width + 2` with `zeros = 0`), padding
  stability of the three content-computed reads (`contentHeader?_padWord_of_le`,
  `contentInput?_padWord_of_le`, `contentWitness_padWord_of_le`), and the headlines
  `ContentAccepts_padWord_of_le` (acceptance of a **complete** word is unchanged by blank
  padding to any larger physical length) and `ContentAccepts_iff_of_padRead_eq` (any two
  complete finite words with the *same* blank-padded tape are accepted alike). The axiom-light
  `contentHeader?_of_decodeGamma` transports an already-successful strict decode. The helper lemmas
  are generic statements about
  `padRead` / `padWord`, the strict readers and the gamma decoder; the headline results
  are invariance of `ContentAccepts` on complete words. Nothing in the module is a
  statement about the language wrapper (see the scope paragraph below). Verified axiom footprint:
  fourteen entries are `[propext, Quot.sound]`, one (`readBit?_padWord_of_lt`) is axiom-free, and
  no theorem in this module depends on `Classical.choice`.
- `ContentPrefixExtensionPaddingTransport.lean` — the explicitly classical conditional transport
  theorem `ContentAccepts_padWord_of_prefixExtendable`, isolated from the axiom-light padding
  module. It derives `ContentPrefixExtendable` directly from
  `ContentPrefixExtendable_iff_of_parse`, without either Boolean language wrapper. Its statement
  necessarily inherits `Classical.choice` from the pre-existing noncomputable `concatBitstring`.
  It is a **conditional existential**, available only under `hparse`, `hn`, `hext`, and `hT`, so it
  proves no unconditional satisfiability or non-emptiness result.
- `ContentPrefixExtensionTransfer.lean` — the decision→search extraction transferred
  to `L'` (the greedy machinery only ever queries deciders on constructed, parseable
  queries), ending in
  `not_PpolyDAG_contentPrefixExtension_of_noPolynomialBoundedSearchSolver`: the
  **same** open lower-bound hypothesis, together with the same extra growth premise
  `TreeMCSPExtractionGrowthAssumptions` that the length-gated Block 9d form carries,
  pins `L'` outside `PpolyDAG`. (The exact-schedule form
  `not_PpolyDAG_contentPrefixExtension_of_noExtractedScheduleSolver` needs no growth
  premise, mirroring 9c.) This is the same one-way
  `PpolyDAG → BoundedSearchSolver` direction as the length-gated chain; **no
  converse** is proved.
- `ContentConsolidatedSource.lean` — `verifiedSourceCT_of_noPolynomialBoundedSearchSolver`
  (generic), `verifiedSourceCT_treePoly` and `NP_not_subset_PpolyDAG_treePolyCT`: the
  consolidated conditional source re-routed through `L'`. The **generic** source takes
  **three** explicit hypotheses — `TreeMCSPExtractionGrowthAssumptions`,
  `NoPolynomialBoundedSearchSolver`, `ContentPrefixExtensionNPWitness`. Only at the
  concrete threshold, where the growth premise is discharged, do
  `verifiedSourceCT_treePoly` / `NP_not_subset_PpolyDAG_treePolyCT` depend on exactly
  two explicit hypotheses (`NoPolynomialBoundedSearchSolver` — input (1), unchanged —
  and `ContentPrefixExtensionNPWitness` — input (2)). The original length-gated chain
  is left intact for reference.

What the padding lemmas **do** buy, precisely. `L'` carries no *explicit* gate on the
ambient length — no test in `L'` compares the physical `N` against
`treeMCSPPrefixM codec n` — and that alone was a definitional observation, weaker than
length-independence, because `contentHeader?` decodes on `padWord z (2 * N + 1)`, so `N`
fixed both that window's width and the gamma decoder's fuel (`decodeGamma?` uses
`m + 1`). `contentHeader?_padWord_of_le` closes exactly that residual `N`-dependence:
the definition still *mentions* `2 * N + 1`, but its value does not move with `N`. Up
the chain, `ContentAccepts_padWord_of_le` and `ContentAccepts_iff_of_padRead_eq`
upgrade this to full invariance **of `ContentAccepts`**: the ambient physical length of a
*complete* word (query ++ certificate) is not observable in `ContentAccepts` at all, so
that predicate is a function of the blank-padded tape only. It is one ingredient the
planned idle-sink verifier would need, and it is a statement about that predicate of the
*specification* and nothing else.

**Scope — `ContentAccepts`, not the language wrapper.** Padding invariance is *not*
proved for `ContentPrefixExtensionLanguage` (`L'`). Membership of a query `y` at physical
length `m` unfolds to
`∃ w : Bitstring (certificateLength m 1), ContentAccepts codec (concatBitstring y w)`, and
both the certificate length and the offset at which `w` is concatenated are functions of
`m`. Padding `y` moves that boundary and changes the family of certificates quantified
over, so nothing here relates `ContentPrefixExtensionLanguage codec m y` to
`ContentPrefixExtensionLanguage codec m' (padWord y m')`. The `L'` NP-witness interface,
and every TM-side claim, are untouched.

What this does **not** establish, stated explicitly because the module names invite
the opposite reading:

- **No machine-side conclusion.** Padding stability is an invariance of the
  specification. The `pnp3` model is still **not** length-blind (tape length and
  evaluation step both move with the input length, as above), no machine is built, and
  the obstruction remains a review of the definitions, never a Lean impossibility
  theorem — so nothing here shows that a verifier for `L'` exists or is achievable.
- **No proof that the re-decode gate is vacuous.** `contentInput?` re-runs the strict
  parser, which re-decodes the gamma header from the narrow window `padWord z (M n')`
  and applies its own gate `m = M n_dec`. That the gate never fires is the *intent*
  (it needs `n_dec = n'`, the narrowing direction of the decode); only the widening
  lemma `decodeGammaAux?_mono` is proved, so no lemma here rules out
  `contentInput? = none` at the gate. Padding stability does not help: it says the two
  sides agree *including on failure*, not that either side succeeds.
- **No unconditional non-vacuity / satisfiability.** Nothing proves *unconditionally*
  that any word is `ContentAccepts`-accepted, or that `L'` is non-empty. The one
  existential statement about `ContentAccepts`,
  `ContentAccepts_padWord_of_prefixExtendable`, is a conditional existential: it is
  available only under the four explicit hypotheses of its statement — `hparse`, `hn`,
  `hext`, none discharged anywhere, plus the padding bound `hT`, which only fixes the
  target length.
- **No padding invariance of the language `L'`.** The padding lemmas are generic
  statements about `padRead` / `padWord`, the strict readers and the gamma decoder,
  topped by invariance of `ContentAccepts` on complete words; the wrapper quantifies
  over certificates whose length and concatenation offset both move with the physical
  length, so wrapper-level invariance is unproved (scope paragraph above).
- **No verifier.** No Turing machine, no runtime bound, and no
  `TM.accepts … = ContentAccepts …` bridge for `L'` is constructed anywhere. Note the
  interface's `runTime_poly` field bounds `M.runTime` at the length-dependent point
  `n + certificateLength n 1`, so the CT route does not remove length-dependence from
  the machine side either.
  Whether a polynomial-time verifier for `L'` exists is open, and
  `ContentPrefixExtensionNPWitness` remains an unproved interface.
- **No separation.** Both open inputs stay explicit arguments of every source in
  `ContentConsolidatedSource.lean`; no `P ≠ NP` claim follows.

Every public theorem of the eight modules has its own `#print axioms` line in
`Pnp4/Tests/AxiomsAudit.lean` and its own `#check` in
`Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean`
(`ContentPrefixExtensionSurface`).

**Plan of record for input (2).** `VERIFIER_RETARGET_PLAN.md` (this directory) freezes the
NP-verifier target at `ContentPrefixExtensionNPWitness` / `ContentAccepts`. FEAS-0 outcome (a) is
now proved by `ContentTargetSizeBound.lean`: accepted complete words have polynomially bounded
header convention length. The length-gated `PrefixExtensionNPWitness` remains compiled and audited
for compatibility and is dispreferred, rather than retired, for new verifier work; a new slice may
target it only with an explicit technical or compatibility rationale. The bound does not prove
polynomial-time verifiability of `L'`: the concrete TM, runtime theorem, non-vacuity, and
`TM.accepts` bridge remain open. This is Infrastructure and makes no `P ≠ NP` claim.

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
   For the length-gated language this input runs into the physical-length-gate review
   above (a limitation of the planned idle-sink machine class, **not** of the TM
   model, which is not length-blind). The `L'` route offers an alternative target,
   **`ContentPrefixExtensionNPWitness (treeCircuitWitnessCodec (thresholdPoly k))`**,
   whose language carries no *explicit* gate on the ambient physical length (the
   strict parser's own equality gate survives inside `contentInput?`, applied to the
   computed window, with vacuity unproved). On the specification side that difference
   is now backed by a proof — `ContentAccepts` is invariant under blank padding of a
   *complete* word (`ContentPrefixExtensionPadding.lean`), so its `2N+1` header window
   no longer makes acceptance move with `N`. It buys nothing on the machine side, and
   the target of this input is the *language* `L'`, for which padding invariance is
   **not** proved (the certificate length and concatenation offset both move with the
   physical length): the interface's runtime bound is still taken at the
   length-dependent point `n + certificateLength n 1`, and no verifier TM, runtime
   bound, or `TM.accepts` bridge is proved for `L'` — so input (2) is an unproved
   interface on **both** routes.

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
