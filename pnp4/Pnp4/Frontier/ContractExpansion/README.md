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
in this directory. The response replaces the *language*, not the chain — thirteen modules, listed here in
review order (the `lakefile.lean` registration is the dependency order):

- `ContentPrefixExtension.lean` — `padRead` / `padWord` (the blank-padded tape read),
  `contentHeader?` (the gamma header decoded on the `2N+1`-padded word),
  `contentInput?` (the **existing** strict parser re-run on the window of the
  *content-computed* length `M n'`; the parser re-decodes its own header from that
  narrower window and gates on `m = M n_dec`. The later
  `ContentPrefixExtensionGateClosure.lean` proves that this convention-length gate compares
  `M n'` with itself and never rejects after a successful header decode), `contentWitness`,
  `ContentAccepts`, the
  language `ContentPrefixExtensionLanguage` (`L'`), and the NP-witness interface
  `ContentPrefixExtensionNPWitness`. Definitions plus the `accepts_iff` unwrapping;
  the interface is a **hypothesis**.
- `ContentVirtualZeroTailReaderCore.lean` — Part A G0-B2a. It implements
  strict bit, big-endian, slice, all-zero, gamma, header, and complete
  tree-prefix parser operations over a physical source with a separate logical
  length. Positions inside the logical extent but beyond physical support read
  as false; positions beyond the logical extent fail. Whole-result equalities
  identify every operation with the frozen counterpart on `padWord z T`,
  including all failure branches. The named loop bounds record only structural
  widths or gamma fuel; they are not a `UniformTM`, gate, or runtime analysis.
- `ContentFixedGammaPayloadZeroSemanticBridge.lean` — Part A G2g
  infrastructure. Under exact logical fit it characterizes a successful
  virtual-reader all-zero scan by false `padRead`s. With explicit physical fit
  it identifies the full physically false gamma payload on the exact window
  `[9 + zeros, 9 + 2 * zeros)` with that scan, then conjoins the existing G2f
  cleanup endpoint and the scan at logical length `a + m`. This is only a
  one-way consequence of the validated trace hypotheses: it proves no
  `qDone` iff, semantic acceptance, dispatcher correctness, or complete parser
  behavior.
- `ContentFixedGammaPayloadPendingSemanticBridge.lean` — Part A G2j
  infrastructure. It characterizes strict positive-width logical failure and,
  under fit, a false scan by the existence of a true `padRead`, without
  classical witness selection. It pairs the cleaned physical-true and
  first-virtual endpoints one-way with their scans on the exact payload window
  `[9 + zeros, 9 + 2 * zeros)`, records exact virtual failure at physical
  length, and specializes both plus the zero-cleanup case to
  `2 * (a + m) + 1`. It proves no endpoint iff, dispatch, parser acceptance,
  payload decode, or cross-machine clock.
- `ContentCappedArithmetic.lean` — Part A G0-B2b1. It provides exact capped
  natural addition, multiplication, binary-length, and exponentiation. Every
  `some` theorem identifies the exact mathematical result and proves it fits;
  every `none` theorem is strict overflow. `checkedPow` has one recursive call
  at exponent `e / 2`, with separate zero-exponent and zero-base branches. This
  records source recursion only: no bigint operation cost, `UniformTM`, gate,
  runtime, semantic-verifier, or bridge theorem is claimed.
- `ContentCappedSizes.lean` — Part A G0-B2b2. It composes capped arithmetic into
  exact concrete threshold, table, witness, gamma, index, partial-endpoint, and
  final convention-length fields. `computeContentSizesCapped` returns `some s`
  exactly when `s` is the canonical record and `s.M ≤ B`, and returns `none`
  exactly when authoritative `treeMCSPPrefixM` strictly exceeds `B`. Successful
  outputs retain table/witness bounds. This is size arithmetic only: no content
  parser, semantic verifier, `UniformTM`, runtime, or bridge theorem is claimed.
- `BoundedContentSemanticVerifier.lean` — Part A G0-B2c. It combines the merged
  exact capped sizes with the virtual-zero-tail parser. The closed public parser
  derives its cap only from the physical input length, invokes strict parsing at
  the computed logical `sizes.M`, and is exactly the authoritative parser
  filtered by the target cap. Unconditional parser equality is intentionally
  not claimed. The copied source-level Boolean checker is proved equal to
  authoritative `contentSemanticAccepts`, using the accepting-window theorem to
  exclude overflow on true branches. This is executable semantic glue, not a
  fixed `UniformTM`, tape program, runtime theorem, or `ContentVerifierBridge`.
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
  part-2 module below proves the target bound. This recovery module itself gives no satisfiability
  theorem for `ContentAccepts` and constructs no verifier TM, runtime bound or `TM.accepts` bridge;
  GATE-0 separately proves concrete non-vacuity below.
- `ContentTargetSizeBound.lean` — FEAS-0 slice, part 2 and outcome (a). It computes the concrete
  all-blank witness decode at zero and positive parsed targets, uses the input-zero projection to
  force a supported truth-table cell and `tableLen r ≤ N`, and proves
  `contentAccepts_target_poly_treePoly`. The proof works at `r := pr.2.n`, transports only through
  `treeMCSPPrefixM codec n_header = treeMCSPPrefixM codec r`, and uses the existing
  `PolyBoundedInTable` / `powAdd` chain; it has no I1 dependency and never infers
  `r = n_header`. This freezes the content target, but remains Infrastructure: no verifier TM,
  runtime theorem, NP-membership proof, or lower-bound obligation is discharged (non-vacuity is the
  separate GATE-0 module below).
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
  `treeMCSPPrefixM codec input.n = treeMCSPPrefixM codec n`; the base theorem therefore retains
  the honest second hypothesis. The proposition-level theorem is the direct specification
  coincidence and does not route through either classical Boolean language wrapper. The I1 module
  below derives an `hn`-free corollary under the exact monotone-witness-width condition.
- `ContentPrefixExtensionNonVacuity.lean` — GATE-0 (plan §4.1): `ContentAccepts` is
  **unconditionally satisfiable**. A private helper stores a full search witness in a certificate's
  leading `witnessBits` block and proves that the content witness window reads it back; prefix
  agreement is vacuous at `i = 0`. The generic theorem
  `contentAccepts_zeroPrefixQuery_of_predicate` then turns a satisfied tree-MCSP promise at `n` into
  an accepted word: `zeroPrefixQueryValue_parses` supplies both `hparse` and `hn : input.n = n` for
  `contentInput?_concat_of_parse` (the parsed object is the canonical `toPrefixInput`, so no
  injectivity of `treeMCSPPrefixM codec` and no gamma canonicity is used), and the relation conjunct
  is `TreeCircuitWitnessCodec.complete`. `contentPrefixExtensionLanguage_zeroPrefixQuery` is the
  language form — the first unconditional `L'`-membership statement here. The concrete discharge
  `contentAccepts_nonvacuous_treePoly` takes the all-false table with `Circuit.const false` (size
  `1`) against `1 ≤ thresholdPoly k n = n ^ k + k`, so `L'` is **not** the empty language at
  `treeCircuitWitnessCodec (thresholdPoly k)` and `ContentPrefixExtensionTransfer.lean`'s
  `NoPolynomialBoundedSearchSolver` hypothesis is not refuted by vacuity. Scope is satisfiability
  only: no verifier TM, runtime bound, `TM.accepts` bridge, `ContentPrefixExtensionNPWitness`
  instance, or NP-membership follows. The separate I1 gate-closure module below proves that the
  convention-length re-decode gate cannot fire after any successful content-header decode; the
  tag, decoded-index, and inactive-padding checks remain genuine rejection points.
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
- `ContentVerifierTapeInterface.lean` — D1a's P0-independent machine-facing surface from
  `VERIFIER_RETARGET_PLAN.md` §4.4. `initialConfig_tape_eq_padRead` identifies every allocated
  start-tape cell with the blank-padded complete concatenated word, including the blank tail;
  `contentAccepts_of_initialConfig_tape_eq` restates the existing blank-padded-read invariance for
  machine consumers; and `ContentVerifierBridgeFor acc` names the verifier obligation for an
  arbitrary acceptance predicate. Its `accepts_eq` field uses the existing exact-step
  `TM.accepts` semantics at the explicit concatenated length `n + certificateLength n 1`: there is
  no halting or within-time variant. This module supplies no specialized alias, witness packaging,
  or bridge instance. The `runTime_poly` inequality bounds runtime numerically but does not
  formally prevent `runTime` from carrying input-length advice; advice avoidance remains a
  documented, unenforced construction obligation.
- `ContentSemanticVerifier.lean` — P0's plain computable `Bool` counterpart of
  `ContentAccepts`. `contentSemanticAccepts` content-parses one complete word, reads its total
  content witness window, and combines `prefixAgreesBool` with `verifiesBool`. The unconditional
  headline `contentSemanticAccepts_eq_true_iff` identifies `= true` with `ContentAccepts`;
  `contentSemanticAccepts_eq_false_of_contentInput_none` rejects parse failures;
  `contentSemanticAccepts_padWord_of_le` inherits complete-word padding stability; and
  `contentSemanticAccepts_correct` gives the existential certificate characterization of `L'`.
  This is semantic Infrastructure only: it constructs no TM or runtime bound, does not itself prove
  non-vacuity or NP membership, and reduces no lower-bound source obligation. GATE-0 separately
  supplies concrete non-vacuity. The four theorems
  stay within `[propext, Classical.choice, Quot.sound]` or a subset, and the surface tests include
  a concrete evaluation to guard computability.
- `TreeCircuitContentWitnessRelation.lean` — Part A P2-4a's exact-length V1 relation boundary.
  It defines separate content and tree-prefix relations and maps every witness length other than
  `certificateLength n 1` to literal `false`. The content relation calls a computable query-first
  concatenator; a proposition-level extensional theorem relates that view to the pre-existing
  noncomputable `concatBitstring`, so the executable relation definition does not call that
  concatenator. Axiom roots may still report `Classical.choice`: both generic relations inherit it
  from the imported `verifiesBool` checker (`decide (codec.verifies …)`), threshold instances
  additionally through `treeCircuitWitnessCodec`, and compatibility theorems through
  `concatBitstring`. This module proves only conversion and guard reductions: it constructs no
  `UniformTM`, proves no `VerifiesRelation` or content/tree pointwise equality, supplies no
  `ContentVerifierBridge`, and reduces no lower-bound obligation.
- `ThresholdTaggedContentFraming.lean` — Part A framing ABI. It names the
  canonical V1 `encodePair` word and total raw-word language for the threshold
  content relation. Canonical tagged inputs reduce exactly to authoritative
  `contentSemanticAccepts` on headerless `concatBitstring`, while malformed pair
  words reduce to `false`. These are semantic equations only: no tape compaction,
  `UniformTM`, legacy Boolean-tape simulation, or runtime theorem is supplied.
- `TreeMCSPPrefixExplicitCap.lean` — Part A G0-B1. It expands the concrete
  `thresholdPoly` witness width and prefix convention into transparent exponents,
  with `e = treeMCSPPrefixTableExponent k = max 10 (k + 6) + 2`,
  `treeMCSPPrefixPowAddExponent k = 2 * e + 2 ^ e`, and
  `contentCapExponent k = treeMCSPPrefixPowAddExponent k + 1`. It proves
  choice-free bounds for the actual dependent target returned by a successful
  `contentInput?`. These are size bounds under semantic acceptance; this module
  constructs no bounded semantic evaluator, `UniformTM`, verifier theorem,
  bridge, or complexity conclusion.
- `ContentPrefixExtensionGateClosure.lean` — I1 (`VERIFIER_RETARGET_PLAN.md` §4.3). It proves
  `treeMCSPPrefixM_strictMono` / `treeMCSPPrefixM_injective_of_monotone`, verifies the premise for
  `treeCircuitWitnessCodec (thresholdPoly k)`, and supplies
  `ContentPrefixExtendable_iff_of_parse'` without an explicit `hn`. No generic-codec injectivity is
  asserted, and none is refuted either: `witnessBits` is unconstrained, so a definition-level codec
  construction can pad it upward at a single point until two adjacent convention lengths collide
  (with widths `3` at `0` and `1` at `1`, both `M` values are `15`), but that is a review of the
  definitions — no counterexample codec is constructed and no formal refutation is claimed. It also
  proves the `readNatBE` power bound and hypothesis-free gamma canonicity, narrows the header via
  the consumed-based transfer correction, proves unconditional convention-length-gate vacuity, and
  characterizes `contentInput?` success by exactly three conjuncts: the tag value, the decoded-index
  bound, and the inactive-pad-zero test. Each conjunct is a *successful read with a value*, so
  read-success for those three fields is bundled into them; what discharges unconditionally is the
  length gate and the three range-only slice obligations. The proof implementation was rebased at
  `19d7c4b3` (497 LOC); the current module is 505 LOC after documentation corrections. Every entry
  carries the standard `[propext, Classical.choice, Quot.sound]` triple except
  `readNatBE_lt_two_pow`, which is `[propext, Quot.sound]`. These are parser/specification facts
  only: padding invariance of the language wrapper, the verifier TM/runtime/`TM.accepts` bridge,
  and advice-channel enforcement all remain open. Content non-vacuity is discharged separately by
  the GATE-0 module above. Infrastructure
  only; no lower-bound obligation or `P ≠ NP` claim.
- `ContentVerifierBridgeWitness.lean` — D1b from `VERIFIER_RETARGET_PLAN.md` §4.5, the only
  P0-dependent half of the bridge work. `ContentVerifierBridge codec` is D1a's
  `ContentVerifierBridgeFor` at `acc := contentSemanticAccepts codec`, and
  `contentPrefixExtensionNPWitness_of_bridge` repackages any such bridge into
  `ContentPrefixExtensionNPWitness`: the machine, exponent and `runTime_poly` are taken over
  verbatim, and `correct` is P0's `contentSemanticAccepts_correct` composed with the bridge's
  `accepts_eq` rewrite under the certificate existential. The abbreviation merely names that bridge
  type; the repackaging definition is **conditional on a supplied bridge**. No bridge instance,
  machine, or runtime bound is constructed here — so this module proves no NP membership for `L'`
  and no advice-free claim: the inherited
  `runTime_poly` still bounds only the clock's magnitude. The repackaging has the standard
  `[propext, Classical.choice, Quot.sound]` axiom footprint.
- `ContentPrefixExtensionPaddingTransport.lean` — the explicitly classical conditional transport
  theorem `ContentAccepts_padWord_of_prefixExtendable`, isolated from the axiom-light padding
  module. It derives `ContentPrefixExtendable` directly from
  `ContentPrefixExtendable_iff_of_parse`, without either Boolean language wrapper. Its statement
  necessarily inherits `Classical.choice` from the pre-existing noncomputable `concatBitstring`.
  It is a **conditional existential**, available only under `hparse`, `hn`, `hext`, and `hT`, so it
  is not the unconditional non-vacuity result; that result is the separate GATE-0 module.
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
- **The re-decode length gate is vacuous, but three read-value tests remain.** I1 proves that a
  successful content header narrows with the same decoded target and consumed width, so the
  parser's `m = M n_dec` comparison is reflexive. It does not prove unconditional parser success:
  a wrong tag, an index exceeding the witness width, or a nonzero inactive suffix is still rejected,
  exactly as characterized by `contentInput?_isSome_iff_of_header`.
- **Non-vacuity is settled; it is not a complexity statement.** `ContentAccepts` *is*
  unconditionally satisfiable, and `L'` is non-empty, by
  `ContentPrefixExtensionNonVacuity.lean` (`contentAccepts_nonvacuous_treePoly` at the
  concrete `treeCircuitWitnessCodec (thresholdPoly k)`). That fixes only which words are
  accepted; it gives no bound on the cost of deciding acceptance, and every "no verifier"
  item below stands unchanged. The older existential
  `ContentAccepts_padWord_of_prefixExtendable` remains a *conditional* one, available only
  under the four explicit hypotheses of its statement — `hparse`, `hn`, `hext`, none
  discharged anywhere, plus the padding bound `hT`, which only fixes the target length —
  and is not what discharges non-vacuity.
- **No padding invariance of the language `L'`.** The padding lemmas are generic
  statements about `padRead` / `padWord`, the strict readers and the gamma decoder,
  topped by invariance of `ContentAccepts` on complete words; the wrapper quantifies
  over certificates whose length and concatenation offset both move with the physical
  length, so wrapper-level invariance is unproved (scope paragraph above).
- **No machine verifier.** The Boolean semantic checker in `ContentSemanticVerifier.lean` is not a
  Turing-machine construction. `ConcreteTreeDirectTagProgram.lean` now constructs only a
  five-step finite-control **single-tag reader**; it is not a decoder loop or circuit evaluator.
  No complete verifier Turing machine, full-evaluation runtime bound, or
  `TM.accepts … = ContentAccepts …` bridge for `L'` is constructed anywhere. Note the
  interface's `runTime_poly` field bounds `M.runTime` at the length-dependent point
  `n + certificateLength n 1`, so the CT route does not remove length-dependence from
  the machine side either.
  Whether a polynomial-time verifier for `L'` exists is open, and
  `ContentPrefixExtensionNPWitness` remains an unproved interface.
- **No separation.** Both open inputs stay explicit arguments of every source in
  `ContentConsolidatedSource.lean`; no `P ≠ NP` claim follows.

Every public theorem of the thirteen modules has its own `#print axioms` line in
`Pnp4/Tests/AxiomsAudit.lean` and its own `#check` in
`Pnp4/Tests/AlgorithmsToLowerBoundsSurfaceTests.lean`
(`ContentPrefixExtensionSurface`).

**Plan of record for input (2).** `VERIFIER_RETARGET_PLAN.md` (this directory) freezes the
NP-verifier target at `ContentPrefixExtensionNPWitness` / `ContentAccepts`. FEAS-0 outcome (a) is
now proved by `ContentTargetSizeBound.lean`: accepted complete words have polynomially bounded
header convention length. The length-gated `PrefixExtensionNPWitness` remains compiled and audited
for compatibility and is dispreferred, rather than retired, for new verifier work; a new slice may
target it only with an explicit technical or compatibility rationale. GATE-0 (§4.1) is likewise
discharged by `ContentPrefixExtensionNonVacuity.lean`, so D-track machine work is no longer aimed at
a predicate of unknown satisfiability. Neither result proves polynomial-time verifiability of `L'`:
the concrete TM, runtime theorem, and `TM.accepts` bridge remain open. This is Infrastructure and
makes no `P ≠ NP` claim.

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

### CVB-ARCH-1 direct-evaluator experiment · **verdict BLOCK**
- `ConcreteTreeDirectEvaluator.lean` — a correct functional evaluator with explicit task/value
  stacks, rejection lemmas for malformed tags, truncated constant payloads, threshold overflow,
  and all three reduction underflows. `decodeCircuitTreeAtDepth_consumed_ge` proves the missing
  decoder-side size bound for arbitrary successful parses, and
  `decodeCircuitFull_directEvalCost_le_length` consequently bounds the functional evaluator's
  logical iterations by serialized length. This is **not** a TM runtime theorem: the Lean decoder
  remains recursive and evaluator tasks contain whole `Circuit` subtrees.
- `ConcreteTreeDirectTagProgram.lean` — a five-step finite-control tag microprogram. Its tag
  classifier is defined from the authoritative decoder and is bridged to successful real decoder
  roots. Four steps classify and return home on an arbitrary offset, including a theorem for the
  actual `initialConfig` input tape; the fifth reaches a redesigned, reachable accept state exactly
  for a valid tag. It does not iterate, serialize either stack, or evaluate a circuit.
- **Why BLOCK, not DIRECT.** There is no TM representation invariant for the parser/control/value
  stacks, no bound on the occupied serialized stack region, no transition program implementing a
  decoder/evaluator iteration, and therefore no premise-free `runConfig` theorem for complete
  witness evaluation. The former quadratic `directMicrostepBound` expression was removed because
  no theorem connected it to such a run. These modules are reusable Infrastructure only; they do
  not construct `ContentVerifierBridge` or reduce a mainline lower-bound source obligation.

### Conditional-accept terminal infrastructure
- `ConstStatePhasedProgramAccepts.lean` keeps phase arrival and full TM acceptance separate:
  `RunSpec.final_state_eq_accept_iff` reduces accepting-state equality to the remaining local-state
  equality, and `RunSpec.accepts_eq_decide_local` specializes that fact to an actual
  `initialConfig` run at the machine's exact clock.
- `ConstStatePhasedProgramConditionalAccept.lean` supplies the fixed
  `acceptIfCellCS Δflag : ConstStatePhasedProgram (Bool × Bool)`. Both flag values run for exactly
  `2 * Δflag + 3` steps, return the head, and preserve the tape. A true flag ends in the complete
  accepting state; a false flag ends in a distinct nonaccepting terminal sink. Its full-run theorem
  currently requires the start phase, the complete start local state, and the head bound needed to
  rule out clamped motion. The local-state premise is inherited from the current combiner proof;
  because the two reads overwrite both local-state bits, the final semantics is independent of that
  initial local state. The end-to-end theorem is stated for the real `initialConfig`; offsets beyond
  the input read the blank `false` cell.
- This terminal program must be the explicit right operand of the final `seq`. It must not be routed
  through `seqList`, because that fold appends `idleCS` and its boundary resets the local state.
  `ConstStatePhasedProgramInitialConfig.lean` now proves the unconditional full-configuration
  equality `initialConfig (seq P₁ P₂) x = embedSeqConfig P₁ P₂ (initialConfig P₁ x)`.
- `ConstStatePhasedProgramConditionalAcceptExamples.lean` exercises that bridge with
  `seq (gateConstCS b d) (acceptIfCellCS d)`. The operands have equal standalone clocks, so no
  padding is involved. Its actual-input `RunSpec` fixes the exact final local state, head, and full
  tape, and the headline theorem proves `TM.accepts ... = b`, including the rejecting branch.
- Generic padding and uniform clock discipline remain open. No arbitrary clock function, padding
  constructor, content verifier, or advice-free theorem is introduced by this capstone.

This closes reusable conditional-accept plumbing and its focused constant-gate capstone only. It
constructs no content verifier, runtime bound for that verifier, or `ContentVerifierBridge`, and is
therefore Infrastructure rather than P-vs-NP mainline progress.

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
   whose language carries no *explicit* gate on the ambient physical length. The
   strict parser's own equality gate survives inside `contentInput?`, applied to the
   computed window, but I1 proves it unconditionally reflexive after a successful header decode;
   exactly the tag, decoded-index, and inactive-padding read-value tests remain. On the
   specification side that difference
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

The Part A fixed-phase chain, including the G2x composed decrement/countdown machine, lives
in a different model: the versioned `Pnp3.Complexity.Uniform.V1.UniformTM`, with
`Option Bool` cells, no runtime field, and tapes laid out against the pair length
`pairLength a m`.  No theorem transfers a V1 execution into this `TM`, no V1 statement of an
advice-free verifier for `contentSemanticAccepts` is frozen, and the unrestricted `runTime`
field described in `VERIFIER_RETARGET_PLAN.md` caveat 6 is untouched by that chain; a future
transfer would have to supply an explicit arithmetic `runTime` by convention.

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

`FixedContentGammaTerminatorCorrect.lean` is the Part A G1 activation bridge.
Under a successful `FixedContentTagGate` handoff, it proves that the real
three-state scan accepts exactly when `contentHeader?` is present and rejects
exactly when it is absent. Independently of machine execution, header absence
forces both content semantic verifiers to reject. The operational phase stops
on the terminator. It neither reads the gamma payload nor provides a machine
implementation of `ContentCappedSizes`.

`ContentFixedGammaPayloadDispatcherSemanticBridge.lean` is the Part A G2n
infrastructure bridge registered after that terminator-correctness dependency.
On matching tags it turns the fixed dispatcher's common deadline classification
into total `qAllZero`/`qHasOne` existential iff statements for the exact payload
scan at logical length `2 * (a + m) + 1`, including width zero, and identifies
`qReject` with gamma failure (optionally conjoined with header absence). The
physical/padded truth helper and window fit are constructive, with fit derived
from `gamma_contract`. It claims no decoded value, payload `readNatBE`,
acceptance, parser correctness, untagged behavior, uniform head, cross-machine
clock, or P-vs-NP mainline progress.

`ContentFixedGammaPayloadDispatcherHeaderValueBridge.lean` is the Part A G2o
infrastructure bridge, registered immediately after G2n and importing only it.
It has exactly seven public theorems:

* `VirtualZeroTailReader.readNatBE_eq_some_zero_iff_allZeroSlice?_eq_some_true`
  and `VirtualZeroTailReader.allZeroSlice?_eq_some_false_iff_readNatBE_pos`,
  iffs with no hypothesis (width zero and non-fitting windows included);
* `contentHeader?_eq_some_iff_gammaZeros_payload`, an iff with no hypothesis
  and no subtraction: the header is `(n, consumed)` exactly when, for some
  `zeros` and `payload`, the physical scan gives `gammaZeros? z = some zeros`,
  the payload read at logical length `2 * N + 1` over
  `[9 + zeros, 9 + 2 * zeros)` is `some payload`,
  `n + 1 = 2 ^ zeros + payload`, and `consumed = 2 * zeros + 1`;
* `contentInput?_target_eq_contentHeader`, one-way from the single premise
  `contentInput? codec z = some pr` for any codec (no monotonicity or
  injectivity): for some `consumed`, `contentHeader? z = some (pr.1, consumed)`
  and `pr.2.n = pr.1`, so the Sigma index and the parsed `PrefixInput` target
  that `ContentAccepts` reads both equal the header target;
* `dispatcher_qReject_iff_contentHeader_none`,
  `dispatcher_qAllZero_iff_contentHeader_succ_eq_two_pow`, and
  `dispatcher_qHasOne_iff_contentHeader_two_pow_lt_succ`, iffs at the common
  deadline whose single premise is a matching tag: header absence, a header
  `(n, 2 * zeros + 1)` with `n + 1 = 2 ^ zeros`, and such a header with
  `2 ^ zeros < n + 1`.

Width zero, positive physical payloads, and virtual payload cells are covered
without a physical-fit premise. The gamma width and payload natural are never
identified with the header target; the parsed target `pr.2.n` equals the header
target only through a successful `contentInput?`. The module does not claim
that the dispatcher stores or materializes `n` or the payload, that any machine
executes the parser, that an endpoint is acceptance of the content language, or
any untagged-input, uniform-head, clock-composition, `ContentVerifierBridge`,
advice-freedom, NP-membership, or P-vs-NP mainline result. Surface regressions
cover malformed gamma, width zero, physical zero and one, a wholly virtual zero
payload, and a physical one followed by a virtual zero; the `contentInput?`
theorem is instantiated on every canonical zero-prefix query.

`ContentFixedGammaTerminatorScratchBootstrapBridge.lean` is the Part A G2p-a
infrastructure bridge. It is registered immediately after G2o and imports G2o
and the pnp3 `FixedGammaTerminatorScratchBootstrap` machine. It has exactly
two public theorems, both at the bootstrap's length-only deadline
`2 * (a + m)`:

* `scratchBootstrap_qReject_iff_contentHeader_none`: under a matching tag,
  `qReject` holds exactly when `contentHeader? = none`;
* `scratchBootstrap_scratch_eq_leading_bit`: under a matching tag and
  `contentHeader? z = some (n, consumed)`, some `zeros` has
  `consumed = 2 * zeros + 1` and `2 ^ zeros ≤ n + 1 < 2 ^ (zeros + 1)`, the
  endpoint is `qTerm` at head `8 + zeros` with the scratch tape, and scratch
  cell `a + m + 1` holds `(n + 1).testBit zeros`.

The digit bound comes from `readNatBE_lt_two_pow` on the padded payload read.
Only the leading digit is placed on the tape. The shuttle crosses the gamma
payload cells, but neither decodes nor copies their digits, and the module
claims no parser execution, content acceptance, untagged behavior, uniform
head, clock composition, or P-vs-NP
mainline result. Surface regressions derive rejection on the malformed G2o word
and, on the word with header `(5, 5)`, head `10` with `true` at scratch cell
`13`.

`ContentFixedGammaTargetFirstPayloadBridge.lean` is the Part A G2p-b
infrastructure bridge. It is registered immediately after G2p-a and imports
G2p-a and the pnp3 `FixedGammaTargetFirstPayload` machine. It has exactly two
public theorems, both one-way, at the machine's length-only deadline
`3 * (a + m)`:

* `firstPayload_positive_register`: under a matching tag,
  `contentHeader? z = some (n, consumed)`, `0 < n`, and
  `a + m + 2 < tapeLength (pairLength a m) B`, some `zeros > 0` has
  `consumed = 2 * zeros + 1` and `2 ^ zeros ≤ n + 1 < 2 ^ (zeros + 1)`. The
  endpoint is `qDone` at head `7` on `firstPayloadTape` with bit
  `(n + 1).testBit (zeros - 1)`. Cells `a + m + 1` and `a + m + 2` hold
  `(n + 1).testBit zeros` and `(n + 1).testBit (zeros - 1)`;
* `firstPayload_zero_width_register`: under a matching tag and the header
  `(0, 1)`, the endpoint is `qDone` at head `7` on the bootstrap scratch tape.
  Cell `a + m + 1` holds `(0 + 1).testBit 0`, and every later cell is blank.

The second digit is the first cell of the header decoder's own payload read
(G2o factorization), including its virtual zero tail. It is matched to the
machine's carried bit `(physicalSymbol z (9 + zeros)).getD false`. The room
premise is a capacity assumption that the header does not imply (it fails at
`a = B = 0`, where the target cell `a + m + 2` is off the tape), so unlike G2p-a
this bridge states no `qReject ↔ contentHeader? = none` equivalence: such an
equivalence would need the same room premise. The two header hypotheses are
nevertheless jointly exhaustive — the positive one only under that premise —
since in the G2o factorization `n + 1 = 2 ^ zeros + payload` with
`payload < 2 ^ zeros`, `n = 0` forces `zeros = 0` and `consumed = 1`. The module
stores no further digit and claims no parser execution, content acceptance,
untagged behavior, clock composition, `ContentVerifierBridge`, or P-vs-NP
mainline result. Surface regressions derive `qDone` for header `(0, 1)`, `10₂`
at cells `12, 13` for header `(3, 5)` (virtual second digit), and `11₂` at cells
`13, 14` for header `(5, 5)` (physical second digit).

`ContentFixedGammaTargetSecondPayloadBridge.lean` is the Part A G2p-c
infrastructure bridge. It is registered immediately after G2p-b and imports
G2p-b and the pnp3 `FixedGammaTargetSecondPayload` machine. It has exactly four
public theorems, all one-way out of a decoded header; only the last three
mention the machine, at its length-only deadline `2 * (a + m)`:

* `header_digits` (one hypothesis; generic, no machine and no tag): from
  `contentHeader? z = some (n, consumed)` for `z : PrefixBitVec N`, some `zeros`
  has `gammaZeros? z = some zeros`, `consumed = 2 * zeros + 1`,
  `2 ^ zeros ≤ n + 1 < 2 ^ (zeros + 1)`, `(n + 1).testBit zeros = true`, and for
  every `t < zeros` the payload cell reads
  `(physicalSymbol z (9 + zeros + t)).getD false = (n + 1).testBit (zeros - 1 - t)`;
* `secondPayload_positive_register` (four hypotheses: matching tag, decoded
  header, `3 ≤ n`, and `a + m + 3 < tapeLength (pairLength a m) B`): some
  `zeros ≥ 2` has `consumed = 2 * zeros + 1` and
  `2 ^ zeros ≤ n + 1 < 2 ^ (zeros + 1)`, the endpoint is `qDone` at head `7` on
  `secondPayloadTape` with digits `(n + 1).testBit (zeros - 1)` and
  `(n + 1).testBit (zeros - 2)`, and cells `a + m + 1`, `a + m + 2`,
  `a + m + 3` hold `(n + 1).testBit zeros`, `(n + 1).testBit (zeros - 1)`,
  `(n + 1).testBit (zeros - 2)`;
* `secondPayload_width_one_register` (three hypotheses: matching tag,
  `contentHeader? = some (n, 3)`, and the G2p-b room `a + m + 2 < tapeLength
  (pairLength a m) B`): the endpoint is `qDone` at head `7` on the two-digit
  `firstPayloadTape`, cells `a + m + 1` and `a + m + 2` hold
  `(n + 1).testBit 1` and `(n + 1).testBit 0`, and every allocated cell past
  `a + m + 2` is blank — no third digit is written;
* `secondPayload_zero_width_register` (two hypotheses: matching tag and the
  header `(0, 1)`): the endpoint is `qDone` at head `7` on the bootstrap scratch
  tape with the one digit `(0 + 1).testBit 0` at `a + m + 1`, blank afterwards,
  with no room premise.

Every payload digit comes from the header decoder's *own* read, virtual zero
tail included, which is why `header_digits` is about `Option.getD false` of the
physical symbol rather than about a physical cell, and why its `t < zeros` guard
matters: outside the payload block the truncated index `zeros - 1 - t` would
repeat digit `0` at an address that has already left the block. The generic
digit induction is `readNatBE_digit` (private). Given a decoded header, `3 ≤ n`
is exactly `2 ≤ zeros`, because the exported bounds make `zeros` the index of
the leading digit of `n + 1`; the bridge still states the implication one way
only. The three concrete header hypotheses are jointly exhaustive over decoded
headers, since `header_digits` splits them by width: `zeros = 0` forces the
header `(0, 1)`, `zeros = 1` forces `consumed = 3`, and `2 ≤ zeros` forces
`3 ≤ n` — the width-one branch only under the G2p-b room, the positive branch
only under the wider one. Room is a capacity assumption the header does not
imply — `FixedGammaTargetSecondPayload.room_iff` reads it as `2 ≤ a + B`, a
condition on the `x` side and the budget that a decoded header does not
constrain — so it is carried explicitly. This bridge states no `qReject`
theorem, and not because room blocks one: on a matching tag,
`contentHeader? = none → qReject` at this deadline is room-free from the
imports, by `fixedGamma_header_contract` together with
`FixedGammaTargetSecondPayload.malformed_at_deadline`, which takes no room
premise. Room is what the opposite direction needs, and hence what the
`qReject ↔ contentHeader? = none` equivalence of G2p-a would need here, since
excluding `qReject` on a decoded header of width one or more goes through the
endpoint theorems. `deadline` and `exactClock` are **phase-local**:
`startConfig` retags the actual G2p-b endpoint configuration and embeds the
earlier phases' steps, which neither clock accounts for, so nothing here is a
runtime or a clock for the composed pipeline. The module asserts no converse
(nothing derives a header, a width, or `2 ≤ zeros` from `qDone`, the tape, or a
digit at `a + m + 3`) and claims no parser execution, `contentInput?`,
`ContentAccepts`, language acceptance, clock composition, the remaining
`zeros - 2` digits, the decrement to `n`, `ContentVerifierBridge`, or P-vs-NP
mainline result. Surface regressions derive, for every budget, the one-digit
register for header `(0, 1)` (digit at cell `10`, with cell `11` and every
later allocated cell blank); `11₂` at cells `12, 13` with cell `14` still blank
for header `(2, 3)`; `100₂` at cells `12, 13, 14` for header `(3, 5)`; `110₂` at
cells `13, 14, 15` for header `(5, 5)`, whose second payload digit is the
virtual zero at the boundary; and `111₂` at cells `14, 15, 16` for header
`(6, 5)`, whose second payload digit is physical.

`ContentFixedGammaTargetPayloadExhaustionBridge.lean` is the Part A G2p-g
infrastructure bridge, the pnp4 companion the pnp3 G2p-f slice deferred. It is
registered immediately after G2p-c and imports G2p-c together with the pnp3
`FixedGammaTargetPayloadExhaustion`. It adds no machine: the run is G2p-f's
`payload_exhausted`, unchanged, and everything here is a statement about what
that endpoint's cells are. Five public theorems, all one-way out of a decoded
header or a successful parse; the first three mention no machine, no tag and no
clock, and only `room_iff_target_bound` mentions the budget `B`, through the
tape length:

* `exhaustion_register_digits` (one propositional hypothesis, a decoded header
  `contentHeader? (Fin.append x w) = some (n, consumed)`): some `zeros` has
  `gammaZeros? (Fin.append x w) = some zeros`, `consumed = 2 * zeros + 1`,
  `2 ^ zeros ≤ n + 1 < 2 ^ (zeros + 1)`, the **register equation**
  `FixedGammaTargetPayloadLoopFoundation.registerBit x w zeros j =
  (n + 1).testBit (zeros - j)` at every `j ≤ zeros`, the completeness fact
  `∀ b, zeros < b → (n + 1).testBit b = false`, and the **virtual-tail**
  conjunct: for every `j` with `1 ≤ j ≤ zeros` and `a + m ≤ 8 + zeros + j`, both
  `registerBit x w zeros j` and `(n + 1).testBit (zeros - j)` are `false`;
* `register_determines_target` (four hypotheses: a decoded header, a decoded
  width, the register digits of a `v`, and that `v` has no bit above `zeros`):
  `v = n + 1`;
* `room_iff_target_bound` (two hypotheses: a decoded header and a decoded
  width): `n + 1 < 2 ^ (a + B + 1) ↔ zeros ≤ a + B`, and
  `zeros ≤ a + B ↔ a + m + 1 + zeros < tapeLength (pairLength a m) B`;
* `exhausted_register_header_value` (four hypotheses: matching tag, decoded
  header, `3 ≤ n`, and `n + 1 < 2 ^ (a + B + 1)`): some `zeros ≥ 2` has
  `consumed = 2 * zeros + 1`, the bit-length bounds, the room in its tape form,
  and, at `FixedGammaTargetPayloadRound.machine.run
  (FixedGammaTargetPayloadExhaustion.totalClock (a + m) zeros)
  (FixedGammaTargetPayloadRound.startConfig B x w)`: `qDone` at head `7`, the
  tape `finishTape B x w zeros`, `d.tape i = some ((n + 1).testBit (zeros - j))`
  at every `i.val = a + m + 1 + j` with `j ≤ zeros`, the virtual-tail cells
  `some false` together with the matching parsed `false`, the completeness fact,
  the uniqueness of `n + 1` among values read off those cells with no bit above
  `zeros`, the restoration of `[7, 8 + zeros)` to
  `FixedPairContentMarkerErase.contentTape`, and persistence at every later time;
* `exhausted_register_parsed_target` (four hypotheses: matching tag, a
  successful `contentInput? codec (Fin.append x w) = some pr` for an arbitrary
  codec, `3 ≤ pr.2.n`, and `pr.2.n + 1 < 2 ^ (a + B + 1)`): `pr.2.n = pr.1`,
  `contentHeader? (Fin.append x w) = some (pr.2.n, 2 * zeros + 1)`, and the same
  endpoint conjuncts restated in `pr.2.n` — every one of the header form except
  the gamma zero field restoration, which is about the tape and not the target.

The virtual-tail conjunct is the point of the slice. G2p-f exports the register
cells as `registerBit`, which is *content*: on a truncated payload its digits
past the physical word are a `false` that no theorem there ties to any value.
`registerBit` pads there because the payload cell is not in the word — on
`contentTape` that cell is blank — while `contentHeader?` pads through
`VirtualZeroTailReader`. Those are two different paddings, and
`exhaustion_register_digits` is where they are proved to agree, so a virtual
`false` in a truncated register is the parsed target's own digit. Three numbers
stay apart: `pr.2.n`, the actual parsed target that `ContentAccepts` feeds to
the search relation, the value a decoded `contentHeader?` and the parser after it
*return* once the gamma convention has been applied, not a value the header
stores; `n + 1`, the encoded gamma integer that convention writes, whose bits
physically occur in the header and whose digits the register holds, the decrement
to `n` being performed by no machine here and not claimed; and
`consumed = 2 * zeros + 1`, a cell count that is never in the register. The parser's other length convention `treeMCSPPrefixM codec pr.1`
occurs only in the type of `pr`. Room is carried, not derived: a decoded header
does not imply it, since `room_iff_target_bound` reads it as `zeros ≤ a + B`, a
condition on the `x` side and the budget, and it is sufficient only — there is
still no footprint theorem on the pnp3 side. Given a decoded header, `3 ≤ n` is
exactly `2 ≤ zeros`, because the exported bounds make `zeros` the index of the
leading digit of `n + 1`; both directions are derivable from the exported
conjuncts and neither is stated as an equivalence, only the direction used. The
two machine theorems therefore inherit G2p-f's exclusion of `zeros ≤ 1`, while
the three parser-side theorems carry no width premise and cover them; `zeros = 2`
is admitted, where the G2p-e round count `zeros - 2` is zero and the endpoint is
the finish alone. `totalClock` is **phase-local**: `startConfig` retags an actual
prior run and embeds the earlier phases' steps, which it does not count, and
`qDone` is an internal control tag, so nothing here is halting of a composed
machine, language acceptance, or a runtime. The module states no converse —
nothing derives a header, a width, `2 ≤ zeros`, or room from `qDone`, the
endpoint tape, or a digit at a register cell — and claims no parser execution,
no reading of the register as a number on the tape (the uniqueness conjunct is
arithmetic about the digits found there, not a decoding step the control
performs), no footprint or budget theorem, no malformed-gamma branch, no first
arrival from `startConfig`, no `ContentAccepts`, no clock composition, no
`ContentVerifierBridge`, and no P-vs-NP mainline result. Surface regressions
derive, for every budget, the wholly physical four-digit register `1101₂` at
cells `16 … 19` for header `(12, 7)` with `totalClock 15 3 = 31`; `110₂` at
cells `13 … 15` for header `(5, 5)` with `totalClock 12 2 = 5`, whose last digit
is the virtual tail; and a twelve-cell word, pinned to be the same word under
both the split `a = 8, m = 4` and the split `a = 1, m = 11` and decoding to
`(5, 5)` under either, where at `B = 0` room holds on the first in its tape form
and fails on the second in the outer two of the three equivalent forms, hence by
`room_iff_target_bound` in all three.

`ContentFixedGammaTargetRegisterDecrementBridge.lean` is the Part A G2r
infrastructure bridge, the pnp4 companion the pnp3 G2q slice deferred. It is
registered immediately after G2p-g and imports G2p-g together with the pnp3
`FixedGammaTargetRegisterDecrement`. It adds no machine: the run is G2q's
`register_decremented`, unchanged. Its whole mathematical content is one
instantiation. G2q's `decBit_sub_one` is arithmetic about an **arbitrary** `v`
whose bit `zeros - j` is register digit `j` at every `j ≤ zeros` and which has no
bit above `zeros`, and no pnp3 theorem supplies such a `v`; G2p-g's
`exhaustion_register_digits` proves both facts for `v = n + 1` on a decoded
header, and `v - 1` is then the decoded target `n`. Five public theorems, all
one-way out of a decoded header or a successful parse; the first three mention no
machine, no tag and no clock, and only `decrement_room_iff_target_bound` mentions
the budget `B`, through the tape length. Write `d = borrow x w zeros`:

* `decremented_register_digits` (one propositional hypothesis, a decoded header
  `contentHeader? (Fin.append x w) = some (n, consumed)`): some `zeros` has
  `gammaZeros? (Fin.append x w) = some zeros`, `consumed = 2 * zeros + 1`,
  `2 ^ zeros ≤ n + 1 < 2 ^ (zeros + 1)`, `d ≤ zeros`, the **decremented register
  equation** `FixedGammaTargetRegisterDecrement.decBit x w zeros d j =
  n.testBit (zeros - j)` at every `j ≤ zeros`, and the completeness fact
  `∀ b, zeros < b → n.testBit b = false`;
* `decremented_register_determines_target` (four hypotheses: a decoded header, a
  decoded width, the decremented digits of a `v`, and that `v` has no bit above
  `zeros`): `v = n`;
* `decrement_room_iff_target_bound` (two hypotheses: a decoded header and a
  decoded width): `n + 1 < 2 ^ (a + B) ↔ zeros + 1 ≤ a + B`, and
  `zeros + 1 ≤ a + B ↔ a + m + 2 + zeros < tapeLength (pairLength a m) B`, plus
  `n + 1 < 2 ^ (a + B) → n + 1 < 2 ^ (a + B + 1)` and
  `zeros = a + B → ¬ n + 1 < 2 ^ (a + B)`;
* `decremented_register_header_value` (four hypotheses: matching tag, decoded
  header, `3 ≤ n`, and `n + 1 < 2 ^ (a + B)`): some `zeros ≥ 2` has
  `consumed = 2 * zeros + 1`, the bit-length bounds, the room in its tape form,
  the incoming `finishTape B x w zeros` register cells reading
  `some ((n + 1).testBit (zeros - j))`, and, at
  `FixedGammaTargetRegisterDecrement.machine.run
  (FixedGammaTargetRegisterDecrement.decClock (a + m) zeros d)
  (FixedGammaTargetRegisterDecrement.startConfig B x w)`: `d ≤ zeros`, `qDone` at
  head `a + m + 1 + zeros - d`, the tape `decTape B x w zeros d`,
  `e.tape i = some (n.testBit (zeros - j))` at every `i.val = a + m + 1 + j` with
  `j ≤ zeros`, the completeness fact, the uniqueness of `n` among values read off
  those cells with no bit above `zeros`, every cell outside
  `[a+m+1, a+m+1+zeros]` equal to the incoming `finishTape` cell, and persistence
  at every later time;
* `decremented_register_parsed_target` (four hypotheses: matching tag, a
  successful `contentInput? codec (Fin.append x w) = some pr` for an arbitrary
  codec, `3 ≤ pr.2.n`, and `pr.2.n + 1 < 2 ^ (a + B)`): `pr.2.n = pr.1`,
  `contentHeader? (Fin.append x w) = some (pr.2.n, 2 * zeros + 1)`, and every
  endpoint conjunct of the header form restated in `pr.2.n`.

The room premise is G2q's, one cell more than G2p-f's because `qRegEnd` finds the
register's right end by the blank past it and by nothing else. The third and
fourth conjuncts of `decrement_room_iff_target_bound` place it exactly against
G2p-g's: it implies that one, and at the boundary width `zeros = a + B` it fails.
That G2p-g's can still hold at that boundary is not a conjunct of any theorem
here; `probe_decrement_room_strictly_stronger` exhibits it at a literal word,
which is what makes the strengthening strict rather than a restatement. It is carried, never
derived — `B` is a free budget — and sufficient only; there is still no footprint
theorem on the pnp3 side. The **gamma leading-digit convention is not restored**:
the convention writes `n + 1` so that the leading digit is a `true` the decoder
can find, and subtracting one destroys that, so when the incoming register is
exactly `2 ^ zeros` the borrow clears digit `0` and the endpoint's top cell is
`some false`. Nothing here re-establishes the invariant, and the decremented
register is not claimed to be a re-encodable gamma payload. For the same reason
G2p-g's virtual-tail conjunct has no analogue: a truncated payload's register cell
is `some false` before the phase and the borrow may flip it to `some true`, so the
only statement made about such a cell is the general one. Three numbers still stay
apart, and which of them is on the tape is what changed: after this phase the
register holds the digits of the decoded target `n`, where before it held those of
the encoded gamma integer `n + 1`, while `consumed = 2 * zeros + 1` and
`treeMCSPPrefixM codec pr.1` remain length conventions that never sit in a
register cell. `decClock` is **phase-local**: `startConfig` retags an actual prior
run and embeds the earlier phases' steps, which it does not count, and `qDone` is
an internal control tag, so nothing here is halting of a composed machine,
language acceptance, or a runtime. The module states no converse — nothing derives
a header, a width, `2 ≤ zeros`, room, or the borrow length from `qDone`, the
endpoint tape, or a digit at a register cell — and claims no parser execution, no
reading of the register as a number on the tape (the uniqueness conjunct is
arithmetic about the digits found there), no footprint or budget theorem, no
malformed-gamma branch, no degenerate width `zeros ≤ 1` on the machine side, no
`ContentAccepts`, no clock composition, no `ContentVerifierBridge`, and no P-vs-NP
mainline result. It states **no first arrival** either: the two machine theorems
give the endpoint at exactly `decClock (a + m) zeros d` and its persistence at
every later time, and no conjunct of theirs says `qDone` is not entered earlier —
minimality is G2q's `decrement_strict`, stated there for an arbitrary configuration
of the G2p-f endpoint shape and neither instantiated nor restated here. Surface
regressions derive, for every budget, the ordinary shape — header `(12, 7)`,
`borrow = 0`, `decClock 15 3 0 = 15`, endpoint register `1100₂` at cells
`16 … 19`, the digits of `12` — and the cleared-top-digit shape — header `(7, 7)`,
whose incoming register is exactly `2 ^ 3`, `borrow = 3`, `decClock 15 3 3 = 18`,
endpoint register `0111₂`, the digits of `7` with a `false` on top.

`ContentFixedGammaTargetUnaryCountdownBridge.lean` is the Part A G2t
infrastructure bridge, the pnp4 companion the pnp3 G2s-a slice deferred. It is
registered immediately after G2r and imports G2r together with the pnp3
`FixedGammaTargetUnaryCountdown`. It adds no machine: the run is G2s-a's
`first_round`, unchanged. Its whole mathematical content is again one
instantiation — G2s-a's `first_round` is stated for a positive `v` whose bit
`zeros - j` is G2q's decremented register digit `j` at every `j ≤ zeros` and which
has no bit above `zeros`, and no pnp3 theorem supplies such a `v`; its own probes
use the hand-picked literals `24` and `23`. G2r's `decremented_register_digits`
proves both digit facts for the decoded target `n`, and `3 ≤ n` gives positivity,
so `v := n` is the instantiation and the first round is a round on the actual
parsed target. Three public theorems, all one-way out of a decoded header or a
successful parse. Write `N = a + m` and `d = borrow x w zeros`:

* `countdown_room_iff_target_bound` (two hypotheses: a decoded header and a
  decoded width): `2 * (n + 1) < 2 ^ (a + B) ↔ zeros + 2 ≤ a + B`, and
  `zeros + 2 ≤ a + B ↔ a + m + 3 + zeros < tapeLength (pairLength a m) B`, plus
  `2 * (n + 1) < 2 ^ (a + B) → n + 1 < 2 ^ (a + B)` and
  `zeros + 1 = a + B → n + 1 < 2 ^ (a + B) ∧ ¬ 2 * (n + 1) < 2 ^ (a + B)`;
* `first_countdown_header_value` (four hypotheses: matching tag, decoded header,
  `3 ≤ n`, and `2 * (n + 1) < 2 ^ (a + B)`): some `zeros ≥ 2` has
  `consumed = 2 * zeros + 1`, the decoded width, the bit-length bounds, the room in
  its tape form, and, at the two configurations
  `FixedGammaTargetUnaryCountdown.machine.run (d + 2)
  (FixedGammaTargetUnaryCountdown.startConfig B x w)` and the same at
  `FixedGammaTargetUnaryCountdown.firstClock zeros d`: `d ≤ zeros`, `qLoop` on the
  separator blank `N + 2 + zeros` at both times, the entry tape
  `loopTape B x w zeros n 0` with every register cell `N + 1 + j` reading
  `some (n.testBit (zeros - j))`, the exit tape `loopTape B x w zeros (n - 1) 1`
  with those cells reading `some ((n - 1).testBit (zeros - j))`, the completeness
  fact for `n - 1`, the uniqueness of `n - 1` among values read off those cells
  with no bit above `zeros`, one mark at `N + 3 + zeros`, blanks from
  `N + 3 + zeros + 1` on, the separator blank `N + 2 + zeros`, the boundary blank
  `N`, and the untouched `finishTape` content below `N`;
* `first_countdown_parsed_target` (four hypotheses: matching tag, a successful
  `contentInput? codec (Fin.append x w) = some pr` for an arbitrary codec,
  `3 ≤ pr.2.n`, and the room at `pr.2.n`): `pr.2.n = pr.1`,
  `contentHeader? (Fin.append x w) = some (pr.2.n, 2 * zeros + 1)`, and every
  endpoint conjunct of the header form restated in `pr.2.n`.

The six cell conjuncts cover every index of the endpoint tape, so the statement
pins the whole tape rather than a sample of it. The room premise is G2s-a's: one
cell more than G2q's, because `qRunEnd` writes the first mark on the first blank
past the separator. The doubling in the target form is exact — the gamma bounds
give `2 ^ (zeros + 1) ≤ 2 * (n + 1) < 2 ^ (zeros + 2)`, so neither direction of the
equivalence has slack — and the last two conjuncts place this room against G2q's:
it implies it, and at the boundary width `zeros + 1 = a + B` G2q's holds while this
one fails. Unlike the G2r separation, which stated only the failing half and left
the other to a probe, *both* halves are stated and proved here;
`probe_countdown_room_boundary_nonvacuous` therefore only shows that the boundary
hypothesis is inhabited, at the `a = 1, m = 11` split of the twelve-cell word with
`B = 2`. Like G2q's, the room is carried, never derived — `B` is a free budget —
and sufficient only; there is still no footprint theorem on the pnp3 side, and it
allocates the *first* lane cell rather than bounding the countdown.

Four numbers now stay apart, and the fourth is the one on the tape: `zeros` is the
physical gamma width, `n + 1` the encoded gamma integer, `consumed = 2 * zeros + 1`
and `treeMCSPPrefixM codec pr.1` length conventions that never sit in a register
cell, `n` what G2r left in the register, and `n - 1` what this round leaves there.
The tally is one **mark**; calling it the target in unary would be a claim about a
decoded value, and no theorem here decodes anything. The gamma **leading-digit
convention is not restored** and is destroyed further at each round, so the
endpoint register's top cell may be `some false` and nothing here excludes it.

This is **one round**. Nothing iterates, composes rounds, or states a clock beyond
`firstClock zeros d = 2 * zeros + d + 9`, which is phase-local and counts none of
the steps `startConfig` embeds — that configuration retags an actual G2q run, which
itself retags an actual G2p-d run. There is deliberately **no persistence
conjunct**: unlike G2r's `qDone`, `qLoop` does not absorb, so each endpoint holds at
exactly its stated time and says nothing about any other time, and there is no
deadline and no clamp. There is **no lane fence**: a target too large for the budget
would run `qRunEnd` off the end of the tape and stick there, which is a timeout and
therefore neither verdict, and no theorem here excludes that or claims the target
fits. The module states no converse — nothing derives a header, a width,
`2 ≤ zeros`, room, the borrow length or a parsed target from `qLoop`, from an
endpoint tape, or from a digit at a register cell — and claims no first arrival, no
parser execution, no reading of the register as a number on the tape (the
uniqueness conjunct is arithmetic about the digits found there), no footprint or
budget theorem, no malformed-gamma branch, no exhaustion, no degenerate width
`zeros ≤ 1` on the machine side, no `accepts`, no `AcceptsAt`, no `ContentAccepts`,
no language membership, no clock composition, no `ContentVerifierBridge`, and no
P-vs-NP mainline result. Surface regressions derive, for every budget, the ordinary
shape — header `(12, 7)`, `borrow = 0`, entry at `2` steps with the register still
`1100₂`, `firstClock 3 0 = 15`, endpoint register `1011₂` at cells `16 … 19` with
one mark at `21`, the separator `20` and cell `22` blank — and the cleared-top shape
— header `(7, 7)`, `borrow = 3`, `firstClock 3 3 = 18`, endpoint register `0110₂`
with the `false` still on top and one mark at `21`.

`ContentFixedGammaTargetUnaryCountdownIterationBridge.lean` is the Part A G2v
infrastructure bridge, the pnp4 companion the pnp3 G2u slice deferred. It is registered
immediately after G2t and imports G2t together with the pnp3
`FixedGammaTargetUnaryCountdownIteration`. It adds **no machine, no state and no table
row**: the run is G2u's `register_drained`, unchanged, which is itself only G2s-a's
fixed 11-state 33-row table run for longer. Its whole mathematical content is again one
instantiation, exactly as G2t's was — `register_drained` is stated for a `v` whose bit
`zeros - j` is G2q's decremented register digit `j` at every `j ≤ zeros` and which has
no bit above `zeros`, no pnp3 theorem supplies such a `v`, and its own probes use the
hand-picked literals `24` and `3`; G2r's `decremented_register_digits` proves both digit
facts for the decoded target `n`, so `v := n` is the instantiation and the whole
countdown is a countdown of the actual parsed target. Four public theorems, all one-way
out of a decoded header or a successful parse. Write `N = a + m` and
`d = borrow x w zeros`:

* `countdown_width_eq_gammaZeros` (two hypotheses: a decoded header and a decoded
  width): `zeros = gammaZeros n`, together with `2 ^ gammaZeros n ≤ n + 1` and
  `n + 1 < 2 ^ (gammaZeros n + 1)`. The physical width is what
  `FixedContentGammaTerminator.gammaZeros?` counts off the word; the canonical width is
  what `gammaZeros n = bitLength (n + 1) - 1` computes from a number. The proof is
  exponent uniqueness: G2p-g exports `2 ^ zeros ≤ n + 1 < 2 ^ (zeros + 1)`, `bitLength`
  satisfies the same two bounds at `gammaZeros n`, and no natural lies in two such
  windows. Both widths are functions of data that already exist, so this is an equation
  between two computed quantities, **not** extraction of a runtime value from a proof.
  No **new direct import** is taken for it, and its proof uses no declaration of the much
  broader I1 gate-closure module — which is not the same as that module being absent: it is
  already in this bridge's transitive closure, through the G2o header-value bridge, whose
  semantic-bridge import reaches `FixedContentGammaTerminatorCorrect` and thence
  `FixedContentTagGateCorrect`, which imports both `ContentPrefixExtensionGateClosure` and
  `BoundedContentSemanticVerifier`. The dependency this bridge actually uses from that
  direction is G2o's `contentInput?_target_eq_contentHeader`, consumed by
  `countdown_drained_parsed_target` below, and *its* proof does invoke I1's
  `contentInput?_lengthGate_vacuous`;
* `countdown_drain_cap_iff_machine_room` (the same two): `zeros = gammaZeros n`; the
  cap-and-room pair `n ≤ F ∧ gammaZeros n + 2 + F ≤ a + B` is the same condition as
  `n ≤ F ∧ zeros + 2 + F ≤ a + B`; `zeros + 2 + F ≤ a + B` is the same condition as
  `a + m + 3 + zeros + F < tapeLength (pairLength a m) B`; and cap plus room imply
  `2 * (n + 1) < 2 ^ (a + B)`, G2t's first-round room. That last implication is the
  **only** relationship claimed between the two rooms;
* `countdown_drained_header_value` (five hypotheses: matching tag, decoded header,
  `3 ≤ n`, the cap `n ≤ F`, the room `gammaZeros n + 2 + F ≤ a + B`): some `zeros ≥ 2`
  is the canonical width, has `consumed = 2 * zeros + 1`, the decoded width, the
  bit-length bounds, G2t's room, and the room in its tape form; and at
  `FixedGammaTargetUnaryCountdown.machine.run (d + 2)
  (FixedGammaTargetUnaryCountdown.startConfig B x w)` and the same at
  `FixedGammaTargetUnaryCountdownIteration.fullClock zeros d n`: `d ≤ zeros`, `qLoop` on
  the separator blank `N + 2 + zeros` with entry tape `loopTape B x w zeros n 0` whose
  register cell `N + 1 + j` reads `some (n.testBit (zeros - j))`, then the absorbing
  `qDone` on that same cell with tape `loopTape B x w zeros 0 n`, every register cell
  `some false`, exactly `n` marks on `[N+3+zeros, N+3+zeros+n)`, blanks from
  `N+3+zeros+n` on, and persistence at every later time;
* `countdown_drained_parsed_target` (five: matching tag, a successful
  `contentInput? codec (Fin.append x w) = some pr` for an arbitrary codec, `3 ≤ pr.2.n`,
  the cap and the room at `pr.2.n`): `pr.2.n = pr.1`,
  `contentHeader? (Fin.append x w) = some (pr.2.n, 2 * zeros + 1)`, and every endpoint
  conjunct of the header form restated in `pr.2.n`.

`3 ≤ n` reaches `2 ≤ zeros`, the width premise G2u inherits from G2q and thence from
`payload_exhausted`. Unlike G2t's use of the same hypothesis, nothing here needs
`1 ≤ n`: G2u's drain has no positivity premise, because at `v = 0` no round runs and the
exhaustion fires at once. The whole-tape equality pins every index, and the cell
conjuncts read the same endpoint back at the addresses a successor phase would care
about. The lane holds `n` **marks** — the tally is exactly as long as the decoded
target, stated as a cell predicate, not as a claim that the machine re-encoded `n` in
unary anywhere. The gamma **leading-digit convention is not restored**: G2q destroyed it,
each round destroyed it further, and the endpoint register is all `some false`.

There is **no fence**. `F` is a parameter of every statement, nothing instantiates it,
and no cell is a cutoff: `loopTape` is blank at `N + 3 + zeros + F`, an installed
`some false` there is not a `loopTape`, and nothing here is evidence that any of these
theorems survives one. The room is a joint condition on the parsed target and the
budget, carried and never derived — `B` is free — and sufficient and used, never shown
necessary: no footprint or budget theorem exists on the pnp3 side, and G2u's
`check_below_room_drain_probe` exhibits a budget where the condition fails while the
canonical unfenced drain completes. A target too large for the budget still runs
`qRunEnd` off the end of the tape and sticks there, a timeout and therefore neither
verdict. **Persistence is not first arrival**: `qDone` absorbs, and no conjunct says it
is entered for the first time at `fullClock zeros d n`. No **converse** is stated in
either direction — nothing derives a header, a width, `2 ≤ zeros`, the cap, the room,
the borrow length or a parsed target from `qDone`, from the endpoint tape or from a mark
in the lane. Parser execution, a malformed-gamma branch, the degenerate widths
`zeros ≤ 1` on the machine side (the two parser-side theorems carry no width premise and
cover them), `accepts`, `AcceptsAt`, `ContentAccepts`, language membership, clock
composition, `ContentVerifierBridge` and P-vs-NP mainline progress are all absent.
`fullClock` counts this phase's steps alone — not one of the steps `startConfig` embeds,
that configuration retagging an actual G2q run which itself retags an actual G2p-d run —
and `qDone` is an internal control tag, so reaching it is phase-local acceptance.
Surface regressions cover the ordinary shape at the header `(12, 7)` — canonical width
`gammaZeros 12 = 3` recovered from that header rather than reduced, `borrow = 0`,
`fullClock 3 0 12 = 301`, `qDone` on the separator blank `20`, register cells `16 … 19`
all `some false`, `some true` at every cell of `[21, 33)`, cell `33` blank, and the
endpoint still `qDone` at step `400` — and the room separation at `B = 0`, where G2t's room and its
first-tally-cell tape form both hold while the cell `21 + 12 = 33` that a twelve-mark
lane reserves is outside the tape, so G2v's room fails at every `F ≥ 12` — which is
every cap the countdown admits there, since `n ≤ F`.

`ContentCountdownLinearCap.lean` is the Part A G2w-a slice, extended by Part A G2w-b: a
value for G2v's lane cap obtained from *semantics*, and then a value for G2v's budget.
It is registered after both G2v and FEAS-0's
`ContentTargetSizeBound`, which it imports, and it builds **no machine, no state, no
table row, no cutoff cell and no `qOverflow` endpoint**. Its starting point is that no
theorem bounds the target from parser success alone, and none is claimed here: the
source is virtually zero-padded, so the strict parser's returned target carries no bound
on the physical length. Six public theorems. The four G2w-a ones are stated at the
concrete `treeCircuitWitnessCodec (thresholdPoly k)` throughout, because the wide case is
a codec-specific fact and no codec-generic analogue is asserted:

* `contentSemanticAccepts_parsed_target_le_length` (two hypotheses: a successful
  `contentInput? codec z = some pr` and `contentSemanticAccepts codec z = true`; the
  exponent `k` is data): `pr.2.n ≤ N` for `z : PrefixBitVec N`. If
  `treeMCSPPrefixM codec pr.2.n ≤ N`, `instanceSize_lt_treeMCSPPrefixM` already places
  `pr.2.n` below it; otherwise `contentAccepts_parsed_tableLen_le_of_header_target_wide`
  turns acceptance into `tableLen pr.2.n = 2 ^ pr.2.n ≤ N` and `pr.2.n < 2 ^ pr.2.n`
  finishes. `contentInput?_target_eq_contentHeader` is what lets the wide case be read
  at the parsed target rather than at the header's. Neither branch needs `0 < N`;
* `contentSemanticAccepts_eq_false_of_length_lt_parsed_target` (the successful parse and
  `N < pr.2.n`): the frozen Boolean checker rejects. This is a statement about
  `contentSemanticAccepts` and nothing else — it does not say that any machine detects
  the overflow, only that rejecting would be the correct verdict;
* `contentSemanticAccepts_parsed_target_le_pair_length`: the same bound at the split
  `z := Fin.append x w`, whose `N` is the compacted content length `a + m` that the
  G2q/G2s-a/G2u tape ABI is laid out against. This is the form that makes `F := a + m`
  legitimate; it instantiates no `F` by itself;
* `countdown_drained_accepted_content` (five: matching tag, the parse, acceptance,
  `3 ≤ pr.2.n`, and the room at `F := a + m`): `pr.2.n ≤ a + m` together with G2v's
  `qDone` endpoint at that cap. The cap is **derived** from acceptance; the room is
  still carried.

The two G2w-b theorems close the budget:

* `concatBitstring_eq_append` (no hypotheses, no codec, both blocks arbitrary):
  `Pnp3.ComplexityInterfaces.concatBitstring x w = Fin.append x w`. It exists because
  GATE-0's accepted words are built with `concatBitstring` while every fixed-phase
  statement of this pipeline is laid out against `Fin.append`. No parse, acceptance,
  header or machine occurs in it, and it says nothing about which splits of a word exist;
* `countdown_drained_accepted_content_at_polyClock` (**three**: the successful parse, the
  Boolean acceptance, `3 ≤ pr.2.n`): the same endpoint at the concrete budget
  `B := polyClock 3 (PairEncoding.pairLength a m) = (2 * a + 1 + m) ^ 3 + 3`, run to
  exactly `B` steps. No tag premise — `fixedTag_semantic_factorization` derives it from
  acceptance — no cap, no room, no free `B`, no free `F`, no runtime premise and no
  correctness premise. Acceptance caps the target at `a + m`, `gammaZeros n ≤ n` caps the
  width, `borrow_pins` caps the borrow by the width, and the cube dominates the expanded
  clock `fullClock zeros d n = d + n*n + n*(2*zeros+6) + 2*zeros + 7`, so the room
  `gammaZeros pr.2.n + 2 + (a + m) ≤ a + B` and the clock bound
  `fullClock zeros (borrow x w zeros) pr.2.n ≤ B` are both **conclusions**, exported as
  conjuncts alongside `3 ≤ a + m` and the derived tag. The transport from `fullClock` to
  `B` steps is G2v's persistence conjunct, so it is persistence rather than first arrival.

Three caveats specific to G2w-b. The exponent `3` is sufficient and is **not** shown
least; nothing rules out a smaller one. The same number `B` is both the tape budget that
`startConfig` and `tapeLength` are laid out against and the number of steps run, which is
an instantiation choice rather than a theorem — nothing says the two must agree, only
that this one value is large enough for both. And `polyClock` occurs here as an
arithmetic value: no `DecidesWithin`, `UniformP`, runtime or `NP` statement is made or
implied. The surface probe `probe_countdown_polyClock_accepted_target_three` inhabits the
three premises **jointly**, one accepted word per exponent — GATE-0's zero-prefix query
for the all-false table on three variables followed by the certificate that
`contentAccepts_zeroPrefixQuery_of_predicate` supplies — at the pinned target `pr.2.n = 3` and the pinned width
`gammaZeros 3 = 2`, and reads the `qDone` endpoint state back after exactly `B` steps. It
exhibits one word per exponent and nothing about any other: no *rejected* word, no
*overshooting* word, and no tape cell.

The more expensive alternative is documented and **not implemented**: if the contract
must instead be that every *bounded-parser* success completes the countdown, the cap has
to come from `boundedContentCap k N = N ^ contentCapExponent k + contentCapExponent k`,
since `boundedContentInput?` success bounds `treeMCSPPrefixM codec pr.1` and
`pr.2.n = pr.1 ≤ treeMCSPPrefixM codec pr.1`. That is a polynomial lane rather than a
linear one; this module defines no such cap and takes **no new direct import** for one.
`BoundedContentSemanticVerifier` is nonetheless already in its transitive closure, through
`FixedContentTagGateCorrect`, so the accurate statement is that no declaration of it is
*used* here, not that it is absent. Non-vacuity is not claimed here either — GATE-0's
`contentAccepts_nonvacuous_treePoly` and `contentAccepts_zeroPrefixQuery_of_predicate`
supply it, and the surface probes only read it back.
`probe_linear_cap_accepted_nonvacuous` shows that the parse and
acceptance premises of `contentSemanticAccepts_parsed_target_le_length` hold together on a
word that exists. It pins no target value and does not inhabit the overflow theorem's
premise pair, so that theorem is not shown non-vacuous; nor is any parse-successful word
exhibited whose target overshoots its own length, so acceptance is used rather than shown
necessary. No probe states the free-budget capstone's five hypotheses directly, but the
G2w-b probe inhabits them at `B := polyClock 3 (pairLength a m)`: G2w-b derives the tag,
cap and room from its jointly inhabited parse, acceptance and target-bound premises. Thus
that capstone is non-vacuous at this one budget, while no probe exhibits its room at a free
`B`. Its hypotheses are not independent: acceptance already implies the tag premise, by
`fixedTag_semantic_factorization`. No converse is stated:
nothing derives acceptance, a parse, a header or a width from `pr.2.n ≤ N`, and a
`false` verdict can equally come from a failed parse or a failed witness check. No
runtime bound, advice-freedom claim, `NP` membership, `accepts`, `AcceptsAt`, language
membership or `ContentVerifierBridge` appears, and this is not P-vs-NP mainline progress.

`ContentFixedGammaTargetDecrementCountdownBridge.lean` is the Part A G2x slice: the
first **executed** phase handoff of the chain, on the parsed target, at G2w-b's budget.
The pnp3 half supplies a generic combinator `UniformTM.seq M₁ M₂` — one closed table whose
`M₁` rows are routed so that a target `M₁.accept` enters `M₂.start` in that same
transition, a zero-step handoff as in the routed parser/verifier constructor, with
`seq_handoff` composing the two runs under a load-bearing first-arrival hypothesis — and
its one application `FixedGammaTargetDecrementCountdown.machine`, G2q's 7-state table
followed by G2s-a's 11-state table as one 18-state, 54-row table.

* `decrement_countdown_drained_accepted_content_at_polyClock` (**three**: the successful
  parse, the Boolean acceptance, `3 ≤ pr.2.n`; no tag, cap, room, budget, clock, width,
  digit, initial-state, correctness or runtime premise): with `N = a + m`,
  `zeros = gammaZeros pr.2.n`, `d = borrow x w zeros`, `T = decClock N zeros d`,
  `C = T + fullClock zeros d pr.2.n` and `B = polyClock 3 (pairLength a m)`, out of the
  composed `startConfig` — G2q's own, the retagged *actual* G2p-f endpoint, routed — the
  composed control is in neither verdict before `T`, is the countdown's landed
  `startConfig B x w` re-embedded at exactly `T`, satisfies `C ≤ B`, and is in the composed
  accept on the separator blank with tape `loopTape B x w zeros 0 pr.2.n` at exactly `C`, at
  exactly `B` and at every later time. The cap, tag, header, width and clock bound are
  derived and exported as in G2w-b, while G2w-b's room is derived and used here but is not
  among this statement's conclusions; the switch time is G2q's first arrival, from G2q's
  `decrement_strict`, and `pr.2.n = pr.1` is exported. The surface probe
  `probe_decrement_countdown_polyClock_accepted_target_three` reuses G2w-b's accepted word at
  the pinned target `3` and reads the switch and the composed accept back.

Caveats specific to G2x. It is **one handoff of seventeen**: the composed `startConfig`
still embeds every earlier phase, the sixteen earlier handoffs stay proof-level, no
`initialConfig` on a raw pair input is executed, and no clock counts a step of any earlier phase.
`T` is the first time the
handoff fires, but no theorem says `C` is the first time the composed accept is entered.
Both tables are unfenced, hence so is the composition: accepted words never overflow the
lane, since `pr.2.n ≤ N` is derived, but an overshooting word still times out, and the rows
routed to the composed reject are pinned and never exercised. Targets `0`, `1`, `2` stay
excluded. The composed accept is the countdown's phase-local `qDone`, reached out of a
retagged actual prior endpoint — neither halting on a raw input nor language acceptance —
and the machine is a V1 `UniformTM` on `Option Bool` cells laid out against
`pairLength a m`, not the legacy `TM` with a `runTime` field that `ContentVerifierBridge`
names (see "Runtime model behind input (2)"). No `accepts`, `AcceptsAt`, `DecidesWithin`,
`UniformP`, `VerifiesRelation`, `NP` membership, advice-freedom claim or
`ContentVerifierBridge` appears, and this is not P-vs-NP mainline progress.

`FixedContentGammaAnchorCorrect.lean` is the Part A G2a bridge. It proves the
exact G1-final-to-G2a operational handoff and provides a logical cell-7
restoration taking the successful marked tape back to literal `contentTape`.
Header and gamma decode facts remain facts about the unchanged source word.
There is no payload traversal, virtual payload read, decoded value, capped
arithmetic, or semantic-acceptance theorem. G2b must not write `none` inside
its counter zone and must physically restore cell 7 before any phase whose
contract expects `contentTape`.
