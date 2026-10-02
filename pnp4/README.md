# pnp4

`pnp4` is a separate Lean-library track for algorithms-to-lower-bounds work.

Scope split:

- `pnp3`: SAL / locality / Route-A/B frontier.
- `pnp4`: algorithmic lower bounds / MCSP / compression magnification frontier.

Current goal:

- mainline: expose a source whose endpoint has the strength
  `NP ⊄ PpolyDAG`, then feed the existing `P ≠ NP` bridge;
- side track: keep the `AC0[p]`, formula, local-PRG, and coin-problem work as
  published restricted-lower-bound formalization.

Milestones:

1. Formalize circuit-class and truth-table MCSP skeletons.
2. Formalize the coin-problem interface and MCSP-to-coin reduction.
3. Add an explicit `AC0[p]` coin-lower-bound contract layer and derive the
   corresponding MCSP threshold-oracle exclusion theorem surface.
4. Add a local-PRG transfer layer and derive counting-closed exclusion theorems
   for tree-MCSP threshold oracles.
5. Add a paper-facing local-PRG hardness-spec layer for published MCSP lower
   bounds.
6. Formalize a Williams-style SAT-algorithm-to-lower-bound schema.

Ultimate bridge target:

```text
MCSP ∉ PpolyDAG ⇒ NP ⊄ PpolyDAG ⇒ P ≠ NP
```

Next progress target:

1. Treat restricted `AC0[p]`/formula/local-PRG lower bounds as side-track
   milestones unless they are paired with an explicit bridge to `PpolyDAG`.
2. Use `Frontier/CompressionMagnification.lean` as the P-vs-NP mainline:
   reduce a search-MCSP/resource-bounded-compression weak lower-bound package
   to `VerifiedNPDAGLowerBoundSource`.
3. Count a new theorem as P-vs-NP progress only if it reduces
   `SearchMCSPWeakLowerBound` or directly reduces `VerifiedNPDAGLowerBoundSource`.
4. The most concrete live form of that obligation is the hypothesis pair of
   `NP_not_subset_PpolyDAG_treePoly`
   (`Frontier/ContractExpansion/ConsolidatedTreeSeparation.lean`): a
   `NoPolynomialBoundedSearchSolver` for the concrete tree codec, and a
   `PrefixExtensionNPWitness` for the concrete prefix parser.  See the downstream
   section below.

Honesty policy:

`pnp4` does not claim unconditional `P ≠ NP` unless it proves `MCSP ∉ PpolyDAG`
or another explicit `NP` language lower bound against `PpolyDAG` without hidden
assumptions.

Current reference point for the coin-problem track:

- Golovnev, Ilango, Impagliazzo, Kabanets, Kolokolova, Tal,
  `AC^0[p] Lower Bounds Against MCSP via the Coin Problem`, ICALP 2019 /
  ECCC 2019.

The current `pnp4` code proves reusable transfer/consequence layers for that
route, but it still does not claim the concentration, hybrid, or concrete
`AC^0[p]` lower-bound ingredients.  Those remain explicit published contracts.

Current reference point for the mainline compression-magnification frontier:

- McKay, Murray, Williams, `Weak lower bounds on resource-bounded compression
  imply strong separations of complexity classes`, STOC 2019.

The Lean surface records this as a theorem-facing source package rather than as
an already-proved result: a `SearchMCSPWeakLowerBound` must supply a verified
`NP` language lower bound against `PpolyDAG`.

Current theorem surface status:

- `Frontier/SignedSupportNoGo/`: three-module generic infrastructure/no-go
  extraction over the current `DagCompose` / `DagCircuit` model.  It provides
  finite rational Boolean averages, the exact equivalence between existential
  reverse-one-sided unnormalized signed fooling and support hitting, an explicit finite-set
  avoider DAG, `FiniteEasyCover`, and dense/easy plus signed-fooling no-go
  endpoints.  Its eventual-linear cover-bits theorem is limited to
  truth-table geometry and retains explicit sparsity and dense/easy premises.
  It has no one-tape/streaming dependency and proves no `P != NP` consequence.
- `BasicCircuitClasses.lean`: minimal non-uniform circuit-class interface plus
  the input-masking operator `maskVec` and `ClosedUnderInputMasking`, the class
  closure condition needed for the masking/averaging translation proof.
- `CoinProblem.lean`: exact finite-distribution semantics for the coin problem,
  monotonicity and complement laws for acceptance probabilities, total-mass
  normalization for product Bernoulli weights, and the reusable probability-gap
  criterion for `SolvesCoinProblem`.
- `CoinMaskingTranslation.lean`: probability-facing decomposition of the
  masking translation step, including rational-valued product expectations,
  `maskedAcceptanceAverage`, `MaskingBiasParams`, pushforward identities as
  explicit facts, and the finite-mask averaging contract.
- `MCSPCoinReduction.lean`: threshold-oracle reduction surface from MCSP to coin
  distinguishing on truth tables, including accept/reject facts for correct
  MCSP threshold oracles.
- `MCSPCoinReductionContract.lean`: smaller theorem-facing half-vs-fair
  reduction contract, fixing a threshold schedule and the exact MCSP slice
  coin-solving obligation via separate low-acceptance, fair-acceptance, and
  advantage-gap certificates, with a named constructor from those distribution
  facts, a lower-level constructor from `treeMCSPPredicate` mass facts, and the
  explicit polarity fact that the half-vs-fair `highBias` side is fair bias
  `1 / 2`.  It also records the corrected-polarity rejection profile, where
  acceptance means "not below the tree-MCSP threshold"; this is the working
  direction for the half-vs-fair MCSP-side reduction.  The current
  source-facing constructor exposes the remaining biased/easy source theorem as
  `HalfVsFairBiasedLowComplexityMassFacts`: low-bias tables are low-complexity
  with high probability.  This is a strong direct half-vs-fair route, kept
  explicit rather than hidden inside the final contract.  The fair-side lower
  bound is fixed to the Shannon-counting value `1 - treeMCSPCountRatio`; the
  remaining companion obligation is the explicit advantage-gap arithmetic.  The
  more paper-faithful route is represented separately by
  `AdjacentBiasMCSPThresholdSeparationFacts`, read as a generic
  `CoinDistinguisherFamily`, plus
  `CoinDistinguisherToHalfVsFairTranslationContract`.  This matches the
  adjacent-bias separation and translation/rescaling shape of the published
  proof: translation produces a new distinguisher, not necessarily the same
  MCSP hard-threshold predicate.  The lower-bound-facing layer adds
  `CircuitCoinDistinguisherFamily` and `CoinTranslationPreservesClass`, making
  explicit the required class/size preservation: a circuit-realized source
  distinguisher translates to a circuit-realized half-vs-fair distinguisher
  with no larger size schedule.  This now feeds the published coin lower-bound
  contract through `BoundedClassSolvesCoinProblem_of_translated_realization`
  and the adjacent-bias contradiction theorem
  `false_of_AC0p_circuit_family_computes_adjacentBias_MCSP_hardDecision`.
  The older
  `AdjacentBiasToHalfVsFairRejectionTranslationContract` remains only as a
  stronger direct-translation target.
- `AC0pCoinLowerBound.lean`: explicit contract layer for published `AC^0[p]`
  coin lower bounds, in size-bounded form.
- `MCSP_AC0p_Final.lean`: consequence layer saying that, under the `AC^0[p]`
  lower-bound contract and either a concrete reduction witness or the smaller
  reduction contract, the corresponding exact MCSP slice has the expected
  size-lower-bound form.
- `MCSP_AC0p_Quantitative.lean`: paper-facing quantitative shell for the
  published `exp(N^(0.49 / d))` envelope, with explicit bias-gap and advantage
  profile metadata for the half-vs-fair coin regime.
- `AC0pCoinAsymptotic.lean`: global half-vs-fair MCSP coin asymptotic language
  on truth-table lengths, unconditional arithmetic that the published
  `exp(N^(0.49 / d))` envelope beats every polynomial on arbitrarily late
  truth-table slices, and the published-contract consequence `¬ InAC0p`.
- `Growth.lean`: unconditional arithmetic that
  `QuasiPolyLower N = N ^ log2 N` has super-polynomial growth.
- `SuperPolynomialBridge.lean`: generic bridge from a super-polynomial
  `SizeLowerBound` to exclusion of polynomial-size non-uniform families.
- `AC0pSuperPolynomialBridge.lean`: fixed-depth `AC0[p]` specialization,
  deriving `¬ InAC0p` from depthwise quasi-polynomial lower bounds.  The bridge
  is unconditional; the quasi-polynomial lower-bound contract remains the
  external published input.
- `AsymptoticSizeLowerBound.lean`: eventual lower-bound interface matching
  published "for sufficiently large input length" theorem statements, plus the
  generic bridge to exclusion of polynomial-size non-uniform families.
- `AC0pAsymptoticBridge.lean`: fixed-depth `AC0[p]` specialization for eventual
  quasi-polynomial lower bounds and the corresponding asymptotic published
  contract shape.
- `LocalPRG.lean`: truth-table local-PRG surface with easy-image and
  pseudorandomness interfaces against size-bounded circuit classes.
- `MCSP_LocalPRG_Transfer.lean`: proved Shannon-counting upper bound for
  uniform acceptance of exact tree-MCSP threshold oracles and the resulting
  local-PRG transfer contradiction theorem surface, plus exact tree-MCSP
  threshold accept/reject facts and probability lifts from predicate mass to
  exact threshold-decision acceptance.  It also defines the reusable
  `treeMCSPCountRatio`, proves the fair-side Shannon-counting upper bound for
  `treeMCSPPredicateDecision`, and proves the
  complementary fair-side lower bound for the hard-table decision
  `notTreeMCSPPredicateDecision`.
- `LocalPRGHardnessSpec.lean`: paper-facing published-route layer packaging
  `LocalPRGHardnessSpec`, target family models, and exact-threshold exclusion
  theorems for published local-PRG regimes.
- `FormulaCircuitTargetModel.lean`: concrete target model connecting the new
  `pnp4` circuit-class interface to the in-repo `pnp3` formula syntax.
- `FormulaCircuitPublishedLowerBound.lean`: theorem-facing published lower-bound
  shortcut for already-final exact slice statements.
- `MCSP_Formula_Final.lean` and `MCSP_Formula_Theorem2Quantitative.lean`: CKLM
  formula-route source contracts and exact-slice consequences.  The preferred
  mainline is now
  `CKLMFormulaCircuitLocalPRGSourceContract → FormulaCircuitPublishedLowerBoundContract → SizeLowerBound`.
- `FormulaCircuitAsymptotic.lean`: optional bridge from slice lower bounds to
  `¬ PpolyFormula`, only under an explicit table-length escape hypothesis.
  It also records the guardrail that the current CKLM `N^{2-o(1)}` envelope
  cannot discharge that asymptotic growth hypothesis by itself.
- `BridgeToPpolyDAG.lean`: final bridge shell from a verified `NP` language
  lower bound against `PpolyDAG` to the existing `pnp3` `P ≠ NP` target.
- `Frontier/PvsNPBridgeRequirements.lean`: explicit frontier split between
  restricted `AC0[p]` milestones and the separate source needed for `P ≠ NP`:
  a verified `NP` language lower bound against `PpolyDAG`.  It records that an
  `AC0[p]` exclusion only reaches the final bridge after an additional
  restricted-to-`PpolyDAG` source theorem.
- `Frontier/CompressionMagnification.lean`: P-vs-NP mainline surface for
  search-MCSP/resource-bounded-compression magnification.  It names the
  repository-local `NP_not_subset_Ppoly` endpoint as `NP_not_subset_PpolyDAG`,
  derives `P ≠ NP` from it, and accepts only packages that produce a
  `VerifiedNPDAGLowerBoundSource`.
- `Frontier/SearchMCSPMagnification.lean`: falsifiable mainline source target
  for search-MCSP/resource-bounded-compression magnification.  It replaces a
  bare `Prop` with a concrete search/compression problem, a circuit class, a
  size schedule, and the lower-bound statement that no bounded search solver
  exists.  A separate `SearchMCSPMagnificationContract` is still required to
  turn that weak lower bound into a `VerifiedNPDAGLowerBoundSource`.
- `Frontier/SearchMCSPConcreteTargets.lean`: concrete tree-MCSP promise-search
  target for the mainline.  Instances are truth tables promised to satisfy the
  existing proof-level `treeMCSPPredicate`; a witness encoding must prove
  soundness and completeness for small tree-circuit witnesses.  This is the
  first named target where a weak search lower bound can be paired with a
  magnification contract to reach `PpolyDAG`.  The preferred witness surface is
  now codec-shaped: `TreeCircuitWitnessCodec` supplies `encode`, `decode`, and
  `decode_encode`, and `TreeMCSPSearchWitnessEncoding.ofCodec` derives the
  verifier from actual decoded `Pnp3.Models.Circuit` witnesses.
- `Frontier/DagSupportCardinality.lean`: infrastructure proving that the
  dependency-closed support of a DAG is contained in its finite direct-input
  cover and has cardinality at most twice `DagCircuit.size`.  It reuses the
  existing support-based evaluation invariance and does not reduce a
  P-vs-NP source obligation.

## Downstream decision→search extraction (`Frontier/ContractExpansion/`)

`Frontier/ContractExpansion/` replaces the abstract
`SearchMCSPMagnificationContract.magnifiesToVerifiedDAGSource` jump with a
machine-checked **conditional** chain:

```text
PpolyDAG (PrefixExtensionLanguage (treeMCSPConcretePrefixParser threshold codec))
  → bounded search solver (greedy query circuits over a shared DAG bundle)
contrapositive: NoPolynomialBoundedSearchSolver + growth ⇒ ¬ PpolyDAG
  + NP-membership witness ⇒ VerifiedNPDAGLowerBoundSource ⇒ (conditional) NP ⊄ PpolyDAG
```

It is strictly conditional: it does **not** prove `P ≠ NP` or `NP ⊄ PpolyDAG`
unconditionally.  What it does is expose the exact remaining obligations as explicit,
clearly-typed inputs.

At a **concrete polynomial threshold** `thresholdPoly k` the growth premise is already
discharged (`polyBoundedInTable_thresholdPoly`, `ThresholdGrowth.lean`) and the concrete
codec is constructed (`treeCircuitWitnessCodec`, `ConcreteTreeCodec.lean`), so the
consolidated surface in `Frontier/ContractExpansion/ConsolidatedTreeSeparation.lean`

```lean
verifiedSource_treePoly          : … → VerifiedNPDAGLowerBoundSource
NP_not_subset_PpolyDAG_treePoly  : … → Pnp3.ComplexityInterfaces.NP_not_subset_PpolyDAG
```

depends on **exactly two** explicit hypotheses:

1. `NoPolynomialBoundedSearchSolver (treeCircuitWitnessCodec (thresholdPoly k))` — a
   genuine `P/poly` circuit lower bound for the concrete tree-MCSP search problem (hard,
   research-level mathematics; **not** a Lean engineering task);
2. `PrefixExtensionNPWitness (treeMCSPConcretePrefixParser (thresholdPoly k) …)` — a
   concrete verifier TM with a polynomial runtime bound and certificate correctness (the
   NP / runtime track).

The preferred verifier target is the content-truthful reroute
`NP_not_subset_PpolyDAG_treePolyCT`, whose two hypotheses are the same no-solver lower bound and
`ContentPrefixExtensionNPWitness (treeCircuitWitnessCodec (thresholdPoly k))`. On that route the
convention-length equality gate and gamma narrowing are closed, exactly three tag/index/padding
read-value tests remain, and concrete `ContentAccepts` non-vacuity is closed. D1b conditionally
repackages a supplied `ContentVerifierBridge`, but constructs no bridge instance. Wrapper-level
`L'` padding invariance, the concrete verifier bridge, runtime/advice enforcement, and
`NoPolynomialBoundedSearchSolver` remain open.

Part A G1 now supplies a fixed three-state terminator scan after the content
tag gate. Under a successful tag-gate handoff, its machine verdict is exactly
`contentHeader?` presence; independently, the semantic factorization gates on
that same presence predicate. This is an infrastructure boundary only: payload
decoding, target materialization, capped-size execution, and the concrete
verifier bridge remain open.

Part A G2a now supplies the six-state gamma-anchor shuttle after G1. On the
G1-success branch it has an exact first-terminal clock, stays between cell 6
and the physical terminator without clamping, and changes no cell except the
recoverable marker at cell 7; on G1 rejection it remains at the physical content
blank and rejects in one step. The pnp4 bridge identifies its verdict with
`contentHeader?` presence and proves a proof-level logical restoration that
writes literal `some false` at cell 7. This is not executable restoration:
physical restoration remains G2b work. G2a does not traverse or decode the
payload and proves no semantic-acceptance claim.

Part A G2g adds an infrastructure-only semantic bridge for the later
physical-false gamma-payload path. It proves that the exact payload window
`[9 + zeros, 9 + 2 * zeros)` yields
`VirtualZeroTailReader.allZeroSlice? = some true` at logical length `a + m`,
and conjoins that fact with the existing G2f restored-tape `qDone` endpoint
under the same trace hypotheses. The result is a one-way shared-hypothesis
consequence, not a machine-verdict equivalence, semantic acceptance,
dispatcher correctness, complete parser behavior, or P-vs-NP mainline
progress.

Part A G2j adds the matching cleaned-pending strict-reader bridge. Positive
width scans return `none` exactly on logical non-fit; fitting scans return
`some false` exactly when a scanned `padRead` is true. The physical-true and
first-virtual cleanup endpoints are paired one-way with `some false` and
`some true` respectively for arbitrary fitting `T`; the first-virtual scan at
physical `T = a + m` is exactly `none`. All pending outcomes, plus the G2g zero
case, are specialized to the common frozen window `2 * (a + m) + 1`. This does
not assert endpoint iff semantics, dispatch, parser acceptance, payload decode,
or a cross-machine clock, and is infrastructure rather than mainline progress.

Part A G2n adds the dependency-closed total endpoint bridge at that same shared
window. Under a matching tag, the fixed dispatcher reaches `qAllZero` iff some
decoded gamma width has an exact `some true` all-zero payload scan, reaches
`qHasOne` iff the analogous scan is `some false`, and reaches `qReject` iff
gamma decoding fails; header failure is additionally conjoined in a narrow
corollary. Width zero is included. These are endpoint/reader propositions only:
they do not expose decoded header values or payload naturals, and assert no TM
acceptance, parser correctness, untagged behavior, uniform head, cross-machine
clock, or P-vs-NP mainline progress.

Part A G2o exposes those header values and payload naturals in
`ContentFixedGammaPayloadDispatcherHeaderValueBridge`, with seven public
theorems. The reader iffs have no fit hypothesis: a strict payload
`readNatBE` is `some 0` iff the same window's `allZeroSlice?` is `some true`,
and the scan is `some false` iff the read is `some payload` with
`0 < payload`. With no premise at all,
`contentHeader? z = some (n, consumed)` iff, for some `zeros` and `payload`,
the physical scan gives `gammaZeros? z = some zeros`, the payload read at
`2 * N + 1` over `[9 + zeros, 9 + 2 * zeros)` is `some payload`,
`n + 1 = 2 ^ zeros + payload`, and `consumed = 2 * zeros + 1`. From the single
premise `contentInput? codec z = some pr`, for any codec, a one-way theorem
returns some `consumed` with `contentHeader? z = some (pr.1, consumed)` and
`pr.2.n = pr.1`, so on a successful parse the parsed target equals the header
target; the gamma width `zeros` is identified with neither. Under only a
matching tag, the dispatcher at the common deadline is in `qReject` iff the
header is absent, in `qAllZero` iff the header is `(n, 2 * zeros + 1)` with
`n + 1 = 2 ^ zeros`, and in `qHasOne` iff it has that shape with
`2 ^ zeros < n + 1`; width zero and virtual payload cells are covered. These
are proof-level facts: they do not claim that the dispatcher stores or
materializes `n` or the payload or that any machine executes the parser, and
assert no content-language acceptance, untagged behavior, uniform head, clock
composition, `ContentVerifierBridge`, advice freedom, NP membership, or P-vs-NP
mainline progress.

Part A G2p-a adds `ContentFixedGammaTerminatorScratchBootstrapBridge` over the
pnp3 fixed terminator-to-scratch bootstrap. That machine retags the actual
dispatcher deadline configuration and writes a literal `true` at scratch cell
`a + m + 1`. The bridge has two public theorems at the bootstrap's length-only
deadline `2 * (a + m)`. Under a matching tag, `qReject` holds iff
`contentHeader? = none`. If additionally `contentHeader? z = some (n, consumed)`,
then for some `zeros` with `consumed = 2 * zeros + 1` and
`2 ^ zeros ≤ n + 1 < 2 ^ (zeros + 1)`, the endpoint is `qTerm` at head
`8 + zeros` with the scratch tape, and cell `a + m + 1` holds
`(n + 1).testBit zeros`, the leading binary digit of `n + 1`. Only that digit
reaches the scratch register; the shuttle crosses the payload cells, but neither
decodes nor copies their digits. This asserts
no parser execution, content-language acceptance, untagged behavior, clock
composition, or P-vs-NP mainline progress.

Part A G2p-b adds `ContentFixedGammaTargetFirstPayloadBridge` over the pnp3
fixed first-payload machine. That machine retags the actual bootstrap deadline
configuration and copies the first gamma payload bit to target cell
`a + m + 2`: a physical bit as itself, or the virtual zero when the payload cell
`9 + zeros` is the boundary `a + m`. The bridge proves two one-way theorems at
the machine's length-only deadline `3 * (a + m)`, under a matching tag. First,
suppose `contentHeader? z = some (n, consumed)` with `0 < n` and
`a + m + 2 < tapeLength (pairLength a m) B`. Then for some `zeros > 0` with
`consumed = 2 * zeros + 1` and `2 ^ zeros ≤ n + 1 < 2 ^ (zeros + 1)`, the
endpoint is `qDone` at head `7`. Cells `a + m + 1` and `a + m + 2` hold
`(n + 1).testBit zeros` and `(n + 1).testBit (zeros - 1)`. Second, for the
header `(0, 1)` the endpoint keeps the one-digit register of `1`, with no room
premise. The room premise is not implied by the header (it fails at
`a = B = 0`). The remaining payload
digits, the decrement to `n`, a `qReject` classification (unlike G2p-a, since
without room there is no endpoint theorem to invoke), the machine's exact
first-arrival clock, clock composition, and `ContentVerifierBridge` are not
provided, and this is not P-vs-NP mainline progress.

Part A G2p-c adds `ContentFixedGammaTargetSecondPayloadBridge` over the pnp3
fixed second-payload machine, at that machine's length-only, *phase-local*
deadline `2 * (a + m)`. It has four public theorems, all one-way out of a
decoded `contentHeader? = some …` and none with a converse; only the last three
reach a machine conclusion, because the first is machine-free.
`header_digits` is generic and machine-free: it takes one hypothesis, a decoded
header `contentHeader? z = some (n, consumed)` for an arbitrary
`z : PrefixBitVec N`, and returns a gamma width `zeros` with
`consumed = 2 * zeros + 1`, `2 ^ zeros ≤ n + 1 < 2 ^ (zeros + 1)`,
`(n + 1).testBit zeros = true`, and, for every `t < zeros`, the payload cell
`9 + zeros + t` read through the decoder's own virtual zero tail
(`(physicalSymbol z (9 + zeros + t)).getD false`) equal to
`(n + 1).testBit (zeros - 1 - t)`. The other three are concrete and carry a
matching tag. With `3 ≤ n` and the exact room
`a + m + 3 < tapeLength (pairLength a m) B` (four hypotheses), the endpoint is
`qDone` at head `7` on `secondPayloadTape` and cells `a + m + 1`, `a + m + 2`,
`a + m + 3` hold `(n + 1).testBit zeros`, `(n + 1).testBit (zeros - 1)`,
`(n + 1).testBit (zeros - 2)` for some `zeros ≥ 2`. With `consumed = 3` and the
G2p-b room (three hypotheses) the two-digit G2p-b register survives and every
allocated cell past `a + m + 2` stays blank. With the header `(0, 1)` (two
hypotheses) the one-digit G2p-a register survives, with no room premise. Given a
decoded header the premise `3 ≤ n` is exactly `2 ≤ zeros`, since the exported
bounds make `zeros` the index of the leading digit of `n + 1`; room, by
contrast, is not implied by the header and fails whenever `a + B ≤ 1`. The three
concrete header hypotheses are jointly exhaustive over decoded headers —
`zeros = 0` forces `(0, 1)`, `zeros = 1` forces `consumed = 3`, `2 ≤ zeros`
forces `3 ≤ n` — with the last two branches conditional on their explicit room.
`deadline` and `exactClock` are phase-local: `startConfig` retags the actual
G2p-b endpoint and embeds the earlier phases' steps, which neither clock counts.
No `qReject` theorem is restated here: the one-way
`contentHeader? = none → qReject` direction is already room-free from the
imports, while the `qReject ↔ contentHeader? = none` equivalence would need the
room premise. Parser execution, `contentInput?`, `ContentAccepts`, language
acceptance from `qDone`, clock composition, the remaining `zeros - 2` digits,
the decrement to `n`, and `ContentVerifierBridge` are not provided, and this is
not P-vs-NP mainline progress.

Part A G2p-g adds `ContentFixedGammaTargetPayloadExhaustionBridge` over the pnp3
G2p-f `FixedGammaTargetPayloadExhaustion`, the companion that slice deferred. It
has five public theorems, all one-way and none with a converse. Three are
machine-free. `exhaustion_register_digits` (one hypothesis, a decoded header
`contentHeader? (Fin.append x w) = some (n, consumed)`) gives a width `zeros`
with `consumed = 2 * zeros + 1`, `2 ^ zeros ≤ n + 1 < 2 ^ (zeros + 1)`, the
register equation `registerBit x w zeros j = (n + 1).testBit (zeros - j)` at
every `j ≤ zeros`, the fact that `n + 1` has no bit above `zeros`, and the
**virtual-tail** conjunct: for `1 ≤ j ≤ zeros` with `a + m ≤ 8 + zeros + j` both
the register digit and `(n + 1).testBit (zeros - j)` are `false`, so
`registerBit`'s padding of a payload cell that has left the word and the
decoder's virtual zero tail agree. `register_determines_target` (four
hypotheses) adds that those digits determine `n + 1` uniquely among values with
no bit above `zeros`; it is arithmetic, not a decoding step any machine
performs. `room_iff_target_bound` (two hypotheses) identifies
`n + 1 < 2 ^ (a + B + 1)`, `zeros ≤ a + B` and the G2p-e room
`a + m + 1 + zeros < tapeLength (pairLength a m) B`. The other two reach the
G2p-f endpoint at `totalClock (a + m) zeros`, under a matching tag, a decoded
header (or a successful parse), `3 ≤ n` and that room — four hypotheses each:
`qDone` at head `7` on `finishTape`, every register cell `a + m + 1 + j` holding
the matching digit, every virtual-tail cell `some false` with the matching
parsed `false`, those cells pinning the target, and the endpoint persisting at
every later time. `exhausted_register_parsed_target` takes a successful
`contentInput? codec (Fin.append x w) = some pr` for an arbitrary codec and
exports `pr.2.n = pr.1`, so the register digits are digits of the target that
`ContentAccepts` feeds to the search relation. The register holds the digits of
`n + 1`, the encoded gamma integer whose bits physically occur in the header, not
of the decoded target `n` the parser returns; room is carried, not derived,
and is not shown necessary. Parser execution, the decrement to `n`, any
converse, a footprint theorem, the degenerate widths `zeros ≤ 1` on the machine
side, a malformed-gamma branch, first arrival from `startConfig`, clock
composition, `ContentAccepts`, and `ContentVerifierBridge` are not provided, and
this is not P-vs-NP mainline progress.

Part A G2r adds `ContentFixedGammaTargetRegisterDecrementBridge` over the pnp3
G2q `FixedGammaTargetRegisterDecrement`, the companion that slice deferred. It
adds no machine either: the run is G2q's `register_decremented`, unchanged. Its
content is one instantiation — G2q's `decBit_sub_one` is arithmetic about an
arbitrary `v` whose bits are the incoming register's digits and which has no bit
above `zeros`, and G2p-g's `exhaustion_register_digits` proves both for
`v = n + 1`, whence `v - 1 = n`. Five public theorems, all one-way. Three are
machine-free: `decremented_register_digits` (one hypothesis, a decoded header)
gives a width `zeros` with `consumed = 2 * zeros + 1`,
`2 ^ zeros ≤ n + 1 < 2 ^ (zeros + 1)`, `borrow x w zeros ≤ zeros`, the equation
`decBit x w zeros (borrow x w zeros) j = n.testBit (zeros - j)` at every
`j ≤ zeros`, and the fact that `n` has no bit above `zeros`;
`decremented_register_determines_target` adds that those digits determine `n`
uniquely among values with no bit above `zeros`;
`decrement_room_iff_target_bound` identifies `n + 1 < 2 ^ (a + B)`,
`zeros + 1 ≤ a + B` and G2q's tape form
`a + m + 2 + zeros < tapeLength (pairLength a m) B`, shows this room implies the
G2p-g room `n + 1 < 2 ^ (a + B + 1)`, and shows it fails at `zeros = a + B` —
that the weaker one can still hold there is no conjunct of it, but a literal word
in the surface probes. The other two reach the G2q endpoint at
`decClock (a + m) zeros (borrow x w zeros)`, under a matching tag, a decoded
header (or a successful parse), `3 ≤ n` and that stronger room: `qDone` on the
stopping cell with tape `decTape`, every register cell `a + m + 1 + j` holding
`some (n.testBit (zeros - j))`, those cells pinning `n`, every cell outside the
register unchanged from `finishTape`, the incoming `finishTape` register cells
still reading `n + 1`, and the endpoint persisting at every later time.
`decremented_register_parsed_target` takes a successful `contentInput?` parse for
an arbitrary codec and exports `pr.2.n = pr.1`, so the decremented digits are the
digits of the actual target `ContentAccepts` feeds to the search relation. The
gamma leading-digit convention is **not** restored: the borrow can clear the top
cell, and a surface probe exhibits that on a literal word. Parser execution, any
converse, a footprint theorem, the degenerate widths `zeros ≤ 1` on the machine
side, a malformed-gamma branch, clock composition, `ContentAccepts`, and
`ContentVerifierBridge` are not provided, and this is not P-vs-NP mainline
progress. First arrival is not provided either: the endpoint is stated at exactly
`decClock (a + m) zeros (borrow x w zeros)` with persistence afterwards, and no
conjunct says `qDone` is not entered earlier — minimality is G2q's
`decrement_strict`, neither instantiated nor restated here.

Part A G2t adds `ContentFixedGammaTargetUnaryCountdownBridge` over the pnp3 G2s-a
`FixedGammaTargetUnaryCountdown`, the companion that slice deferred. It adds no
machine either: the run is G2s-a's `first_round`, unchanged. Its content is again
one instantiation — `first_round` is stated for a positive `v` whose bits are the
decremented register's digits and which has no bit above `zeros`, no pnp3 theorem
supplies one, and G2r's `decremented_register_digits` proves both facts for the
decoded target `n` while `3 ≤ n` gives positivity, so `v := n`. Three public
theorems, all one-way. `countdown_room_iff_target_bound` (two hypotheses, a decoded
header and a decoded width) identifies `2 * (n + 1) < 2 ^ (a + B)`,
`zeros + 2 ≤ a + B` and G2s-a's tape form
`a + m + 3 + zeros < tapeLength (pairLength a m) B`, shows this room implies G2q's
`n + 1 < 2 ^ (a + B)`, and shows that at the boundary width `zeros + 1 = a + B`
G2q's holds while this one fails — both halves stated and proved, where the G2r
analogue stated only the failing half and left the other to a probe. The other two reach the G2s-a entry at `d + 2` steps and its
first round at `firstClock zeros d = 2 * zeros + d + 9`, under a matching tag, a
decoded header (or a successful `contentInput?` parse for an arbitrary codec, which
also exports `pr.2.n = pr.1`), `3 ≤ n` and that room: `qLoop` on the separator blank
`a + m + 2 + zeros` at both times, the entry register holding the decoded target
`n`, the exit register holding `n - 1`, one **mark** at `a + m + 3 + zeros`, and six
cell conjuncts covering every index of the endpoint tape, the exit register cells
pinning `n - 1`. This is one round: iteration, composed clocks, the lane fence, the
exhaustion, and every converse stay deferred, and there is deliberately **no
persistence conjunct** — `qLoop` does not absorb, so each endpoint is the
configuration at exactly its stated time. The room allocates the first lane cell and
is not a bound on the countdown; a target too large for the budget would run the
lane off the tape, which is a timeout and neither verdict. The gamma leading-digit
convention stays destroyed. Parser execution, first arrival, a footprint theorem,
the degenerate widths `zeros ≤ 1` on the machine side, a malformed-gamma branch,
`accepts`, `ContentAccepts`, language membership, clock composition, and
`ContentVerifierBridge` are not provided, and this is not P-vs-NP mainline progress.

Part A G2v adds `ContentFixedGammaTargetUnaryCountdownIterationBridge` over the pnp3
G2u `FixedGammaTargetUnaryCountdownIteration`, standing to it exactly as G2t stands to
G2s-a. It adds no machine, no state and no table row: the run is G2u's
`register_drained`, unchanged. Its content is again one instantiation — that theorem is
stated for a universally quantified `v` whose bits are the decremented register's
digits, its own probes use the hand-picked literals `24` and `3`, and G2r's
`decremented_register_digits` proves both digit facts for the decoded target `n`, so
`v := n`. Four public theorems, all one-way.
`countdown_width_eq_gammaZeros` (two hypotheses, a decoded header and a decoded width)
identifies the physical width `FixedContentGammaTerminator.gammaZeros?` reads off the
word with the canonical `gammaZeros n = bitLength (n + 1) - 1` the layout convention
computes from the decoded target, by exponent uniqueness on
`2 ^ zeros ≤ n + 1 < 2 ^ (zeros + 1)`; both widths are already functions of data, so
nothing is extracted from a proof. `countdown_drain_cap_iff_machine_room` (the same
two) states the explicit lane cap `n ≤ F` and G2u's room
`gammaZeros n + 2 + F ≤ a + B` in its width and tape forms, and the **one** direction
that holds: cap and room imply G2t's first-round room `2 * (n + 1) < 2 ^ (a + B)`,
never the converse, which
`probe_countdown_drain_room_strictly_stronger` refutes on a literal split at every `F`
the cap admits. The other two reach the absorbing `qDone` at
`fullClock zeros d n` under a matching tag, a decoded header (or a successful
`contentInput?` parse for an arbitrary codec, which also exports `pr.2.n = pr.1`),
`3 ≤ n`, the cap and the room: the entry register holds `n`, the endpoint register is
all `some false`, exactly `n` **marks** fill `[a+m+3+zeros, a+m+3+zeros+n)`, the lane
is blank beyond them, and the endpoint persists. `3 ≤ n` reaches `2 ≤ zeros`; G2u's
drain needs no positivity, so unlike G2t nothing here uses `1 ≤ n`.

Part A G2w-a adds `ContentCountdownLinearCap`, which supplies a value for `F` from
semantics rather than from parsing. **No** theorem bounds the target from parser
success alone, and none is claimed — the source is virtually zero-padded, so the
strict parser's returned target carries no bound on the physical length. Content
*acceptance* does, at the concrete `treeCircuitWitnessCodec (thresholdPoly k)`:
`contentSemanticAccepts_parsed_target_le_length` gives `pr.2.n ≤ N` for
`z : PrefixBitVec N`, by `instanceSize_lt_treeMCSPPrefixM` when the target's convention
length fits and by FEAS-0's
`contentAccepts_parsed_tableLen_le_of_header_target_wide` when it does not, which
forces `2 ^ pr.2.n ≤ N`. Its contrapositive
`contentSemanticAccepts_eq_false_of_length_lt_parsed_target` says that a successful
parse with `N < pr.2.n` makes the frozen Boolean checker reject;
`contentSemanticAccepts_parsed_target_le_pair_length` restates the bound at the split
`Fin.append x w`, whose `N` is the compacted content length `a + m` of the fixed-phase
tape ABI; and `countdown_drained_accepted_content` runs G2v's drain at the derived cap
`F := a + m`, carrying G2v's room unchanged.

Part A G2w-b closes the remaining free budget in the same module, by *choosing* it at
`B := polyClock 3 (PairEncoding.pairLength a m) = (2 * a + 1 + m) ^ 3 + 3`.
`concatBitstring_eq_append` is the word-shape bridge it needs and nothing more — the
interface's `concatBitstring x w` and the fixed-phase `Fin.append x w` are the same
function of the two blocks, with no parse, acceptance, header, codec or machine in the
statement. `countdown_drained_accepted_content_at_polyClock` then has exactly **three**
proposition hypotheses — the successful parse, the Boolean acceptance and
`3 ≤ pr.2.n` — and no others: no tag premise (acceptance supplies it through
`fixedTag_semantic_factorization`), no cap, no room, no free `B`, no free `F`, no
runtime premise and no correctness premise. Acceptance caps the target at `a + m`,
`gammaZeros n ≤ n` caps the width, `borrow_pins` caps the borrow, and the cube dominates
the expanded quadratic clock
`fullClock zeros d n = d + n*n + n*(2*zeros+6) + 2*zeros + 7`, so both the room and
`fullClock zeros d pr.2.n ≤ B` come out as **conclusions**; the endpoint is transported
from `fullClock` to exactly `B` steps by G2v's persistence conjunct. The surface probe
`probe_countdown_polyClock_accepted_target_three` inhabits the three premises jointly,
on GATE-0's zero-prefix query for the all-false table on three variables plus its
certificate, at the pinned target `3` and width `2`, and reads the `qDone` endpoint state
back after exactly `B` steps. The exponent `3` is sufficient and
is **not** shown least; the same `B` serves as both the tape budget and the step count,
which is an instantiation choice rather than a theorem; and `polyClock` here is an
arithmetic value, not a runtime, `DecidesWithin`, `UniformP` or `NP` claim.

None of these slices takes the **fence**. `F` is a parameter of every G2v statement, the tape
is the unchanged canonical `loopTape` — blank at `a+m+3+zeros+F` — and nothing here
lays a cutoff cell, adds a `qOverflow` state, or shows any execution theorem surviving
an installed `some false` in the lane. The lane is still uncapped in the machine: a
target too large for the budget runs off the end of the tape and sticks, which is a
timeout and neither verdict, and G2w-a's bound identifies a legitimate cap value rather
than a mechanism enforcing one. In G2v and G2w-a the room is **carried, never
derived** — `B` is a free budget in both — while G2w-b derives it, but only by
*instantiating* `B` at the cube: that room is sufficient only, and no budget, cubic or
otherwise, is shown necessary. The more expensive `boundedContentCap` alternative — a
polynomial lane from `boundedContentInput?` success instead of a linear one from
acceptance — is documented
and **not implemented**. Persistence is not first arrival (`qDone` absorbs). No
converse is stated in either direction: not endpoint-to-parse, and not
`pr.2.n ≤ N`-to-acceptance. Parser execution, a footprint theorem, the degenerate
widths `zeros ≤ 1` on the machine side, a malformed-gamma branch, `accepts`,
`AcceptsAt`, language membership, advice freedom, `NP` membership, clock composition and
`ContentVerifierBridge` are not provided, and none of these three slices is P-vs-NP
mainline progress.

The Part A fixed-phase chain strings its phases together across **seventeen** handoffs, and
until now every one of them was proof-level: each phase's `startConfig` retags the previous
phase's run at a length-only deadline, and no finite table performs the control switch.
Part A G2x executes **one** of those seventeen handoffs.
`ContentFixedGammaTargetDecrementCountdownBridge.lean` runs the pnp3 composed machine
`FixedGammaTargetRegisterDecrement.machine.seq FixedGammaTargetUnaryCountdown.machine` —
G2q's 7-state table followed by G2s-a's 11-state table as one closed 18-state table, built
by the new generic `UniformTM.seq` whose routed rows make a target `M₁.accept` enter
`M₂.start` in that same transition — under exactly G2w-b's three hypotheses at G2w-b's
budget. `decrement_countdown_drained_accepted_content_at_polyClock` concludes that the
composed run switches blocks at G2q's **first arrival** `decClock`, not at G2q's deadline,
is in neither composed verdict before it, is the countdown's landed `startConfig`
re-embedded at it, and is in the composed accept at exactly
`decClock + fullClock ≤ B`, at exactly `B` and at every later time, with the register
cleared and `pr.2.n` marks laid. The sixteen handoffs G2x leaves untouched stay proof-level
identifications — the composed `startConfig` still embeds every earlier phase — no first arrival
of the composed accept is proved, the lane is still unfenced, the composed accept is the
countdown's phase-local `qDone` rather than language acceptance, the V1 machine model is
not the legacy `TM` the bridge interface names, and this is not P-vs-NP mainline progress.

Part A G2y executes the handoff immediately before it, so **two** of those seventeen were performed
at that slice. Four earlier chain handoffs were later executed by G2z, G3a, G3c and G3e, taking the
count to six. `ContentFixedGammaTargetLoopDecrementCountdownBridge.lean` runs the
pnp3 composed machine `FixedGammaTargetPayloadRound.machine.seq
FixedGammaTargetDecrementCountdown.machine` — G2p-d's 22-state payload-round table followed by the
whole G2x 18-state composite as one closed 40-state table, whose routed row `qFin`-on-`some false`
(index `19` → `22`) is the new handoff H16 and whose index-`26` → `29` row is G2x's H17, inherited —
under exactly the same three hypotheses at the same budget.
`loop_decrement_countdown_drained_accepted_content_at_polyClock` concludes that the composed run
switches blocks at the payload loop's **first arrival** `totalClock`, not at G2q's length-only
deadline, is in neither composed verdict before it, is G2x's landed `startConfig` re-embedded at it,
and is in the composed accept at exactly `totalClock + composedClock ≤ B`, at exactly `B` and at
every later time, with tape `loopTape B x w zeros 0 pr.2.n` — one equality from which the cleared
register and the `pr.2.n` marks follow; G2x's cell-by-cell conjuncts are not restated. The
exported length bound is `11 ≤ N`, stronger than G2x's `3 ≤ N`. The fifteen earlier handoffs
remain proof-level identifications — the composed `startConfig` still embeds every earlier phase —
no first arrival of the composed accept is proved (the first arrival proved is the loop's, inside
the left block), the lane is still unfenced, the composed accept is still the countdown's
phase-local `qDone` rather than language acceptance, and, like G2x, this is infrastructure, not
P-vs-NP mainline progress; it makes no `P ≠ NP` claim.

**Part A G2z** applies the same combinator a third time, one block further left:
`ContentFixedGammaTargetMarkersLoopDecrementCountdownBridge` runs **one** machine — G2p-d's
14-state marker-preamble table followed by the whole G2y 40-state composite as one closed 54-state
table, whose four routed rows into `qDone` (index `14`) are the new handoff H15 and whose
index-`33` → `36` and `40` → `43` rows are G2y's H16 and G2x's H17, inherited — under exactly the
same three hypotheses at the same budget.
`markers_loop_decrement_countdown_drained_accepted_content_at_polyClock` concludes that the composed
run switches blocks at the marker preamble's **first arrival** `exactClock zeros = zeros + 7`, not at
the preamble's length-only deadline `N`, is in neither composed verdict before it, is G2y's landed
`startConfig` re-embedded at it, and is in the composed accept at exactly
`exactClock zeros + chainClock N zeros d pr.2.n ≤ B`, at exactly `B` and at every later time, with
tape `loopTape B x w zeros 0 pr.2.n`. G2z needs no new first-arrival theorem: the preamble's
`markers_installed`, `markers_strict` and `exactClock_le_deadline` are all landed. Of its four
routed H15 rows the pnp3 fixtures exercise the two that `qSrcB` selects, the other two being the
width-zero and width-one dispatch that `2 ≤ zeros` excludes; the pnp3 module also exercises
the **first routed reject** of the chain composition, on a malformed gamma, which is no converse and
characterises no parsed target. The fourteen earlier handoffs remain proof-level identifications —
the composed `startConfig` still embeds every earlier phase — no first arrival of the composed
accept is proved (the first arrival proved is the preamble's, inside the left block), the lane is
still unfenced, the composed accept is still the countdown's phase-local `qDone` rather than
language acceptance, and, like G2x and G2y, this is infrastructure, not P-vs-NP mainline progress;
it makes no `P ≠ NP` claim. The fourteen-and-three counts in this G2z paragraph are the ones that
slice left; H14 has since been taken by G3a.

**Part A G3a** applies the same combinator a fourth time, one block further left:
`ContentFixedGammaTargetSecondPayloadMarkersLoopDecrementCountdownBridge` runs **one** machine —
G2p-c's 14-state second-payload table followed by the whole G2z 54-state composite as one closed
68-state table, whose *single* live routed row `qScanLeft`-on-blank (into index `14`) is the new
handoff H14 and whose index-`23`/`24` → `28`, `47` → `50` and `54` → `57` rows are G2z's H15, H16
and H17, inherited — under exactly the same three hypotheses at the same budget.
`second_payload_markers_loop_decrement_countdown_drained_accepted_content_at_polyClock` concludes
that the composed run switches blocks at G2p-c's **first arrival**, exported as the
length-dependent `2N − 7`, not at G2p-c's length-only deadline `2N`, is in neither composed verdict
before it, is G2z's landed `startConfig` re-embedded at it, and is in the composed accept at exactly
`(2N − 7) + exactClock zeros + chainClock N zeros d pr.2.n ≤ B`, at exactly `B` and at every later
time, with tape `loopTape B x w zeros 0 pr.2.n`. The target tracked throughout is the parsed
`pr.2.n`. G3a needs no new first-arrival theorem: G2p-c's `second_payload_exact`,
`second_payload_strict` and `exactClock_le_deadline` are all landed. `3 ≤ pr.2.n` forces
`2 ≤ gammaZeros pr.2.n`, so an accepted parsed target reaches only G2p-c's positive-width branch,
whose endpoint is extensional in its three source shapes; the pnp3 module additionally states the
same switch at the two degenerate decoded widths (first arrivals `3` and `5`), for which **nothing
downstream is claimed**, and transports G2p-c's malformed rejection into the composed reject in the
forward direction only, which is no converse and characterises no parsed target. **Four of the
seventeen** handoffs were performed by a finite table when this slice landed; the thirteen earlier
ones remained proof-level identifications — the composed `startConfig` still embeds every earlier
phase — the next one down was blocked on a missing G2p-b first-arrival theorem, which Part A G3b
supplied in pnp3; G3c has since used it to build that next composition. No first arrival of the
G3a composed accept is proved (the first arrival proved there is G2p-c's, inside the left block),
the lane is still unfenced, the composed accept is still the countdown's phase-local `qDone` rather
than language
acceptance, the machine is a V1 `UniformTM` on `Option Bool` cells against `pairLength a m` and not
the legacy `TM` with a `runTime` field that `ContentVerifierBridge` names, and, like G2x, G2y and
G2z, this is infrastructure, not P-vs-NP mainline progress; it makes no `P ≠ NP` claim. The
four-and-thirteen counts in this G3a paragraph are the ones that slice left; H13 has since been
taken by G3c and H12 by G3e, as the paragraphs below record.

**Part A G3c** applies the same combinator a fifth time, one block further left:
`ContentFixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdownBridge` runs **one**
machine — G2p-b's 18-state first-payload table followed by the whole G3a 68-state composite as one
closed 86-state table, whose *single* live routed row `qSeekAnchor`-on-blank (into index `18`) is
the new handoff H13 and whose index-`29` → `32`, `41`/`42` → `46`, `65` → `68` and `72` → `75` rows
are G3a's H14, H15, H16 and H17, inherited — under exactly the same three hypotheses at the same
budget. `first_payload_second_payload_markers_loop_decrement_countdown_drained_accepted_content_at_polyClock`
concludes that the composed run switches blocks at G2p-b's **first arrival**, exported as the
length- and width-dependent `2N + zeros − 6`, not at G2p-b's length-only deadline `3N`, is in
neither composed verdict before it, is G3a's landed `startConfig` re-embedded at it, and is in the
composed accept at exactly `(2N + zeros − 6) + secondChainClock N zeros d pr.2.n ≤ B`, at exactly
`B` and at every later time, with tape `loopTape B x w zeros 0 pr.2.n`. The target tracked
throughout is the parsed `pr.2.n`. G3c needs no new first-arrival theorem: G2p-b's
`first_payload_exact`, `first_payload_strict` and `exactClock_le_deadline` are all landed by Part A
G3b. `3 ≤ pr.2.n` forces `2 ≤ gammaZeros pr.2.n`, so an accepted parsed target reaches only a
positive width, which is one branch of the pnp3 statement and whose endpoint is extensional in its
two source shapes; the pnp3 module additionally states the same switch at the one degenerate decoded
width (first arrival `6`), for which **nothing downstream is claimed**, and transports G2p-b's
malformed rejection into the composed reject in the forward direction only, which is no converse and
characterises no parsed target. **Five of the seventeen** handoffs were performed by a finite
table when this slice landed; the twelve earlier ones remained proof-level identifications — the
composed `startConfig` still embeds every earlier phase — the next one down, G2p-a's bootstrap into
G2p-b, needed no new first-arrival theorem either but was not built, no first arrival of the
composed accept is proved (the first arrival proved is G2p-b's, inside the left block), the lane is
still unfenced, the composed accept is still the countdown's phase-local `qDone` rather than
language acceptance, the machine is a V1 `UniformTM` on `Option Bool` cells against
`pairLength a m` and not the legacy `TM` with a `runTime` field that `ContentVerifierBridge` names,
and, like G2x, G2y, G2z and G3a, this is infrastructure, not P-vs-NP mainline progress; it makes no
`P ≠ NP` claim. The five-and-twelve counts in this G3c paragraph are the ones that slice left; H12
has since been taken by G3e below.

**Part A G3e** applies the same combinator a sixth time, one block further left again (the G3d slice
label is skipped here; the preceding composite is G3c):
`ContentFixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdownBridge`
runs **one** machine — G2p-a's 9-state scratch-bootstrap table followed by the whole G3c 86-state
composite as one closed 95-state table, whose *single* live routed row `qScanLeft`-on-blank (into
index `9`, writing back the gamma terminator the bootstrap had blanked as its return marker) is the
new handoff H12 and whose index-`24` → `27`, `38` → `41`, `50`/`51` → `55`, `74` → `77` and
`81` → `84` rows are G3c's H13, H14, H15, H16 and H17, inherited — under exactly the same three
hypotheses at the same budget.
`scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained_accepted_content_at_polyClock`
concludes that the composed run switches blocks at G2p-a's **first arrival**, exported as the
length- and width-dependent `2N − 11 − zeros`, not at G2p-a's length-only deadline `2N`, is in
neither composed verdict before it, is G3c's landed `startConfig` re-embedded at it — on the
restored terminator cell `8 + zeros` with G2p-a's whole `scratchTape`, the two projections G2p-b's
own `startConfig` carries, both also exported — and is in the composed accept at exactly
`(2N − 11 − zeros) + firstChainClock N zeros d pr.2.n ≤ B`, at exactly `B` and at every later time,
with tape `loopTape B x w zeros 0 pr.2.n`. The target tracked throughout is the parsed `pr.2.n`.
G3e needs no new first-arrival theorem: G2p-a's `strict_first_terminal` and `exactClock_le_deadline`
are landed, the latter with no premise at all. Unlike every earlier handoff in this chain, H12
needs **no width case and no room premise**: G2p-a's clock is `2N − 11 − zeros` at every decoded
width, the degenerate width zero differing only in the incoming G2m dispatcher head, and
`tapeLength` allocates G2p-a's scratch cell for every budget, so one pnp3 statement covers all
widths and there is no separate degenerate theorem. G2p-a's malformed rejection is transported into
the composed reject in the forward direction only, which is no converse and characterises no parsed
target. **Six of the seventeen** handoffs are now performed by a finite table; the eleven earlier
ones remain proof-level identifications — the composed `startConfig` still embeds every earlier
phase. Part A G3f's pnp3 `FixedGammaPayloadDispatcherFirstArrival` closes the first of the two
blockers on **H11**, from G2m's payload dispatcher into G2p-a: strict first arrival at any dispatcher
terminal, with equality to the deadline configuration. The second blocker remains: two non-reject
absorbing outcomes, `qAllZero` (its `machine.accept`) and `qHasOne`, of which `UniformTM.seq` routes
only the first. G3f adds no composite table, executed handoff or pnp4 bridge; H11 stays uncomposed
and the count stays **six of seventeen**. G3f is Infrastructure only. Part A G3g (pnp3 only) has
since removed that second blocker with the generic `UniformTM.mergeAccept` — `qHasOne` merged into
`qAllZero`, the merged dispatcher composed with the G3e composite as one 123-state table — and
executed H11 at the dispatcher's input-dependent strict first arrival, taking the count to **seven
of seventeen** with ten earlier handoffs still proof-level; the six-and-eleven counts in this G3e
paragraph are the ones that slice left. G3g builds **no pnp4 bridge**, so the three-hypothesis
chained run described here still starts at G3e's composite, and the standalone dispatcher's pnp4
semantics (`qHasOne_iff`, `qAllZero_iff`, `qReject_iff`) are unchanged. Part A G3h (pnp3 only) has
since executed **H10** as well — G2a's fixed 6-state gamma anchor prefixed to that G3g composite as
one closed 129-state, 387-row table, with no new row and no `mergeAccept`, switching at the anchor's
width-only strict first arrival `2*zeros+5` through the anchor's single live row targeting its accept —
taking the count to **eight of seventeen** with nine earlier handoffs still proof-level. G3h is
Infrastructure only and likewise builds **no pnp4 bridge**: no `ContentVerifierBridge`, no
raw-input acceptance, no advice-freedom claim and no P-vs-NP mainline progress; the standalone
phases' pnp4 semantics are unchanged and the chained run described here still starts at G3e's
composite. Part A G3i (pnp3 only) has since executed **H9** as well — G2's fixed 3-state gamma
terminator prefixed to that G3h composite as one closed 132-state, 396-row table, again with no new
row and no `mergeAccept`, switching at the terminator's width-only strict first arrival `zeros + 1`
through its single live row targeting its accept — taking the count to **nine of seventeen** with
eight earlier handoffs still proof-level; the eight-and-nine counts just given are the ones G3h left.
G3i is Infrastructure only and likewise builds **no pnp4 bridge**: no `ContentVerifierBridge`, no
raw-input acceptance, no advice-freedom claim and no P-vs-NP mainline progress; the standalone
phases' pnp4 semantics are unchanged, this chained run still starts at G3e's composite, and G3i's own
routed reject is forward-direction only and tag-gated. Part A G3j (pnp3 only) has since executed
**H8** as well — G1's fixed 15-state content tag gate prefixed to that G3i composite as one closed
147-state, 441-row table, again with no new row and no `mergeAccept`, switching at the gate's
length-only strict first arrival `3N + 7` (which is also the gate's own deadline, assembled here from
its landed `exact_terminal_contract` and `run_deadline`) through its single live row targeting its
accept — taking the count to **ten of seventeen** with **seven** earlier handoffs still proof-level;
the nine-and-eight counts just given are the ones G3i left. The terminator's reject took one live row
proved unique and the anchor's six pinned individually; the gate's is the target of many, so G3j
claims neither reject-row uniqueness nor a count and instead routes them all to the composed reject
by one quantified theorem. G3j is Infrastructure only and likewise builds **no pnp4
bridge**: no `ContentVerifierBridge`, no raw-input acceptance, no advice-freedom claim and no P-vs-NP
mainline progress; the standalone phases' pnp4 semantics are unchanged, this chained run still starts
at G3e's composite, and both of G3j's routed rejects are forward-direction only, the new
mismatched-tag one timed only from the gate's length-only deadline `3N + 7` on, with no claim about
any earlier time: on a nonempty content the gate's own rejection lands at `3N + j` for a mismatch
cell `j ≤ 7`, at or before that deadline, and on empty content (`N = 0`) at `2`; G3j derives no such
`j` from the mismatch hypothesis. Part A G3k (pnp3 only) has since executed **H7** as well — the fixed
4-state trailing-content-marker erasure prefixed to that G3j composite as one closed 151-state,
453-row table, again with no new row and no `mergeAccept`, switching at the phase's length-only
strict first arrival `N + 3` (which is also the phase's own clock, and which was already landed in
the shape `seq` consumes and hypothesis-free, so G3k's `handoff_exact` takes no hypothesis at all)
through its single live row targeting its accept, a row that writes `none` and so performs the marker
erasure itself — taking the count to **eleven of seventeen** with **six** earlier handoffs still
proof-level; the ten-and-seven counts just given are the ones G3j left. The marker-erase reject is the
first of the chain whose live list is both complete and plural: exactly two rows, proved the only ones
once both verdicts' own absorbing rows are excluded, each routed to the composed reject, and neither
ever taken out of G3k's start. G3k is Infrastructure only and likewise builds **no pnp4 bridge**: no
`ContentVerifierBridge`, no raw-input acceptance, no advice-freedom claim and no P-vs-NP mainline
progress; the standalone phases' pnp4 semantics are unchanged, this chained run still starts at G3e's
composite, and both of G3k's inherited routed rejects are forward-direction only, the mismatched-tag
one still timed only from the gate's length-only deadline on. Part A G3l (pnp3 only) has since
executed **H6** as well — the fixed 26-state, 78-row pair origin alignment prefixed to that G3k
composite as one closed 177-state, 531-row table, again with no new row and no `mergeAccept` —
taking the count to **twelve of seventeen** with **five** earlier handoffs still proof-level; the
eleven-and-six counts just given are the ones G3k left. In **forward execution order** H6 is the
first handoff of the chain whose live accept list is plural — the already-executed H11, further
right, routes six: **three** rows, the alignment states `10`, `11` and `12` on `none`,
proved the only ones targeting the phase's accept once the accept's own absorbing three are
excluded, each routed to index `26` keeping its own restoration write and its left move, a genuine
step onto the origin and **not** a clamp (the phase's sole left clamp is two steps earlier, at source
time `clock - 3`); which of the three fires on a given input is not claimed. Its
reject is the longest such list so far: every row targeting it is one of **21**, proved exhaustive in
that one direction and each
routed to the composed reject, none ever taken out of G3l's start. G3l's switch time
`(10a + 7)(a + m + 1) + 3a` is the **first in the chain to depend on the split lengths `a` and `m`
separately** — the landed ones are length-only in `N = a + m`, width-only in the decoded `zeros`, or
input-dependent — so
the composed clock is quadratic in `a` and it is **not** proved that the cubic budget still
dominates it. G3l is Infrastructure only and builds **no pnp4 bridge** either, on the same terms as
G3k.

**Part A G3t — Infrastructure: generic fenced raw execution through H17.**
`FixedGammaSuffixFootprint` and `FixedRawLengthFenceSuffix` extend the actual raw
execution of the unchanged 256-state `FixedRawLengthFence.prefixed` through
countdown entry, global state **245**, for arbitrary dependent words `x/w`, every
`B ≥ 2*R+2`, matching tag, decoded gamma width `zeros ≥ 2`, and the actual strict
dispatcher arrival `C/q`. Here `R=2*a+1+m` and `L=a+m`; the physical tape domain
remains `Fin (R+B+1)` throughout. The whole endpoint is
`fencedDecrementConfig`: head `L+1+zeros-borrow x w zeros`, complete `decTape`,
and the existing false fence at `P=3*R+2`. No transition, initializer, encoding,
allocation, or interpreter changes.

The trace proves `head ≤ 3*L < P` after installation through H17, preservation
of the literal false fence, and exclusion of both verdicts at every such time.
The cell theorem exposes every register digit, both adjacent blanks, and the
blank lane up to the fence. The exact clock is installation plus G3s's
`contentClock` plus `h17SuffixClock`; `h17_clock_bound` bounds it by
`h17Deadline R = 32*(R+1)^2`. `raw_fenced_h17_allocated` existentially produces
the actual dispatcher `C/q` at the unchanged `B=16*(R+1)^2`. This is a polynomial
prefix bound on the stated valid branch, not a whole-machine halting bound.

`ContentRawFencedDecrementBridge.raw_fenced_h17_parsed_target` fixes
`treeCircuitWitnessCodec (thresholdPoly k)` and the **same dependent `pr`** from
`contentInput?`. For `3 ≤ pr.2.n` and the explicit matching tag, it identifies
actual raw endpoint digits with `pr.2.n.testBit (zeros-j)`, including zero high
bits. It neither executes the parser nor supplies a different parsed witness.
Named full-proposition surfaces and direct axiom roots cover all public results.
The raw regressions derive the existing 2335-step overflow H17 endpoint via the
new generic theorem and cover width-two physical-zero, virtual, and positive
pending paths, including a strictly larger allocation.

G3t stops at nonterminal countdown entry 245. Generic **fenced countdown**,
including success at exact capacity and overflow rejection, remains open.
Remaining parser fields, GN program/serialization/start configuration and
witness checks, malformed-input rejection completeness, acceptance equivalence,
whole-verifier length-only resource domination, and operational advice freedom
remain open. The V1 Option-Bool/raw-pair model still needs its initialization,
alphabet/encoding, clock and verdict simulation into the legacy exact-step
Boolean `TM.accepts` model. `ContentVerifierBridge` is unconstructed; Part A is
unfinished. No `SearchMCSPWeakLowerBound`, `VerifiedNPDAGLowerBoundSource`, or
`NP_not_subset_PpolyDAG` obligation is reduced. This is Infrastructure, not
P-vs-NP mainline progress.

The following G3s record is historical; of its first open obligation G3t narrows
only the generic fenced H8–H17 preservation half, and the generic countdown
success/overflow dichotomy stays open exactly as stated there.

**Part A G3s — Infrastructure: generic fenced H1–H7 and one raw overflow rejection.**
The machine is unchanged: `FixedRawLengthFence.prefixed`, **256 states / 768 rows**,
start 0, accept 254, reject 255. No transition or runtime interpreter is added.
The generic and concrete results have different scopes.

`UniformTM.run_update_of_unvisited` proves locality for one unscanned tape cell.
`FixedRawLengthFenceContent` discharges its avoidance premise using all seven
existing phase footprints: every head through H7 is at most `R+1`, below the
installed fence `P=3*R+2`, where `R=pairLength a m=2*a+1+m`.
For arbitrary dependent words x/w and **every** `2*R+2 ≤ B`,
`raw_fenced_content_exact` starts from literal raw `initialConfig` and reaches
state 109, head `a+m`, the entire `fencedContentTape B x w`, at
`installClock R + contentClock a m`, with
`contentClock a m = 11*a*a+10*a*m+36*a+13*m+23`.
The tape has x followed by w, blanks elsewhere, and the installed false fence.
`raw_fenced_content_trace` preserves that fence and excludes both verdicts
through H7. Empty pairs are included (their raw encoding has length one).
`content_prefix_resources` discharges room and this prefix clock at the existing
`allocation R=16*(R+1)^2`; it is not a whole-machine resource theorem.

`FixedRawLengthFenceOverflowWitness` supplies the separate closed witness
`x=1`, `w=011001000000111111`, raw `011011001000000111111`, with
`a=1,m=18,N=19,R=21,B=45`: 67 allocated cells, false fence at 65, width 5.
The decremented register is 62; therefore the pre-H17 copied value is 63
(an arithmetic inference from the borrow-free decrement).
`overflow_values` proves the matching tag, gamma width, original dispatcher's
strict first terminal at C=21 in `qHasOne`, borrow zero and the actual digit
identities. This is not identification with a returned `contentInput?` object.
H11 executes the existing merged dispatcher, retaining its actual routing.

Installation ends at 1517; H1–H7 end at
1560/1564/1565/1573/1636/1979/2001. The concrete fenced H8–H17 boundaries are
2065/2071/2086/2107/2129/2166/2197/2209/2314/2335.
`overflow_h17_exact` proves state 245, head 25, whole `overflowTape 62 0`.
Countdown enters `qLoop` at 2337, completes 38 rounds at 4389 with register 24,
then decrements to **23** before scanning the fence. `overflow_prereject_exact`
proves state 251, head 65, whole `overflowTape 23 38` at 4442.
`overflow_reject_row` is the existing false-symbol write/stay row to reject 255;
`overflow_reject_exact s` proves the complete literal rejecting configuration
from raw `initialConfig` at **4443+s**, with persistence by `run_reject`.
`overflow_fence_trace` keeps the false fence and head at most 65 throughout
1517–4443. The final tape has tag cells 0–7, false zeros 8–12, blanks 13–17,
true terminator 18, blank 19, register `010111` at 20–25, blank 26,
exactly 38 true marks 27–64, false fence 65 and blank 66.

The finite proofs reduce segments of at most 64 suffix steps and 91 countdown
steps; the 105-step payload loop is split into 31/31/31/12. Whole configurations
are composed with `run_add` and existing `seq_run_right` embeddings, retaining
raw-length indices throughout. No monolithic 4443-step kernel reduction is used.
Surface probes separately check an empty raw pair, a theorem-derived mixed pair,
and phase-local last-mark/exhaustion/overflow boundaries. Those boundary probes
supply countdown configurations and are not additional raw-input capstones.
The intended generic boundary is strict: `v ≤ F` fits and `F < v` overflows.
That universal theorem is still open; the phase-local probes check its last-step
cases only. The raw overflow witness has F=38. Since **4443>B=45**, this is exact
execution, not `RejectsWithin ... 45`. Inherited left clamps remain; the suffix
is not claimed clamp-free. The unfenced drain theorem is never substituted for
a run on the installed fence.

The following obligations remain open, in order:

1. Generic fenced H8–H17 preservation and generic countdown success/overflow
   from the actual predecessor configuration; G3s proves only the stated raw witness.
2. Identify every field and dependent length of the **same** `pr` returned by
   `contentInput? codec z`: `pr.2.tag`, `.n`, `.x`, `.i`, `.p`, `.padBits`, `.pad`,
   with `codec := treeCircuitWitnessCodec (thresholdPoly k)` and `z := Fin.append x w`.
   `pr.2.n = pr.1` alone does not identify the executed register.
3. Build the dependent `GNProgram`, serialization and physical starting configuration
   from those fields and `contentWitness codec z pr.2.n`; complete gate/witness
   verification. Frozen GN work and GN-E2-4b donor-only status are unchanged.
4. Connect V1 Option Bool/pair execution to legacy Boolean/`concatBitstring`
   `TM.runConfig`, accounting for initialization, time, space and verdicts.
5. Prove whole-machine length-only polynomial allocation and clock, domination
   on every branch and operational advice freedom. Only the installed H1–H7 prefix
   has the new polynomial resource guarantee.
6. Prove the final acceptance equation for `contentSemanticAccepts`, including
   malformed-input rejection completeness and failed witness checks; timeout is not rejection.

`ContentVerifierBridge`, canonical NP witnesses, Part A completion,
`SearchMCSPWeakLowerBound` and `VerifiedNPDAGLowerBoundSource` remain open.
No pnp4 bridge or semantic acceptance theorem is added; its accepted-content
bridge remains at G3e. This is Infrastructure, not P-vs-NP mainline progress.

The following G3r record is historical; its then-open fence obligations are narrowed above.

**Part A G3r — Infrastructure: executed raw-length false fence and exact G3q handoff.**
`FixedRawLengthFence.machine` is a fixed **48-state / 144-row** three-symbol table,
start 0, accept 2, reject 3. For raw length R, it reads every bit, uses an origin
hole and a temporary tally, restores the input, erases the tally and accepts at head
zero with exactly one nonblank cell beyond the input: `some false` at `3*R+2`.
The endpoint has blank cells R and R+1, including R=0. The installation clock is
4 for R=0 and `3*R*R+9*R+5` otherwise. For every `2*R+2 ≤ B`,
`install_exact` proves complete configuration equality from literal raw
`initialConfig`; `install_trace` proves strict first terminal arrival, head
at most `3*R+2`, and no attempted boundary clamping. `installed_cells` states
the executed restoration and unique suffix marker. Insufficient-room probes
can clamp and accept with a misplaced marker; no all-budget result is claimed.

`allocation R = 16*(R+1)^2` supplies both room and a polynomial installation
deadline. No transition takes R, B, a parser result, target, proof or advice.
`prefixed = machine.seq G3q.machine` has **256 states / 768 rows**, start 0,
accept 254, reject 255. `raw_fence_handoff_exact` runs from literal raw input
at that allocation: at `installClock R+s` its whole configuration equals
G3q's actual s-step run from state 0, head zero and the installed fenced tape,
embedded at offset 48. At s=0 the composite is in state 48, neither verdict.
The raw `[true,false,true]` witness has R=3, B=256, time 59 and marker 11;
the full tape contains only cells 0=true, 1=false, 2=true and 11=false.

Review hypothesis freeze: `install_exact`, `install_trace`, `installed_cells`
and `fence_handoff_exact` require exactly `2*R+2 ≤ B`; the raw capstones
supply that inequality using `allocation R` and take no propositional premise.
Their execution is V1 `UniformTM.run`, not legacy `TM.runConfig`. The suffix
time `s` is arbitrary, with no suffix verdict or runtime bound asserted.
G3q's eight drain premises recorded below still concern its unfenced entry;
none supplies the missing fenced-entry preservation theorem.

At G3r the following obligations were open; G3s above narrows the first and the prefix resources:

1. Preserve the fence through H1–H17 and prove fenced countdown success and
   literal overflow rejection from the actual predecessor configuration.
   The existing G3q whole-tape drain theorem ends in an unfenced `loopTape`
   and cannot be substituted for this missing proof.
2. Identify every field of the **same** `pr` returned by `contentInput? codec z`,
   with `codec := treeCircuitWitnessCodec (thresholdPoly k)` and `z := Fin.append x w`:
   `pr.2.tag`, `.n`, `.x`, `.i`, `.p`, `.padBits`, `.pad`, and dependent lengths.
   The semantic fact `pr.2.n = pr.1` does not identify the executed register.
3. Build the actual dependent `GNProgram`, serialization and physical starting
   configuration from those fields and `contentWitness codec z pr.2.n`;
   complete gate/witness verification. An already encoded GN input supplies
   neither bridge. Frozen GN work and GN-E2-4b donor-only status are unchanged.
4. Connect V1 Option Bool/pair execution to legacy Boolean/`concatBitstring`
   `TM.runConfig`, including initialization, time, space and verdicts.
5. Prove explicit whole-machine length-only polynomial allocation and clock,
   domination on every branch and operational advice freedom. G3r's resource
   theorem covers installation alone, not the unbounded suffix time s.
6. Prove the final exact-step acceptance equation for `contentSemanticAccepts`,
   including malformed input and failed witness checks; timeout is not rejection.
`ContentVerifierBridge`, canonical NP witnesses, Part A completion,
`SearchMCSPWeakLowerBound` and `VerifiedNPDAGLowerBoundSource` remain open.
This is Infrastructure, not P-vs-NP mainline progress. The pnp4 accepted-content
bridge remains at G3e; no bridge instance or acceptance theorem is added.

The following G3q record concerns its original unfenced raw entry.

**Part A G3q — Infrastructure: executed sentinel → unchanged G3p handoff H1.**
`FixedPairSentinelCursorHoleTagRemovalShiftAlignmentCountdown.machine` is exactly
`FixedPairConcatSentinel.machine.seq
FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown.machine`:
**208 states / 624 rows**, start 0, accept 206, reject 207, G3p entry 7.
All seventeen **named operational handoffs** are now executed in this chain.
This closes H1 execution, not the semantic verifier or either P-vs-NP source obligation.

`raw_suffix` and `handoff_exact` start from literal raw `initialConfig` on every
raw word and every allocation budget B, including zero. With raw length
`R = pairLength a m = 2*a+1+m` and content length `L = a+m`, H1 executes at
`S0 = 2*R+1`, strictly confined to the five sentinel work controls before S0.
The complete successor has state 7, literal head zero and `sentinelTape`.
Raw cell R is blank; phase-local cell R is `some true`, even at B=0.
The three live H1 rows on arbitrary raw words are start/blank, back-false/blank,
and back-true/blank. Only the latter two occur on encoded pairs: they restore
the saved first **raw** bit by a write/stay transition. The three dead
accept-source rows are not additional live handoffs. The old verdict copies
5/6 are neither the start nor transition targets. Sentinel steps before H1
are clamp-free; the inherited removal-origin left clamp is retained.

H2 follows at `S0 + 2*a+2`, in state 12, head `2*a`, with the whole sentinel
tape unchanged. The pre-H2 row is state 9/nonblank → state 12/same bit/left,
from positive address `2*a+1`. H3/H4/H5/H6/H7 states are 15/24/31/57/61;
full suffix transport preserves the physical allocation `Config 208 R B`
through compaction and countdown. Time through H2 is `6*a+2*m+5 ≤ 3*R+2`.
Malformed syntax rejection is proved at `3*R+3+s` for every s, retaining
head `R+1` and the entire sentinel tape, under exactly `decodePair raw = none`
and **B>0**. A literal B=0 counterexample prevents dropping that restriction.
Both inherited content rejection implications persist at all later deadlines.

`raw_countdown_drained` retains exactly eight G3p premises: matching tag;
gamma width for `Fin.append x w`; dispatcher `StrictFirstTerminalAt B x w C q`;
`2 ≤ zeros`; `v ≤ F`; `zeros+2+F ≤ a+B`; identification of every register bit
with `decBit x w zeros (borrow x w zeros)`; and zero high bits of v.
It executes from raw input at `S0 + G3p.cursorChainClock C a m zeros d v`,
where `d = borrow x w zeros`, to literal accept 206, head `L+2+zeros`, the
whole `loopTape B x w zeros 0 v`, full configuration equality and persistence.
C/q/v/F are theorem-side run/value descriptions; no transition takes them.
The dispatcher q retains its dispatcher-control type and strict exclusion of
all earlier terminals; no successful-q premise is added. F is only a room
bound, and the bit premises do not supply a length-only polynomial cap.
The closed literal witness discharges all eight premises at
`a=8,m=9,B=22,zeros=4,C=18,q=qHasOne,d=0,v=F=24` and runs for
**3044 = 53+2991 steps**, accept 206, head 23, all 49 tape cells pinned.
Its H1–H7 times are 53/71/72/178/242/1832/1852; H5 head 27, H7 head 17,
and the removal-origin clamp occurs at 176. Register cells 18–22 are false,
23 blank, marks 24–47 true, and 48 blank. This is execution nonvacuity,
not `ContentAccepts` nonvacuity or first arrival of composed accept.

Explicitly open: runtime-enforced fence/cap and overflow rejection; full parser
fields, parser→GN encoding/configuration bridge, and gate/witness verification
(the frozen GN track remains separate); identification of the executed register
with the same authoritative dependent parser field `pr.2.n`; whole-machine
length-only polynomial runtime, budget domination, externally fixed polynomial
allocation, and operational advice freedom; V1 Option Bool/pair-encoded
`UniformTM` to legacy Boolean/`concatBitstring` `TM.runConfig` conversion with
time/space/acceptance accounting; content acceptance equivalence and rejection
completeness (timeout/nonacceptance is not rejection); `ContentVerifierBridge`,
canonical NP witnesses, `SearchMCSPWeakLowerBound`, and
`VerifiedNPDAGLowerBoundSource`. Since 3044>B=22, allocation is visibly not a
runtime deadline. The accepted-content pnp4 bridge remains at G3e; no new
pnp4 bridge instance is supplied. This is Infrastructure, not P-vs-NP mainline progress.

The following G3p record is historical (sixteen executed, H1 then remaining).

**Part A G3p — Infrastructure: executed cursor → unchanged G3o handoff H2.**
`FixedPairSeparatorCursorHoleTagRemovalShiftAlignmentCountdown` composes the
unchanged five-state `FixedPairSeparatorCursor` with G3o using `UniformTM.seq`:
**201 states, 603 rows**, start 0, accept 199, reject 200, tail entry 5.
**Sixteen of seventeen handoffs are executed; only H1 remains proof-level.**
The phase-local entry has head zero and the complete sentinelized pair tape;
it is not raw `initialConfig`. At strict first entry `T = 2*a+2`, H2 writes
back the nonblank lookahead bit unchanged and moves left to head `2*a`,
retaining the full `sentinelTape`. Both Boolean lookahead rows are live.
H3 follows one step later, erases the separator, and stays. H2 is clamp-free
on valid pairs, including empty pairs and `B=0`; the inherited removal origin
clamp remains at `T+(1+(Removal.clock a-2))`. The H3/H4/H5/H6/H7 controls are
8/17/24/50/54 at their inherited times plus T; H6 retains head zero and the
whole `alignedTape`. Every later G3o full configuration is transported.

`separator_cursor_countdown_drained` preserves exactly the eight inherited
premises: matching tag, gamma width, dispatcher strict first terminal,
width at least two, fence bound, allocation room, register-bit identification,
and zero high bits. The theorem-derived finite witness uses
`a=8, m=9, B=22, zeros=4, C=18, q=qHasOne, borrow=0, v=F=24` and reaches
**2991 = 18+2973 steps, accept 199, head 23**, with the complete
`loopTape 22 tag physWord 4 0 24` and persistence thereafter. Its 49-cell
layout has drained register cells 18–22, blank 23, marks 24–47, blank 48.
This witnesses the eight execution premises, not `ContentAccepts` nonvacuity,
runtime decoding of 24, or first arrival of composed accept. In particular,
2991 exceeds B=22: B allocates tape, not time.

Three blank source rows reject with unchanged head/tape. Malformed
sentinelized raw-word rejection requires **positive padding B>0**; that
restriction is not imposed on valid-pair or inherited rejection theorems.
Independent finite probes expose the B=0 malformed counterexample and the
valid empty pair's raw-entry rejection versus successful phase-local H2.
Both inherited rejection branches preserve their full endpoints and all
later persistence at the original deadlines, without a converse or
first-rejection claim.

H1, raw-input front-chain execution, runtime fence/cap and budget domination,
full parser/GN bridge, runtime selection of C/q/v, advice freedom, language
acceptance, `TM.runConfig` conversion, and `ContentVerifierBridge` remain open.
No pnp4 bridge advances: the accepted-content composite bridge still starts
at G3e. Neither `SearchMCSPWeakLowerBound` nor
`VerifiedNPDAGLowerBoundSource` is reduced. This is not P-vs-NP mainline progress.

The following G3o record is historical (fifteen executed, two remaining at that stage).

Part A G3o (pnp3 only) executed **H3**, separator-hole into unchanged G3n,
using `FixedPairSeparatorHoleTagRemovalShiftAlignmentCountdown`: **fifteen of
seventeen** executed handoffs, with **two** remaining (H1–H2). Its closed
196-state, 588-row `UniformTM` has an unconditional strict one-step
whole-configuration handoff. H4–H7 inherit their exact endpoints at times plus
one, with controls 12/19/45/49. The exact drain retains the eight G3n premises;
the theorem-derived **2973-step** fixture has accept 194, head 23, complete
`loopTape 22 tag physWord 4 0 24`, and persistence. Its hand-supplied `v=24`
witnesses execution premises, not `ContentAccepts` nonvacuity or first arrival
of composed accept. Rejection transport is forward-only. This is
**Infrastructure only** and builds **no pnp4 bridge**: the accepted-content
composite bridge still starts at G3e. No raw-input execution, later parser
field, `TM.runConfig` conversion, runtime fence or budget domination, runtime
selection of `C/q/v`, advice-freedom claim, language acceptance, verifier bridge,
or P-vs-NP mainline progress follows. Neither `SearchMCSPWeakLowerBound` nor
`VerifiedNPDAGLowerBoundSource` is reduced.

The following G3m counts describe its earlier boundary. Part A G3m (pnp3 only) has since executed **H5** as well — the fixed 7-state, 21-row structural
one-cell origin shift prefixed to that G3l composite as one closed 184-state, 552-row table, again
with no new row and no `mergeAccept`, switching at the shift phase's own strict first arrival
`4a + 3m + 5`, which was already landed in the shape `seq` consumes and hypothesis-free, so G3m's
`handoff_exact` takes no hypothesis either and additionally pins strict left-block confinement —
then taking the count to **thirteen of seventeen** with **four** earlier handoffs still proof-level; the
twelve-and-five counts just given are the ones G3l left. H5's live accept list is as narrow as a live
handoff's can be: **one** row, the bootstrap fetch state `4` on `none`, proved the only one targeting
the phase's accept once the accept's own absorbing three are excluded, routed to index `7` keeping
its written `none` and its `.stay`, so it costs nothing and clamps on neither budget. Its reject side
is proved an **equivalence**, not just exhaustive: once **both** verdicts' own absorbing rows are
excluded, a row targets the phase's reject exactly when the symbol is a Boolean and the state is one
of `1`, `2`, `3`, six rows in all, each routed to the composed reject, none ever taken out of G3m's
start. G3m's switch time is linear, far below G3l's quadratic one, but it still reads the two split
lengths apart, so the composed clock stays quadratic in `a` and it is still **not** proved that the
cubic budget dominates it. G3m is Infrastructure only and builds **no pnp4 bridge** either, on the
same terms as G3l. No first arrival of the G3e composed accept is
proved (the first arrival proved is G2p-a's, inside the left block), the lane is still unfenced, the
composed accept is still the countdown's phase-local `qDone` rather than language acceptance, the
machine is a V1 `UniformTM` on `Option Bool` cells against `pairLength a m` and not
the legacy `TM` with a `runTime` field that `ContentVerifierBridge` names, and, like G2x, G2y, G2z,
G3a and G3c, this is infrastructure, not P-vs-NP mainline progress; it makes no `P ≠ NP` claim.

For an *arbitrary* threshold there is a third input, `PolyBoundedInTable threshold`;
it is proved for the canonical polynomial thresholds, so it disappears at
`thresholdPoly k`.  The general capstone `verifiedSource_of_explicit_interfaces`
(`ExplicitConditionalSource.lean`) still packages three interfaces for an arbitrary
codec and threshold.

The extraction is formalized in **one direction only** (`PpolyDAG → solver`, plus its
contrapositive); the converse is not formalized, so input (1) is *at least as strong as*
the full `P/poly` lower bound rather than a weak bound amplified by magnification.  See
`Frontier/ContractExpansion/README.md` for the full module map, the runtime-model caveat
attaching to input (2), and the proved-vs-open breakdown.
