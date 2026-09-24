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
