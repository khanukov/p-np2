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

- `BasicCircuitClasses.lean`: minimal non-uniform circuit-class interface plus
  the input-masking operator `maskVec` and `ClosedUnderInputMasking`, the class
  closure condition needed for the masking/averaging translation proof.
- `DagShannonCounting.lean`: unconditional Shannon-counting layer at the exact
  `PpolyDAG` endpoint of the final bridge.  It proves an explicit
  description-count bound for the functions computed by `DagCircuit` families,
  the diagonal language `dagHardLanguage` with an outright
  `¬ PpolyDAG dagHardLanguage` theorem, the unconditional existence theorem
  `exists_language_not_PpolyDAG`, and superpolynomial coverage of the
  self-calibrating per-length hardness budget `dagHardBudget`.  Honest scope:
  this settles the hardness half of the research-gap target unconditionally
  and isolates the remaining gap as NP-membership of a hard language; it does
  not by itself reduce the `VerifiedNPDAGLowerBoundSource` obligation, whose
  open half is the NP-membership of such a language.
- `SparseWitnessPruning.lean`: route-pruning upper bounds at the `PpolyDAG`
  endpoint.  Polynomially sparse and polynomially co-sparse languages are
  proved to lie in `PpolyDAG` (explicit DNF construction on top of new
  reusable `notC`/`andC`/`orC`/`andList`/`orList`/`eqCircuit`/`dnfCircuit`
  combinators with eval/size laws), so any valid
  `VerifiedNPDAGLowerBoundSource` witness must be dense on both the accepted
  and rejected sides (`VerifiedNPDAGLowerBoundSource.not_polySparse` /
  `.not_polyCosparse`).  This formally eliminates unary/tally-style witness
  candidates; see `pnp4/Docs/INPUT1_SELF_ATTACK_NOTES.md`.
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
unconditionally.  What it does is expose the exact remaining obligations as three
explicit, clearly-typed inputs:

1. `NoPolynomialBoundedSearchSolver codec` — the genuine weak lower bound (hard,
   research-level mathematics);
2. `PrefixExtensionNPWitness parser` — a concrete verifier TM with a polynomial
   runtime bound and certificate correctness (the NP / runtime track);
3. the concrete `TreeCircuitWitnessCodec` final assembly — reduced (by the
   `Circuit ↔ CircuitTree` bridge, the native encoder round-trip, and the
   encoding-length upper bound) to choosing a width schedule, eliminating the
   decoder's depth budget, and supplying `PolyBoundedInTable codec.witnessBits`.

The capstone `verifiedSource_of_explicit_interfaces` packages the three inputs into
`VerifiedNPDAGLowerBoundSource`.  See
`Frontier/ContractExpansion/README.md` for the full module map and the
proved-vs-open breakdown.
