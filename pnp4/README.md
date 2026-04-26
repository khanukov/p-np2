# pnp4

`pnp4` is a separate Lean-library track for algorithms-to-lower-bounds work.

Scope split:

- `pnp3`: SAL / locality / Route-A/B frontier.
- `pnp4`: algorithmic lower bounds / MCSP / Williams-style route.

Current goal:

- build a verified algorithms-to-lower-bounds track without polluting the
  active `pnp3` research frontier.

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

1. Treat the CKLM formula/local-PRG route as an exact-slice lower-bound
   transfer, not as a `PpolyFormula` asymptotic source.  The current
   `N^{2-o(1)}` envelope cannot beat every polynomial-size formula family.
2. Use the `AC^0[p]` coin route through the published-envelope contract and the
   truth-table-slice asymptotic language.  The dense `EventuallySizeLowerBound`
   bridge is available for dense lower bounds; the current coin route is sparse
   on truth-table lengths, so it is connected through an explicit table-slice
   growth condition instead of being forced into a false dense contract.
3. Keep the final `PpolyDAG` bridge frozen until an explicit `NP` language lower
   bound against `PpolyDAG` is available.

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

Current theorem surface status:

- `BasicCircuitClasses.lean`: minimal non-uniform circuit-class interface plus
  the input-masking operator `maskVec` and `ClosedUnderInputMasking`, the class
  closure condition needed for the masking/averaging translation proof.
- `CoinProblem.lean`: exact finite-distribution semantics for the coin problem,
  monotonicity and complement laws for acceptance probabilities, total-mass
  normalization for product Bernoulli weights, and the reusable probability-gap
  criterion for `SolvesCoinProblem`.
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
