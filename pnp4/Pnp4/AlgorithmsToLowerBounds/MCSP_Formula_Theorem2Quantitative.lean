import Pnp4.AlgorithmsToLowerBounds.MCSP_Formula_Final
import Mathlib.Data.Nat.Sqrt

namespace Pnp4
namespace AlgorithmsToLowerBounds

/--
Integer-friendly lower-envelope for the CKLM ICALP 2019 Theorem 2 lower bound on
truth-table slices `N = 2^n`.

The paper states the lower bound as `N^(2 / 2^{O(√log N)}) = N^{2-o(1)}` for
formulas over an arbitrary basis and for general branching programs.  Since our
slice index is already `n = log N`, we package one representative envelope as
`2 ^ ((2 * n) / 2^(c * sqrt n + c))`, with the hidden `O(·)` absorbed into the
single natural-number parameter `c`.
-/
def cklmFormulaTheorem2LowerEnvelope
    (c n : Nat) : Nat :=
  2 ^ ((2 * n) / (2 ^ (c * Nat.sqrt n + c)))

/--
Paper-facing asymptotic profile corresponding to CKLM Theorem 2 on the
truth-table slice parameter `n = log N`.

This is only the quantitative shape of the published bound.  It does not by
itself supply the exact MCSP lower bound; that still comes from a separate
published lower-bound contract.
-/
def EventuallyAtLeastCKLMFormulaTheorem2LowerEnvelope
    (sizeBound : Nat → Nat) : Prop :=
  ∃ c n0 : Nat,
    ∀ n : Nat, n0 ≤ n →
      cklmFormulaTheorem2LowerEnvelope c n ≤ sizeBound n

/--
Quantitative paper-facing hardness regime for the CKLM Theorem 2 formula route.

This keeps only the threshold schedule, the forbidden formula size schedule, and
the asymptotic shape promised by the published theorem.
-/
structure CKLMFormulaCircuitTheorem2Hardness where
  threshold : Nat → Nat
  sizeBound : Nat → Nat
  theorem2_profile :
    EventuallyAtLeastCKLMFormulaTheorem2LowerEnvelope sizeBound

/--
CKLM formula-route source specification.

Unlike the theorem-facing `FormulaCircuitPublishedLowerBoundContract`, this
keeps the local-PRG transfer data visible: the MCSP threshold schedule, the
forbidden formula-size schedule, the PRG error schedule, the exact
Shannon-counting slack needed by the transfer theorem, and the quantitative
Theorem 2 profile.
-/
structure CKLMFormulaCircuitLocalPRGSourceSpec where
  threshold : Nat → Nat
  sizeBound : Nat → Nat
  epsilon : Nat → Rat
  epsilon_small :
    ∀ n : Nat, epsilon n < 1 - treeMCSPCountRatio n (threshold n)
  theorem2_profile :
    EventuallyAtLeastCKLMFormulaTheorem2LowerEnvelope sizeBound

/-- Read the CKLM source spec as the generic local-PRG hardness spec. -/
def CKLMFormulaCircuitLocalPRGSourceSpec.toLocalPRGHardnessSpec
    (source : CKLMFormulaCircuitLocalPRGSourceSpec) :
    LocalPRGHardnessSpec where
  threshold := source.threshold
  sizeBound := source.sizeBound
  epsilon := source.epsilon
  epsilon_small := source.epsilon_small

/--
Read the CKLM source spec as the CKLM formula/branching-program local-PRG
hardness spec used by the older route-level APIs.
-/
def CKLMFormulaCircuitLocalPRGSourceSpec.toCKLMFormulaCircuitHardnessSpec
    (source : CKLMFormulaCircuitLocalPRGSourceSpec) :
    CKLMFormulaCircuitHardnessSpec where
  threshold := source.threshold
  sizeBound := source.sizeBound
  epsilon := source.epsilon
  epsilon_small := source.epsilon_small

/-- Forget the PRG-error metadata and keep the quantitative Theorem 2 hardness. -/
def CKLMFormulaCircuitLocalPRGSourceSpec.toTheorem2Hardness
    (source : CKLMFormulaCircuitLocalPRGSourceSpec) :
    CKLMFormulaCircuitTheorem2Hardness where
  threshold := source.threshold
  sizeBound := source.sizeBound
  theorem2_profile := source.theorem2_profile

/--
Concrete CKLM source contract for the in-repo formula model.

The PRG easy-image fact is carried inside each `TruthTableLocalPRG`; the fields
here add the target threshold comparison and two-sided fooling against formulas
up to the source size bound.
-/
structure CKLMFormulaCircuitLocalPRGSourceContract
    (source : CKLMFormulaCircuitLocalPRGSourceSpec) where
  prg : ∀ n : Nat, TruthTableLocalPRG n
  imageBound_le_threshold :
    ∀ n : Nat, (prg n).imageSizeBound ≤ source.threshold n
  fools_small :
    ∀ n : Nat,
      FoolsBoundedTruthTableClass
        (prg n)
        formulaCircuitFamilyClass
        (source.sizeBound n)
        (source.epsilon n)

/-- Compile the CKLM source contract into the generic formula local-PRG route. -/
def CKLMFormulaCircuitLocalPRGSourceContract.toPublishedRoute
    {source : CKLMFormulaCircuitLocalPRGSourceSpec}
    (contract : CKLMFormulaCircuitLocalPRGSourceContract source) :
    FormulaCircuitPublishedLocalPRGRouteContract
      source.toLocalPRGHardnessSpec where
  prg := contract.prg
  imageBound_le_threshold := contract.imageBound_le_threshold
  fools_small := contract.fools_small

/-- Forget the asymptotic metadata and keep the exact thresholded slice data. -/
def CKLMFormulaCircuitTheorem2Hardness.toSliceSpec
    (hardness : CKLMFormulaCircuitTheorem2Hardness) :
    FormulaCircuitSliceSpec where
  threshold := hardness.threshold
  sizeBound := hardness.sizeBound

/--
Paper-facing contract for the exact slice lower bound promised by the CKLM
Theorem 2 quantitative regime.
-/
abbrev CKLMFormulaCircuitPublishedTheorem2QuantitativeContract
    (hardness : CKLMFormulaCircuitTheorem2Hardness) :=
  FormulaCircuitPublishedLowerBoundContract hardness.toSliceSpec

/-- Exact thresholded MCSP language attached to one quantitative CKLM slice. -/
noncomputable def CKLMFormulaCircuitQuantitativeLanguage
    (hardness : CKLMFormulaCircuitTheorem2Hardness)
    (n : Nat) : BitVecLanguage :=
  formulaCircuitThresholdLanguage hardness.toSliceSpec n

/-- Pointwise lower-bound schedule attached to one quantitative CKLM slice. -/
def CKLMFormulaCircuitQuantitativeLowerBound
    (hardness : CKLMFormulaCircuitTheorem2Hardness)
    (n : Nat) : Nat → Nat :=
  formulaCircuitThresholdLowerBound hardness.toSliceSpec n

/--
Package an existing PRG-level CKLM route together with an explicit Theorem 2
asymptotic profile witness into the smaller theorem-facing quantitative regime.
-/
def CKLMFormulaCircuitTheorem2Hardness.ofRouteSpec
    (spec : CKLMFormulaCircuitHardnessSpec)
    (hProfile : EventuallyAtLeastCKLMFormulaTheorem2LowerEnvelope spec.sizeBound) :
    CKLMFormulaCircuitTheorem2Hardness where
  threshold := spec.threshold
  sizeBound := spec.sizeBound
  theorem2_profile := hProfile

/--
Compile an existing theorem-facing CKLM contract together with a Theorem 2
profile witness into the quantitative published contract.
-/
def CKLMFormulaCircuitPublishedTheorem2QuantitativeContract.ofTheorem2Contract
    {spec : CKLMFormulaCircuitHardnessSpec}
    (hProfile : EventuallyAtLeastCKLMFormulaTheorem2LowerEnvelope spec.sizeBound)
    (contract : CKLMFormulaCircuitPublishedTheorem2Contract spec) :
    CKLMFormulaCircuitPublishedTheorem2QuantitativeContract
      (CKLMFormulaCircuitTheorem2Hardness.ofRouteSpec spec hProfile) := by
  simpa [CKLMFormulaCircuitPublishedTheorem2QuantitativeContract,
    CKLMFormulaCircuitTheorem2Hardness.ofRouteSpec,
    CKLMFormulaCircuitHardnessSpec.toFormulaCircuitSliceSpec,
    CKLMFormulaCircuitTheorem2Hardness.toSliceSpec]
    using contract

/--
Route-level compiler into the quantitative published contract.
-/
def CKLMFormulaCircuitPublishedTheorem2QuantitativeContract.ofRoute
    {spec : CKLMFormulaCircuitHardnessSpec}
    (hProfile : EventuallyAtLeastCKLMFormulaTheorem2LowerEnvelope spec.sizeBound)
    (contract : CKLMFormulaCircuitPublishedRouteContract spec) :
    CKLMFormulaCircuitPublishedTheorem2QuantitativeContract
      (CKLMFormulaCircuitTheorem2Hardness.ofRouteSpec spec hProfile) :=
  CKLMFormulaCircuitPublishedTheorem2QuantitativeContract.ofTheorem2Contract
    hProfile
    (CKLMFormulaCircuitPublishedTheorem2Contract.ofRoute contract)

/--
One-sided route-level compiler into the same quantitative published contract.
-/
def CKLMFormulaCircuitPublishedTheorem2QuantitativeContract.ofOneSidedRoute
    {spec : CKLMFormulaCircuitHardnessSpec}
    (hProfile : EventuallyAtLeastCKLMFormulaTheorem2LowerEnvelope spec.sizeBound)
    (contract : CKLMFormulaCircuitPublishedOneSidedRouteContract spec) :
    CKLMFormulaCircuitPublishedTheorem2QuantitativeContract
      (CKLMFormulaCircuitTheorem2Hardness.ofRouteSpec spec hProfile) :=
  CKLMFormulaCircuitPublishedTheorem2QuantitativeContract.ofTheorem2Contract
    hProfile
    (CKLMFormulaCircuitPublishedTheorem2Contract.ofOneSidedRoute contract)

/--
Compile a CKLM local-PRG source contract into the theorem-facing Theorem 2
contract.  This is the preferred mainline path because the PRG, easy-image
bound, fooling property, and transfer slack remain explicit until this point.
-/
def CKLMFormulaCircuitPublishedTheorem2Contract.ofLocalPRGSource
    {source : CKLMFormulaCircuitLocalPRGSourceSpec}
    (contract : CKLMFormulaCircuitLocalPRGSourceContract source) :
    CKLMFormulaCircuitPublishedTheorem2Contract
      source.toCKLMFormulaCircuitHardnessSpec :=
  CKLMFormulaCircuitPublishedTheorem2Contract.ofRoute
    contract.toPublishedRoute

/--
Compile a CKLM local-PRG source contract into the quantitative Theorem 2
contract.
-/
def CKLMFormulaCircuitPublishedTheorem2QuantitativeContract.ofLocalPRGSource
    {source : CKLMFormulaCircuitLocalPRGSourceSpec}
    (contract : CKLMFormulaCircuitLocalPRGSourceContract source) :
    CKLMFormulaCircuitPublishedTheorem2QuantitativeContract
      source.toTheorem2Hardness := by
  simpa [CKLMFormulaCircuitPublishedTheorem2QuantitativeContract,
    CKLMFormulaCircuitLocalPRGSourceSpec.toTheorem2Hardness,
    CKLMFormulaCircuitLocalPRGSourceSpec.toCKLMFormulaCircuitHardnessSpec,
    CKLMFormulaCircuitHardnessSpec.toFormulaCircuitSliceSpec,
    CKLMFormulaCircuitTheorem2Hardness.toSliceSpec] using
    (CKLMFormulaCircuitPublishedTheorem2Contract.ofLocalPRGSource contract)

/--
Direct lower-bound theorem from the quantitative CKLM Theorem 2 contract.
-/
theorem formulaCircuit_MCSP_lower_bound_from_CKLMFormulaCircuitTheorem2QuantitativeContract
    {hardness : CKLMFormulaCircuitTheorem2Hardness}
    (contract : CKLMFormulaCircuitPublishedTheorem2QuantitativeContract hardness)
    (n : Nat) :
    SizeLowerBound
      formulaCircuitFamilyClass
      (CKLMFormulaCircuitQuantitativeLanguage hardness n)
      (CKLMFormulaCircuitQuantitativeLowerBound hardness n) := by
  exact formulaCircuit_MCSP_lower_bound_from_publishedLowerBoundContract contract n

/--
Direct contradiction theorem from the quantitative CKLM Theorem 2 contract.
-/
theorem noSmallImplementedThresholdOracle_of_CKLMFormulaCircuitTheorem2QuantitativeContract
    {hardness : CKLMFormulaCircuitTheorem2Hardness}
    (contract : CKLMFormulaCircuitPublishedTheorem2QuantitativeContract hardness)
    (n : Nat) :
    ¬ ∃ impl : ImplementedThresholdOracle formulaCircuitFamilyClass n,
        formulaCircuitFamilyClass.size impl.circuit ≤ hardness.sizeBound n ∧
        impl.threshold = hardness.threshold n := by
  exact noSmallImplementedThresholdOracle_of_publishedLowerBoundContract
    contract n

/--
Mainline CKLM source theorem: the explicit local-PRG source contract implies the
exact-slice formula lower bound for the quantitative Theorem 2 hardness package.
-/
theorem formulaCircuit_MCSP_lower_bound_from_CKLMFormulaCircuitLocalPRGSource
    {source : CKLMFormulaCircuitLocalPRGSourceSpec}
    (contract : CKLMFormulaCircuitLocalPRGSourceContract source)
    (n : Nat) :
    SizeLowerBound
      formulaCircuitFamilyClass
      (CKLMFormulaCircuitQuantitativeLanguage source.toTheorem2Hardness n)
      (CKLMFormulaCircuitQuantitativeLowerBound source.toTheorem2Hardness n) := by
  exact formulaCircuit_MCSP_lower_bound_from_CKLMFormulaCircuitTheorem2QuantitativeContract
    (CKLMFormulaCircuitPublishedTheorem2QuantitativeContract.ofLocalPRGSource contract)
    n

/--
Mainline CKLM source contradiction theorem for one exact threshold-oracle
implementation.
-/
theorem noSmallImplementedThresholdOracle_of_CKLMFormulaCircuitLocalPRGSource
    {source : CKLMFormulaCircuitLocalPRGSourceSpec}
    (contract : CKLMFormulaCircuitLocalPRGSourceContract source)
    (n : Nat) :
    ¬ ∃ impl : ImplementedThresholdOracle formulaCircuitFamilyClass n,
        formulaCircuitFamilyClass.size impl.circuit ≤ source.sizeBound n ∧
        impl.threshold = source.threshold n := by
  exact noSmallImplementedThresholdOracle_of_CKLMFormulaCircuitTheorem2QuantitativeContract
    (CKLMFormulaCircuitPublishedTheorem2QuantitativeContract.ofLocalPRGSource contract)
    n

end AlgorithmsToLowerBounds
end Pnp4
