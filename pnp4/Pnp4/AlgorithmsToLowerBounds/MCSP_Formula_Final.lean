import Pnp4.AlgorithmsToLowerBounds.FormulaCircuitPublishedLowerBound

namespace Pnp4
namespace AlgorithmsToLowerBounds

/--
Published CKLM 2019 hardness regime for the formula / branching-program route,
specialized to the in-repo formula syntax.

Mathematically, CKLM Theorem 2 is stated for formulas over an arbitrary basis
and for general branching programs.  This file instantiates only the formula
half of that route, using the existing `pnp3` basis `{NOT, AND, OR}` and its
exact size measure `FormulaCircuit.size`.
-/
abbrev CKLMFormulaCircuitHardnessSpec :=
  FormulaOrBranchingProgramLocalPRGHardnessSpec

/--
One-sided published local-PRG contract for the CKLM Theorem 2 route on the
in-repo formula syntax.
-/
abbrev CKLMFormulaCircuitPublishedOneSidedRouteContract
    (spec : CKLMFormulaCircuitHardnessSpec) :=
  FormulaCircuitPublishedOneSidedLocalPRGRouteContract spec.toLocalPRGHardnessSpec

/--
Two-sided published local-PRG contract for the CKLM Theorem 2 route on the
in-repo formula syntax.
-/
abbrev CKLMFormulaCircuitPublishedRouteContract
    (spec : CKLMFormulaCircuitHardnessSpec) :=
  FormulaCircuitPublishedLocalPRGRouteContract spec.toLocalPRGHardnessSpec

/--
The smaller theorem-facing slice specification underlying the CKLM Theorem 2
formula route.
-/
def CKLMFormulaCircuitHardnessSpec.toFormulaCircuitSliceSpec
    (spec : CKLMFormulaCircuitHardnessSpec) : FormulaCircuitSliceSpec :=
  spec.toLocalPRGHardnessSpec.toFormulaCircuitSliceSpec

/--
Paper-facing lower-bound contract for the CKLM Theorem 2 formula route, after
forgetting the internal PRG witness.
-/
abbrev CKLMFormulaCircuitPublishedTheorem2Contract
    (spec : CKLMFormulaCircuitHardnessSpec) :=
  FormulaCircuitPublishedLowerBoundContract spec.toFormulaCircuitSliceSpec

/--
Exact thresholded MCSP language attached to one CKLM Theorem 2 formula slice.
-/
noncomputable def CKLMFormulaCircuitLanguage
    (spec : CKLMFormulaCircuitHardnessSpec)
    (n : Nat) : BitVecLanguage :=
  formulaCircuitThresholdLanguage spec.toFormulaCircuitSliceSpec n

/--
Pointwise lower-bound schedule attached to one CKLM Theorem 2 formula slice.
-/
def CKLMFormulaCircuitLowerBound
    (spec : CKLMFormulaCircuitHardnessSpec)
    (n : Nat) : Nat → Nat :=
  formulaCircuitThresholdLowerBound spec.toFormulaCircuitSliceSpec n

/--
Compile the PRG-level CKLM route into the smaller theorem-facing Theorem 2
contract.
-/
def CKLMFormulaCircuitPublishedTheorem2Contract.ofRoute
    {spec : CKLMFormulaCircuitHardnessSpec}
    (contract : CKLMFormulaCircuitPublishedRouteContract spec) :
    CKLMFormulaCircuitPublishedTheorem2Contract spec :=
  formulaCircuitPublishedLowerBoundContract_of_publishedLocalPRGRoute contract

/--
One-sided version of the same compilation step.
-/
def CKLMFormulaCircuitPublishedTheorem2Contract.ofOneSidedRoute
    {spec : CKLMFormulaCircuitHardnessSpec}
    (contract : CKLMFormulaCircuitPublishedOneSidedRouteContract spec) :
    CKLMFormulaCircuitPublishedTheorem2Contract spec :=
  formulaCircuitPublishedLowerBoundContract_of_publishedOneSidedLocalPRGRoute
    contract

/--
Paper-facing contradiction theorem for the CKLM Theorem 2 formula route,
specialized to the in-repo formula syntax.
-/
theorem noSmallImplementedThresholdOracle_of_CKLMFormulaCircuitRoute
    {spec : CKLMFormulaCircuitHardnessSpec}
    (contract : CKLMFormulaCircuitPublishedRouteContract spec)
    (n : Nat) :
    ¬ ∃ impl : ImplementedThresholdOracle formulaCircuitFamilyClass n,
        formulaCircuitFamilyClass.size impl.circuit ≤ spec.sizeBound n ∧
        impl.threshold = spec.threshold n := by
  exact noSmallImplementedThresholdOracle_of_publishedLowerBoundContract
    (CKLMFormulaCircuitPublishedTheorem2Contract.ofRoute contract) n

/--
One-sided version of the same CKLM Theorem 2 contradiction theorem.
-/
theorem noSmallImplementedThresholdOracle_of_CKLMFormulaCircuitOneSidedRoute
    {spec : CKLMFormulaCircuitHardnessSpec}
    (contract : CKLMFormulaCircuitPublishedOneSidedRouteContract spec)
    (n : Nat) :
    ¬ ∃ impl : ImplementedThresholdOracle formulaCircuitFamilyClass n,
        formulaCircuitFamilyClass.size impl.circuit ≤ spec.sizeBound n ∧
        impl.threshold = spec.threshold n := by
  exact noSmallImplementedThresholdOracle_of_publishedLowerBoundContract
    (CKLMFormulaCircuitPublishedTheorem2Contract.ofOneSidedRoute contract) n

/--
Direct theorem-facing contradiction theorem for the CKLM Theorem 2 contract,
without exposing the underlying local-PRG witness.
-/
theorem noSmallImplementedThresholdOracle_of_CKLMFormulaCircuitTheorem2Contract
    {spec : CKLMFormulaCircuitHardnessSpec}
    (contract : CKLMFormulaCircuitPublishedTheorem2Contract spec)
    (n : Nat) :
    ¬ ∃ impl : ImplementedThresholdOracle formulaCircuitFamilyClass n,
        formulaCircuitFamilyClass.size impl.circuit ≤ spec.sizeBound n ∧
        impl.threshold = spec.threshold n := by
  exact noSmallImplementedThresholdOracle_of_publishedLowerBoundContract contract n

/--
Main exact-slice lower-bound theorem for the CKLM Theorem 2 formula route on
the in-repo formula syntax.
-/
theorem formulaCircuit_MCSP_lower_bound_from_CKLMFormulaCircuitRoute
    {spec : CKLMFormulaCircuitHardnessSpec}
    (contract : CKLMFormulaCircuitPublishedRouteContract spec)
    (n : Nat) :
    SizeLowerBound
      formulaCircuitFamilyClass
      (CKLMFormulaCircuitLanguage spec n)
      (CKLMFormulaCircuitLowerBound spec n) := by
  exact formulaCircuit_MCSP_lower_bound_from_publishedLowerBoundContract
    (CKLMFormulaCircuitPublishedTheorem2Contract.ofRoute contract) n

/--
One-sided version of the same exact-slice lower-bound theorem.
-/
theorem formulaCircuit_MCSP_lower_bound_from_CKLMFormulaCircuitOneSidedRoute
    {spec : CKLMFormulaCircuitHardnessSpec}
    (contract : CKLMFormulaCircuitPublishedOneSidedRouteContract spec)
    (n : Nat) :
    SizeLowerBound
      formulaCircuitFamilyClass
      (CKLMFormulaCircuitLanguage spec n)
      (CKLMFormulaCircuitLowerBound spec n) := by
  exact formulaCircuit_MCSP_lower_bound_from_publishedLowerBoundContract
    (CKLMFormulaCircuitPublishedTheorem2Contract.ofOneSidedRoute contract) n

/--
Direct theorem-facing lower-bound form of the CKLM Theorem 2 formula route,
without exposing the underlying local-PRG witness.
-/
theorem formulaCircuit_MCSP_lower_bound_from_CKLMFormulaCircuitTheorem2Contract
    {spec : CKLMFormulaCircuitHardnessSpec}
    (contract : CKLMFormulaCircuitPublishedTheorem2Contract spec)
    (n : Nat) :
    SizeLowerBound
      formulaCircuitFamilyClass
      (CKLMFormulaCircuitLanguage spec n)
      (CKLMFormulaCircuitLowerBound spec n) := by
  exact formulaCircuit_MCSP_lower_bound_from_publishedLowerBoundContract
    contract n

end AlgorithmsToLowerBounds
end Pnp4
