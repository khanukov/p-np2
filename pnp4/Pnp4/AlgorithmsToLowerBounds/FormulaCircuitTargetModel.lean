import Pnp4.AlgorithmsToLowerBounds.LocalPRGHardnessSpec
import Complexity.Interfaces

namespace Pnp4
namespace AlgorithmsToLowerBounds

/--
Concrete `pnp4` target class built from the fixed `pnp3` formula syntax.

This is the in-repo family of formulas over the basis `{NOT, AND, OR}` with
the exact size measure `Pnp3.ComplexityInterfaces.FormulaCircuit.size`.  We do
not identify this automatically with any external asymptotic formula model; a
published local-PRG contract must already be phrased for this concrete size
measure.
-/
def formulaCircuitFamilyClass : CircuitFamilyClass where
  Family := Pnp3.ComplexityInterfaces.FormulaCircuit
  eval := fun {_} c x => Pnp3.ComplexityInterfaces.FormulaCircuit.eval c x
  size := fun {_} c => Pnp3.ComplexityInterfaces.FormulaCircuit.size c

/--
Concrete local-PRG target model using the same in-repo formula class at every
truth-table length.
-/
def formulaCircuitTargetFamilyModel : LocalPRGTargetFamilyModel where
  classOf := fun _ => formulaCircuitFamilyClass

/--
One-sided published local-PRG route specialized to the in-repo formula class.
-/
abbrev FormulaCircuitPublishedOneSidedLocalPRGRouteContract
    (spec : LocalPRGHardnessSpec) :=
  PublishedOneSidedLocalPRGRouteContract formulaCircuitTargetFamilyModel spec

/--
Two-sided published local-PRG route specialized to the in-repo formula class.
-/
abbrev FormulaCircuitPublishedLocalPRGRouteContract
    (spec : LocalPRGHardnessSpec) :=
  PublishedLocalPRGRouteContract formulaCircuitTargetFamilyModel spec

/--
Concrete one-sided contradiction theorem for the in-repo formula class.
-/
theorem noSmallImplementedThresholdOracle_of_formulaCircuitPublishedOneSidedLocalPRGRoute
    {spec : LocalPRGHardnessSpec}
    (contract : FormulaCircuitPublishedOneSidedLocalPRGRouteContract spec)
    (n : Nat) :
    ¬ ∃ impl : ImplementedThresholdOracle formulaCircuitFamilyClass n,
        formulaCircuitFamilyClass.size impl.circuit ≤ spec.sizeBound n ∧
        impl.threshold = spec.threshold n := by
  exact noSmallImplementedThresholdOracle_of_publishedOneSidedLocalPRGRoute
    contract n

/--
Concrete two-sided contradiction theorem for the in-repo formula class.
-/
theorem noSmallImplementedThresholdOracle_of_formulaCircuitPublishedLocalPRGRoute
    {spec : LocalPRGHardnessSpec}
    (contract : FormulaCircuitPublishedLocalPRGRouteContract spec)
    (n : Nat) :
    ¬ ∃ impl : ImplementedThresholdOracle formulaCircuitFamilyClass n,
        formulaCircuitFamilyClass.size impl.circuit ≤ spec.sizeBound n ∧
        impl.threshold = spec.threshold n := by
  exact noSmallImplementedThresholdOracle_of_publishedLocalPRGRoute
    contract n

/--
Concrete size-lower-bound theorem for the in-repo formula class.

This is the first non-abstract `pnp4` local-PRG instantiation: the target
class is no longer an arbitrary `CircuitFamilyClass`, but the existing formula
syntax from `pnp3`.
-/
theorem formulaCircuit_MCSP_lower_bound_from_publishedOneSidedLocalPRGRoute
    {spec : LocalPRGHardnessSpec}
    (contract : FormulaCircuitPublishedOneSidedLocalPRGRouteContract spec)
    (n : Nat) :
    SizeLowerBound
      formulaCircuitFamilyClass
      (thresholdMCSPLanguage spec n)
      (thresholdMCSPLowerBound spec n) := by
  exact MCSP_lower_bound_from_publishedOneSidedLocalPRGRoute
    contract n

/--
Concrete two-sided size-lower-bound theorem for the in-repo formula class.
-/
theorem formulaCircuit_MCSP_lower_bound_from_publishedLocalPRGRoute
    {spec : LocalPRGHardnessSpec}
    (contract : FormulaCircuitPublishedLocalPRGRouteContract spec)
    (n : Nat) :
    SizeLowerBound
      formulaCircuitFamilyClass
      (thresholdMCSPLanguage spec n)
      (thresholdMCSPLowerBound spec n) := by
  exact MCSP_lower_bound_from_publishedLocalPRGRoute
    contract n

end AlgorithmsToLowerBounds
end Pnp4
