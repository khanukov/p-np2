import Pnp4.AlgorithmsToLowerBounds.FormulaCircuitTargetModel

namespace Pnp4
namespace AlgorithmsToLowerBounds

/--
Thresholded exact tree-MCSP slice specification for the in-repo formula class.

This is intentionally smaller than `LocalPRGHardnessSpec`: a published theorem
may provide the MCSP lower bound directly without exposing the underlying PRG,
its seed length, or its fooling proof.
-/
structure FormulaCircuitSliceSpec where
  threshold : Nat → Nat
  sizeBound : Nat → Nat

/-- Forget the PRG-specific fields and keep only the threshold/lower-bound data. -/
def LocalPRGHardnessSpec.toFormulaCircuitSliceSpec
    (spec : LocalPRGHardnessSpec) : FormulaCircuitSliceSpec where
  threshold := spec.threshold
  sizeBound := spec.sizeBound

/--
Exact thresholded MCSP language attached to one quantitative slice specification
for the in-repo formula class.
-/
noncomputable def formulaCircuitThresholdLanguage
    (spec : FormulaCircuitSliceSpec)
    (n : Nat) : BitVecLanguage :=
  exactTreeMCSPThresholdLanguage n (spec.threshold n)

/--
Pointwise lower-bound schedule attached to one quantitative slice
specification: only the truth-table slice `2^n` carries the nontrivial bound.
-/
def formulaCircuitThresholdLowerBound
    (spec : FormulaCircuitSliceSpec)
    (n : Nat) : Nat → Nat :=
  exactTreeMCSPThresholdLowerBound n (spec.sizeBound n)

/--
Paper-facing published lower-bound shortcut for one thresholded MCSP slice over
the in-repo formula syntax.

This is intentionally theorem-oracle shaped: it is useful for comparing against
published statements that already provide the final exact slice lower bound, but
the CKLM mainline should prefer the local-PRG source contracts that expose the
PRG, easy-image, fooling, and transfer-slack data before compiling to this form.
-/
structure FormulaCircuitPublishedLowerBoundContract
    (spec : FormulaCircuitSliceSpec) where
  sliceLowerBound :
    ∀ n : Nat,
      SizeLowerBound
        formulaCircuitFamilyClass
        (formulaCircuitThresholdLanguage spec n)
        (formulaCircuitThresholdLowerBound spec n)

/--
The lower-bound theorem carried by the published contract can be read back in
the standard `SizeLowerBound` form.
-/
theorem formulaCircuit_MCSP_lower_bound_from_publishedLowerBoundContract
    {spec : FormulaCircuitSliceSpec}
    (contract : FormulaCircuitPublishedLowerBoundContract spec)
    (n : Nat) :
    SizeLowerBound
      formulaCircuitFamilyClass
      (formulaCircuitThresholdLanguage spec n)
      (formulaCircuitThresholdLowerBound spec n) :=
  contract.sliceLowerBound n

/--
Any exact threshold oracle below the published size bound would violate the
published slice lower bound.
-/
theorem noSmallImplementedThresholdOracle_of_publishedLowerBoundContract
    {spec : FormulaCircuitSliceSpec}
    (contract : FormulaCircuitPublishedLowerBoundContract spec)
    (n : Nat) :
    ¬ ∃ impl : ImplementedThresholdOracle formulaCircuitFamilyClass n,
        formulaCircuitFamilyClass.size impl.circuit ≤ spec.sizeBound n ∧
        impl.threshold = spec.threshold n := by
  intro hImpl
  rcases hImpl with ⟨impl, hSize, hThresholdEq⟩
  have hComp :
      ∀ x : BitVec (Pnp3.Models.Partial.tableLen n),
        formulaCircuitFamilyClass.eval impl.circuit x =
          formulaCircuitThresholdLanguage spec n
            (Pnp3.Models.Partial.tableLen n) x := by
    intro x
    have hDecideEq :
        impl.decide x = exactTreeMCSPThresholdDecision n impl.threshold x := by
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hTrue
        exact
          (exactTreeMCSPThresholdDecision_spec x).2
            ((impl.correct x).1 hTrue)
      · intro hTrue
        exact
          (impl.correct x).2
            ((exactTreeMCSPThresholdDecision_spec x).1 hTrue)
    calc
      formulaCircuitFamilyClass.eval impl.circuit x = impl.decide x := by
        exact impl.circuit_correct x
      _ = exactTreeMCSPThresholdDecision n impl.threshold x := hDecideEq
      _ = exactTreeMCSPThresholdDecision n (spec.threshold n) x := by
        simp [hThresholdEq]
      _ = formulaCircuitThresholdLanguage spec n (Pnp3.Models.Partial.tableLen n) x := by
        simp [formulaCircuitThresholdLanguage, exactTreeMCSPThresholdLanguage]
  have hLower :
      formulaCircuitThresholdLowerBound spec n (Pnp3.Models.Partial.tableLen n) ≤
        formulaCircuitFamilyClass.size impl.circuit :=
    contract.sliceLowerBound n
      (Pnp3.Models.Partial.tableLen n)
      impl.circuit
      hComp
  have hImpossible : spec.sizeBound n + 1 ≤ spec.sizeBound n := by
    simpa [formulaCircuitThresholdLowerBound, exactTreeMCSPThresholdLowerBound] using
      le_trans hLower hSize
  exact Nat.not_succ_le_self _ hImpossible

/--
Compile the one-sided local-PRG route into the smaller theorem-facing published
formula lower-bound contract.
-/
def formulaCircuitPublishedLowerBoundContract_of_publishedOneSidedLocalPRGRoute
    {spec : LocalPRGHardnessSpec}
    (contract : FormulaCircuitPublishedOneSidedLocalPRGRouteContract spec) :
    FormulaCircuitPublishedLowerBoundContract spec.toFormulaCircuitSliceSpec where
  sliceLowerBound := fun n =>
    formulaCircuit_MCSP_lower_bound_from_publishedOneSidedLocalPRGRoute contract n

/--
Compile the two-sided local-PRG route into the smaller theorem-facing published
formula lower-bound contract.
-/
def formulaCircuitPublishedLowerBoundContract_of_publishedLocalPRGRoute
    {spec : LocalPRGHardnessSpec}
    (contract : FormulaCircuitPublishedLocalPRGRouteContract spec) :
    FormulaCircuitPublishedLowerBoundContract spec.toFormulaCircuitSliceSpec where
  sliceLowerBound := fun n =>
    formulaCircuit_MCSP_lower_bound_from_publishedLocalPRGRoute contract n

end AlgorithmsToLowerBounds
end Pnp4
