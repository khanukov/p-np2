import Pnp4.AlgorithmsToLowerBounds.MCSP_LocalPRG_Transfer

namespace Pnp4
namespace AlgorithmsToLowerBounds

/--
Counting ratio for truth tables on `n` variables accepted by an exact
tree-MCSP threshold oracle at threshold `threshold`.

This is the Shannon-counting upper bound proved in
`uniformTruthTableAcceptanceProbability_le_countRatio_of_treeMCSPOracle`.
-/
noncomputable def treeMCSPCountRatio
    (n threshold : Nat) : Rat :=
  (Pnp3.Models.circuitCountBound n threshold : Rat) /
    (2 ^ (Pnp3.Models.Partial.tableLen n) : Rat)

/--
Paper-facing quantitative specification for one local-PRG lower-bound regime.

The intended reading is:
- `threshold n` is the MCSP threshold used at truth-table length `2^n`,
- `sizeBound n` is the forbidden circuit size for the target model, and
- `epsilon n` is the PRG distinguishing error tolerated by the transfer.

The field `epsilon_small` records the exact quantitative inequality needed to
close the transfer contradiction using Shannon counting.
-/
structure LocalPRGHardnessSpec where
  threshold : Nat → Nat
  sizeBound : Nat → Nat
  epsilon : Nat → Rat
  epsilon_small :
    ∀ n : Nat, epsilon n < 1 - treeMCSPCountRatio n (threshold n)

/--
Abstract family model for one published local-PRG lower-bound route.

The family may represent de Morgan formulas, arbitrary-basis formulas,
branching programs, or depth-`d` `AC0`; the asymptotic meaning is carried by
the surrounding hardness specification.
-/
structure LocalPRGTargetFamilyModel where
  classOf : Nat → CircuitFamilyClass

/--
One-sided published local-PRG route contract.

This is the minimal paper-facing interface needed by the transfer theorem:
an easy-image PRG family, a target threshold schedule, and one-sided fooling
for all circuits below the published size bound.
-/
structure PublishedOneSidedLocalPRGRouteContract
    (model : LocalPRGTargetFamilyModel)
    (spec : LocalPRGHardnessSpec) where
  prg : ∀ n : Nat, TruthTableLocalPRG n
  imageBound_le_threshold :
    ∀ n : Nat, (prg n).imageSizeBound ≤ spec.threshold n
  fools_small :
    ∀ n : Nat,
      OneSidedFoolsBoundedTruthTableClass
        (prg n)
        (model.classOf n)
        (spec.sizeBound n)
        (spec.epsilon n)

/--
Two-sided published local-PRG route contract.

This matches the usual pseudorandomness statement in the literature and is
compiled automatically to the one-sided transfer surface.
-/
structure PublishedLocalPRGRouteContract
    (model : LocalPRGTargetFamilyModel)
    (spec : LocalPRGHardnessSpec) where
  prg : ∀ n : Nat, TruthTableLocalPRG n
  imageBound_le_threshold :
    ∀ n : Nat, (prg n).imageSizeBound ≤ spec.threshold n
  fools_small :
    ∀ n : Nat,
      FoolsBoundedTruthTableClass
        (prg n)
        (model.classOf n)
        (spec.sizeBound n)
        (spec.epsilon n)

/-- Compile a two-sided published route contract into the one-sided form. -/
def PublishedLocalPRGRouteContract.toOneSided
    {model : LocalPRGTargetFamilyModel}
    {spec : LocalPRGHardnessSpec}
    (contract : PublishedLocalPRGRouteContract model spec) :
    PublishedOneSidedLocalPRGRouteContract model spec where
  prg := contract.prg
  imageBound_le_threshold := contract.imageBound_le_threshold
  fools_small := fun n =>
    oneSidedFoolsBoundedTruthTableClass_of_foolsBounded
      (contract.fools_small n)

/--
Paper-facing contradiction surface for a published one-sided local-PRG route.

If the published local-PRG regime applies at input length `n`, then no circuit
from the target model of size at most `spec.sizeBound n` can implement the
exact thresholded MCSP oracle at threshold `spec.threshold n`.
-/
theorem noSmallImplementedThresholdOracle_of_publishedOneSidedLocalPRGRoute
    {model : LocalPRGTargetFamilyModel}
    {spec : LocalPRGHardnessSpec}
    (contract : PublishedOneSidedLocalPRGRouteContract model spec)
    (n : Nat) :
    ¬ ∃ impl : ImplementedThresholdOracle (model.classOf n) n,
        (model.classOf n).size impl.circuit ≤ spec.sizeBound n ∧
        impl.threshold = spec.threshold n := by
  intro hImpl
  rcases hImpl with ⟨impl, hSize, hThresholdEq⟩
  have hThreshold :
      (contract.prg n).imageSizeBound ≤ impl.threshold := by
    simpa [hThresholdEq.symm] using contract.imageBound_le_threshold n
  have hEpsSmall :
      spec.epsilon n < 1 - treeMCSPCountRatio n impl.threshold := by
    simpa [treeMCSPCountRatio, hThresholdEq.symm] using spec.epsilon_small n
  exact smallImplementedThresholdOracle_contradiction_of_localPRGTransfer
    (prg := contract.prg n)
    (impl := impl)
    hSize
    hThreshold
    (contract.fools_small n)
    hEpsSmall

/--
Two-sided published-route version of the same contradiction theorem.
-/
theorem noSmallImplementedThresholdOracle_of_publishedLocalPRGRoute
    {model : LocalPRGTargetFamilyModel}
    {spec : LocalPRGHardnessSpec}
    (contract : PublishedLocalPRGRouteContract model spec)
    (n : Nat) :
    ¬ ∃ impl : ImplementedThresholdOracle (model.classOf n) n,
        (model.classOf n).size impl.circuit ≤ spec.sizeBound n ∧
        impl.threshold = spec.threshold n := by
  exact noSmallImplementedThresholdOracle_of_publishedOneSidedLocalPRGRoute
    contract.toOneSided n

/--
Published asymptotic target from Cheraghchi-Kabanets-Lu-Myrisiotis for de
Morgan formulas:
`MCSP` on truth-table length `N = 2^n` requires de Morgan formula size
`N^(3 - o(1))`.

This wrapper does not attempt to formalize the asymptotic `o(1)` term inside
Lean yet; it just marks the intended theorem family for future instantiation.
-/
structure DeMorganFormulaLocalPRGHardnessSpec extends LocalPRGHardnessSpec

/--
Published asymptotic target from Cheraghchi-Kabanets-Lu-Myrisiotis for formulas
over an arbitrary basis and for general branching programs:
`MCSP` on truth-table length `N = 2^n` requires size `N^(2 - o(1))`.
-/
structure FormulaOrBranchingProgramLocalPRGHardnessSpec extends LocalPRGHardnessSpec

/--
Published asymptotic target from Cheraghchi-Kabanets-Lu-Myrisiotis for depth-`d`
`AC0`:
`MCSP` on truth-table length `N = 2^n` requires size
`2^(Ω(N^(1 / (d + 2.01))))`.

The exact asymptotic constants are intentionally not hard-coded yet; this is a
paper-facing wrapper around the quantitative schedule carried by
`LocalPRGHardnessSpec`.
-/
structure AC0LocalPRGHardnessSpec extends LocalPRGHardnessSpec where
  depth : Nat

end AlgorithmsToLowerBounds
end Pnp4
