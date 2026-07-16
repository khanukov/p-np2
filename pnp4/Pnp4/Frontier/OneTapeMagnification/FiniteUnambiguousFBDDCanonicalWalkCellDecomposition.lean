import Pnp4.Frontier.OneTapeMagnification.FiniteUnambiguousFBDDWalkPairLiteralFactorization

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Canonical-walk cells inside residual suffix cones

The accepted models in a canonical residual suffix cone have an exact finite
partition by their selected bare accepting walks.  Although the ambient type
of formal walks is not equipped with a `Fintype`, the realized walks form the
finite image of `AcceptedModel` under `canonicalAcceptingWalk`.

Each cell below is the accepted-point sum over one fiber of that map, with the
suffix-key test retained inside the fiber.  It is supported on the
compatibility fiber of its indexing walk.  Consequently a product of two cone
indicators is an exact double sum of walk-pair rectangles.

No unambiguity or read-once premise is needed for these partition identities.
The double sum includes equal-walk pairs; this file does not claim an
opposite-literal factorization for those pairs, nor any bound on the number or
total mass of the rectangles.
-/

noncomputable section

open scoped BigOperators

open FiniteBooleanFourier
open FiniteBooleanOppositeLiteralCorrelation

namespace FiniteUnambiguousFBDD

/-- Bare accepting walks selected by at least one accepted input.  This is a
finite image even though the type of all formal accepting walks has no global
`Fintype` instance. -/
noncomputable def realizedCanonicalAcceptingWalks {n : Nat}
    (B : FiniteUnambiguousFBDD n) :
    Finset (B.Walk B.start B.accept) := by
  classical
  exact Finset.univ.image B.canonicalAcceptingWalk

@[simp]
theorem mem_realizedCanonicalAcceptingWalks {n : Nat}
    (B : FiniteUnambiguousFBDD n) (walk : B.Walk B.start B.accept) :
    walk ∈ B.realizedCanonicalAcceptingWalks ↔
      ∃ accepted : B.AcceptedModel,
        B.canonicalAcceptingWalk accepted = walk := by
  classical
  simp [realizedCanonicalAcceptingWalks]

/-- Accepted models whose selected bare accepting walk is exactly `walk`. -/
noncomputable def canonicalAcceptingWalkFiber {n : Nat}
    (B : FiniteUnambiguousFBDD n)
    (walk : B.Walk B.start B.accept) : Finset B.AcceptedModel := by
  classical
  exact Finset.univ.filter fun accepted =>
    B.canonicalAcceptingWalk accepted = walk

@[simp]
theorem mem_canonicalAcceptingWalkFiber {n : Nat}
    (B : FiniteUnambiguousFBDD n)
    (walk : B.Walk B.start B.accept) (accepted : B.AcceptedModel) :
    accepted ∈ B.canonicalAcceptingWalkFiber walk ↔
      B.canonicalAcceptingWalk accepted = walk := by
  classical
  simp [canonicalAcceptingWalkFiber]

/-- The part of one canonical residual suffix-cone indicator carried by a
single selected bare accepting walk. -/
noncomputable def canonicalWalkSuffixConeCellIndicator {n : Nat}
    (B : FiniteUnambiguousFBDD n)
    (key : List (InputLabelledFullStep B))
    (walk : B.Walk B.start B.accept) (input : Fin n → Bool) : Rat :=
  ∑ accepted ∈ B.canonicalAcceptingWalkFiber walk,
    if key <:+ B.canonicalInputLabelledFullTrace accepted then
      B.ratAcceptedPointIndicator accepted input
    else 0

/-- Every canonical-walk cell is supported on the compatibility fiber of its
indexing walk.  The claim is also valid for unrealized walks, where the cell is
empty. -/
theorem canonicalWalkSuffixConeCellIndicator_supportedOnCompatibleFiber
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (key : List (InputLabelledFullStep B))
    (walk : B.Walk B.start B.accept) :
    walk.RatSupportedOnCompatibleFiber
      (B.canonicalWalkSuffixConeCellIndicator key walk) := by
  classical
  intro input hincompatible
  unfold canonicalWalkSuffixConeCellIndicator
  apply Finset.sum_eq_zero
  intro accepted haccepted
  have hwalk : B.canonicalAcceptingWalk accepted = walk :=
    (B.mem_canonicalAcceptingWalkFiber walk accepted).1 haccepted
  by_cases hinput : input = accepted.1
  · subst input
    have hcompatible : walk.Compatible accepted.1 :=
      hwalk ▸ B.canonicalAcceptingWalk_compatible accepted
    exact (hincompatible hcompatible).elim
  · simp [ratAcceptedPointIndicator, hinput]

/-- Exact finite decomposition of a canonical residual suffix-cone indicator
into its canonical-walk-supported cells. -/
theorem canonicalResidualSuffixConeIndicator_eq_sum_canonicalWalkCells
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (key : List (InputLabelledFullStep B)) (input : Fin n → Bool) :
    B.canonicalResidualSuffixConeIndicator key input =
      ∑ walk ∈ B.realizedCanonicalAcceptingWalks,
        B.canonicalWalkSuffixConeCellIndicator key walk input := by
  classical
  unfold canonicalResidualSuffixConeIndicator
    canonicalWalkSuffixConeCellIndicator canonicalAcceptingWalkFiber
    realizedCanonicalAcceptingWalks
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset B.AcceptedModel))
    (t := Finset.univ.image B.canonicalAcceptingWalk)
    (g := B.canonicalAcceptingWalk)
    (fun accepted _ => Finset.mem_image_of_mem _ (Finset.mem_univ accepted))
    (fun accepted =>
      if key <:+ B.canonicalInputLabelledFullTrace accepted then
        B.ratAcceptedPointIndicator accepted input
      else 0)

/-- Distinct realized canonical-walk cells inherit the fixed-walk-pair
opposite-literal factorization.  Realizedness supplies one compatible reference
input for each walk; the factors themselves apply to the entire two cell
functions and are independent of the separating coordinate.

This theorem is deliberately restricted to distinct bare walks.  Equal-walk
sibling cells require a separate analysis of their input-labelled suffix
steps. -/
theorem exists_oppositeLiteralFactorization_canonicalWalkSuffixConeCells_of_ne
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (hUnambiguous : B.IsUnambiguous)
    (leftKey rightKey : List (InputLabelledFullStep B))
    (leftWalk rightWalk : B.Walk B.start B.accept)
    (hleftRealized : leftWalk ∈ B.realizedCanonicalAcceptingWalks)
    (hrightRealized : rightWalk ∈ B.realizedCanonicalAcceptingWalks)
    (hne : leftWalk ≠ rightWalk) :
    ∃ coordinate : Fin n,
      ∃ leftFactor rightFactor : (Fin n → Bool) → Rat,
        coordinate ∈ leftWalk.queryVars ∧
          coordinate ∈ rightWalk.queryVars ∧
            DependsOnlyOn (Finset.univ.erase coordinate) leftFactor ∧
              DependsOnlyOn (Finset.univ.erase coordinate) rightFactor ∧
                ((B.canonicalWalkSuffixConeCellIndicator leftKey leftWalk =
                      falseLiteralPart coordinate leftFactor ∧
                    B.canonicalWalkSuffixConeCellIndicator rightKey rightWalk =
                      trueLiteralPart coordinate rightFactor) ∨
                  (B.canonicalWalkSuffixConeCellIndicator leftKey leftWalk =
                      trueLiteralPart coordinate leftFactor ∧
                    B.canonicalWalkSuffixConeCellIndicator rightKey rightWalk =
                      falseLiteralPart coordinate rightFactor)) := by
  obtain ⟨leftAccepted, hleftWalk⟩ :=
    (B.mem_realizedCanonicalAcceptingWalks leftWalk).1 hleftRealized
  obtain ⟨rightAccepted, hrightWalk⟩ :=
    (B.mem_realizedCanonicalAcceptingWalks rightWalk).1 hrightRealized
  have hleftCompatible : leftWalk.Compatible leftAccepted.1 :=
    hleftWalk ▸ B.canonicalAcceptingWalk_compatible leftAccepted
  have hrightCompatible : rightWalk.Compatible rightAccepted.1 :=
    hrightWalk ▸ B.canonicalAcceptingWalk_compatible rightAccepted
  exact Walk.exists_oppositeLiteralFactorization_of_ne
    hUnambiguous leftWalk rightWalk leftAccepted.1 rightAccepted.1
    hleftCompatible hrightCompatible hne
    (B.canonicalWalkSuffixConeCellIndicator leftKey leftWalk)
    (B.canonicalWalkSuffixConeCellIndicator rightKey rightWalk)
    (B.canonicalWalkSuffixConeCellIndicator_supportedOnCompatibleFiber
      leftKey leftWalk)
    (B.canonicalWalkSuffixConeCellIndicator_supportedOnCompatibleFiber
      rightKey rightWalk)

/-- Product of two canonical-walk cells, viewed as a rectangle on two copies
of the Boolean cube. -/
noncomputable def canonicalWalkPairRectangleIndicator {n : Nat}
    (B : FiniteUnambiguousFBDD n)
    (leftKey rightKey : List (InputLabelledFullStep B))
    (leftWalk rightWalk : B.Walk B.start B.accept)
    (inputs : (Fin n → Bool) × (Fin n → Bool)) : Rat :=
  B.canonicalWalkSuffixConeCellIndicator leftKey leftWalk inputs.1 *
    B.canonicalWalkSuffixConeCellIndicator rightKey rightWalk inputs.2

/-- Exact walk-pair rectangle expansion of the product of two residual
suffix-cone indicators.  In particular this applies to two distinct sibling
keys `leftStep :: key` and `rightStep :: key`; distinctness is not needed for
the algebraic decomposition itself. -/
theorem canonicalResidualSuffixConeIndicators_mul_eq_sum_walkPairRectangles
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (leftKey rightKey : List (InputLabelledFullStep B))
    (leftInput rightInput : Fin n → Bool) :
    B.canonicalResidualSuffixConeIndicator leftKey leftInput *
        B.canonicalResidualSuffixConeIndicator rightKey rightInput =
      ∑ leftWalk ∈ B.realizedCanonicalAcceptingWalks,
        ∑ rightWalk ∈ B.realizedCanonicalAcceptingWalks,
          B.canonicalWalkPairRectangleIndicator leftKey rightKey
            leftWalk rightWalk (leftInput, rightInput) := by
  rw [B.canonicalResidualSuffixConeIndicator_eq_sum_canonicalWalkCells,
    B.canonicalResidualSuffixConeIndicator_eq_sum_canonicalWalkCells]
  rw [Finset.sum_mul_sum]
  rfl

end FiniteUnambiguousFBDD

end

end OneTapeMagnification
end Frontier
end Pnp4
