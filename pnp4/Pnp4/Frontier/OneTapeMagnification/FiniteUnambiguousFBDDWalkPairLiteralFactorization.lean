import Pnp4.Frontier.OneTapeMagnification.FiniteUnambiguousFBDDOppositeQueryConflict
import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanLiteralSupportFactorization

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Literal factorization for one fixed pair of accepting walks

For two distinct accepting walks of an explicitly unambiguous branching DAG,
the uniform opposite-query witness fixes opposite values on one coordinate
throughout the two compatibility fibers.  Therefore every rational-valued
function which vanishes outside one of those fibers factors through the
corresponding Boolean literal.  Freezing that coordinate gives a factor which
does not depend on it.

This is an exact factorization for one fixed ordered pair of walks.  The
coordinate may change with the walk pair.  The result supplies neither a
coordinate uniform across sibling cones nor a bounded-size decomposition of
those cones, and it proves no packing or correlation estimate.
-/

noncomputable section

open FiniteBooleanFourier
open FiniteBooleanOppositeLiteralCorrelation
open FiniteBooleanLiteralSupportFactorization

namespace FiniteUnambiguousFBDD
namespace Walk

/-- A rational-valued cube function is supported on a walk's compatibility
fiber when it vanishes at every input incompatible with that walk. -/
def RatSupportedOnCompatibleFiber
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {source target : B.Vertex} (walk : B.Walk source target)
    (f : (Fin n -> Bool) -> Rat) : Prop :=
  forall input, Not (walk.Compatible input) -> f input = 0

/-- If a coordinate has one fixed value throughout a walk's compatibility
fiber, every function supported on that fiber vanishes on the opposite
coordinate slice. -/
theorem RatSupportedOnCompatibleFiber.eq_zero_of_coordinate_ne
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {source target : B.Vertex} (walk : B.Walk source target)
    (f : (Fin n -> Bool) -> Rat)
    (hsupport : walk.RatSupportedOnCompatibleFiber f)
    (coordinate : Fin n) (value : Bool)
    (hfixed : forall input : Fin n -> Bool,
      walk.Compatible input -> input coordinate = value)
    (input : Fin n -> Bool) (hvalue : input coordinate ≠ value) :
    f input = 0 := by
  apply hsupport input
  intro hcompatible
  exact hvalue (hfixed input hcompatible)

/-- **Fixed-walk-pair literal factorization.**  Functions supported on the
compatibility fibers of two distinct accepting walks factor through opposite
literals on a common coordinate queried by both walks.  The existential
factors are independent of that coordinate.

The orientation records which compatibility fiber fixes `false`; no choice
of orientation is assumed in advance. -/
theorem exists_oppositeLiteralFactorization_of_ne
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    (hUnambiguous : B.IsUnambiguous)
    (left right : B.Walk B.start B.accept)
    (leftReference rightReference : Fin n -> Bool)
    (hleft : left.Compatible leftReference)
    (hright : right.Compatible rightReference)
    (hne : left ≠ right)
    (f g : (Fin n -> Bool) -> Rat)
    (hf : left.RatSupportedOnCompatibleFiber f)
    (hg : right.RatSupportedOnCompatibleFiber g) :
    exists coordinate : Fin n,
      exists leftFactor rightFactor : (Fin n -> Bool) -> Rat,
        coordinate ∈ left.queryVars ∧
          coordinate ∈ right.queryVars ∧
            DependsOnlyOn (Finset.univ.erase coordinate) leftFactor ∧
              DependsOnlyOn (Finset.univ.erase coordinate) rightFactor ∧
                ((f = falseLiteralPart coordinate leftFactor ∧
                    g = trueLiteralPart coordinate rightFactor) ∨
                  (f = trueLiteralPart coordinate leftFactor ∧
                    g = falseLiteralPart coordinate rightFactor)) := by
  obtain ⟨coordinate, value, hleftQuery, hrightQuery,
      hleftFixed, hrightFixed⟩ :=
    left.exists_uniformlyOppositeLiteral_of_ne hUnambiguous right
      leftReference rightReference hleft hright hne
  cases value with
  | false =>
      have hfVanish : forall input,
          input coordinate = true -> f input = 0 := by
        intro input hvalue
        exact RatSupportedOnCompatibleFiber.eq_zero_of_coordinate_ne
          left f hf coordinate false hleftFixed input (by simp [hvalue])
      have hgVanish : forall input,
          input coordinate = false -> g input = 0 := by
        intro input hvalue
        apply RatSupportedOnCompatibleFiber.eq_zero_of_coordinate_ne
          right g hg coordinate true (by simpa using hrightFixed) input
        simp [hvalue]
      obtain ⟨hfFactorization, hgFactorization,
          hleftFactor, hrightFactor⟩ :=
        paired_literal_support_factorization coordinate f g
          hfVanish hgVanish
      exact ⟨coordinate,
        freezeCoordinate coordinate false f,
        freezeCoordinate coordinate true g,
        hleftQuery, hrightQuery, hleftFactor, hrightFactor,
        Or.inl ⟨hfFactorization, hgFactorization⟩⟩
  | true =>
      have hfVanish : forall input,
          input coordinate = false -> f input = 0 := by
        intro input hvalue
        exact RatSupportedOnCompatibleFiber.eq_zero_of_coordinate_ne
          left f hf coordinate true hleftFixed input (by simp [hvalue])
      have hgVanish : forall input,
          input coordinate = true -> g input = 0 := by
        intro input hvalue
        apply RatSupportedOnCompatibleFiber.eq_zero_of_coordinate_ne
          right g hg coordinate false (by simpa using hrightFixed) input
        simp [hvalue]
      obtain ⟨hgFactorization, hfFactorization,
          hrightFactor, hleftFactor⟩ :=
        paired_literal_support_factorization coordinate g f
          hgVanish hfVanish
      exact ⟨coordinate,
        freezeCoordinate coordinate true f,
        freezeCoordinate coordinate false g,
        hleftQuery, hrightQuery, hleftFactor, hrightFactor,
        Or.inr ⟨hfFactorization, hgFactorization⟩⟩

end Walk
end FiniteUnambiguousFBDD

end

end OneTapeMagnification
end Frontier
end Pnp4
