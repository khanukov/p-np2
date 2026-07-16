import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanOppositeLiteralCorrelation

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Literal support factorization

This file records the elementary local factorization behind an opposite-query
pair.  Freezing one Boolean coordinate removes that coordinate from the
dependency set.  Consequently, a rational-valued function supported on one
value of the coordinate is exactly the corresponding literal times its frozen
restriction.

These are pointwise local identities only.  They do not provide a common
coordinate for a family of functions, a rectangle decomposition, a packing
estimate, or a bound for a correlation sum.
-/

noncomputable section

open FiniteBooleanFourier
open FiniteBooleanOppositeLiteralCorrelation

namespace FiniteBooleanLiteralSupportFactorization

/-- Freeze one input coordinate before evaluating a cube function. -/
def freezeCoordinate {N : Nat} (coordinate : Fin N) (value : Bool)
    (f : (Fin N -> Bool) -> Rat) (input : Fin N -> Bool) : Rat :=
  f (Function.update input coordinate value)

/-- A frozen restriction is independent of the coordinate that was frozen. -/
theorem freezeCoordinate_dependsOnlyOn_erase {N : Nat}
    (coordinate : Fin N) (value : Bool)
    (f : (Fin N -> Bool) -> Rat) :
    DependsOnlyOn (Finset.univ.erase coordinate)
      (freezeCoordinate coordinate value f) := by
  intro input input' hagree
  unfold freezeCoordinate
  apply congrArg f
  funext queryIndex
  by_cases hquery : queryIndex = coordinate
  · subst queryIndex
    simp
  · rw [Function.update_of_ne hquery, Function.update_of_ne hquery]
    exact hagree queryIndex (by simp [hquery])

private theorem update_eq_self_of_apply_eq {N : Nat}
    (input : Fin N -> Bool) (coordinate : Fin N) (value : Bool)
    (hvalue : input coordinate = value) :
    Function.update input coordinate value = input := by
  funext queryIndex
  by_cases hquery : queryIndex = coordinate
  · subst queryIndex
    simp [hvalue]
  · rw [Function.update_of_ne hquery]

/-- Pointwise false-slice factorization through the coordinate frozen to
`false`. -/
theorem falseLiteralPart_freezeCoordinate_apply {N : Nat}
    (coordinate : Fin N) (f : (Fin N -> Bool) -> Rat)
    (hvanish : forall input, input coordinate = true -> f input = 0)
    (input : Fin N -> Bool) :
    f input =
      falseLiteralPart coordinate (freezeCoordinate coordinate false f) input := by
  cases hvalue : input coordinate
  · have hupdate := update_eq_self_of_apply_eq input coordinate false hvalue
    simp [falseLiteralPart, falseLiteral, freezeCoordinate, hvalue, hupdate]
  · simp [falseLiteralPart, falseLiteral, freezeCoordinate, hvalue,
      hvanish input hvalue]

/-- A function vanishing on the true slice is its false-literal part, with
coordinate-free factor obtained by freezing the coordinate to `false`. -/
theorem eq_falseLiteralPart_freezeCoordinate {N : Nat}
    (coordinate : Fin N) (f : (Fin N -> Bool) -> Rat)
    (hvanish : forall input, input coordinate = true -> f input = 0) :
    f = falseLiteralPart coordinate (freezeCoordinate coordinate false f) := by
  funext input
  exact falseLiteralPart_freezeCoordinate_apply coordinate f hvanish input

/-- Pointwise true-slice factorization through the coordinate frozen to
`true`. -/
theorem trueLiteralPart_freezeCoordinate_apply {N : Nat}
    (coordinate : Fin N) (f : (Fin N -> Bool) -> Rat)
    (hvanish : forall input, input coordinate = false -> f input = 0)
    (input : Fin N -> Bool) :
    f input =
      trueLiteralPart coordinate (freezeCoordinate coordinate true f) input := by
  cases hvalue : input coordinate
  · simp [trueLiteralPart, trueLiteral, freezeCoordinate, hvalue,
      hvanish input hvalue]
  · have hupdate := update_eq_self_of_apply_eq input coordinate true hvalue
    simp [trueLiteralPart, trueLiteral, freezeCoordinate, hvalue, hupdate]

/-- A function vanishing on the false slice is its true-literal part, with
coordinate-free factor obtained by freezing the coordinate to `true`. -/
theorem eq_trueLiteralPart_freezeCoordinate {N : Nat}
    (coordinate : Fin N) (f : (Fin N -> Bool) -> Rat)
    (hvanish : forall input, input coordinate = false -> f input = 0) :
    f = trueLiteralPart coordinate (freezeCoordinate coordinate true f) := by
  funext input
  exact trueLiteralPart_freezeCoordinate_apply coordinate f hvanish input

/-- Orientation-neutral packaging of the two opposite-slice factorizations.
The two frozen factors are separately independent of `coordinate`. -/
theorem paired_literal_support_factorization {N : Nat}
    (coordinate : Fin N)
    (falseSupported trueSupported : (Fin N -> Bool) -> Rat)
    (hfalse : forall input,
      input coordinate = true -> falseSupported input = 0)
    (htrue : forall input,
      input coordinate = false -> trueSupported input = 0) :
    (falseSupported = falseLiteralPart coordinate
        (freezeCoordinate coordinate false falseSupported)) ∧
      (trueSupported = trueLiteralPart coordinate
        (freezeCoordinate coordinate true trueSupported)) ∧
      DependsOnlyOn (Finset.univ.erase coordinate)
        (freezeCoordinate coordinate false falseSupported) ∧
      DependsOnlyOn (Finset.univ.erase coordinate)
        (freezeCoordinate coordinate true trueSupported) := by
  exact ⟨eq_falseLiteralPart_freezeCoordinate coordinate falseSupported hfalse,
    eq_trueLiteralPart_freezeCoordinate coordinate trueSupported htrue,
    freezeCoordinate_dependsOnlyOn_erase coordinate false falseSupported,
    freezeCoordinate_dependsOnlyOn_erase coordinate true trueSupported⟩

end FiniteBooleanLiteralSupportFactorization
end
end OneTapeMagnification
end Frontier
end Pnp4
