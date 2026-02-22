/-!
  pnp3/Barrier/Algebrization.lean

  Minimal formal interface for algebrization barriers.

  As in `Barrier.Relativization`, we keep the model abstract and expose only
  oracle-family invariance plus bypass witnesses.
-/

namespace Pnp3
namespace Barrier

universe u

/-- A statement scheme is algebrizing if algebraic oracle changes do not matter. -/
def Algebrizing (S : Type u → Prop) : Prop :=
  ∀ A₁ A₂ : Type u, S A₁ ↔ S A₂

/-- A witness that a statement scheme is non-algebrizing. -/
structure AlgebrizationBypassWitness (S : Type u → Prop) : Type (u + 1) where
  A₁ : Type u
  A₂ : Type u
  holds₁ : S A₁
  fails₂ : ¬ S A₂

/-- A bypass witness immediately implies that the scheme is not algebrizing. -/
theorem not_algebrizing_of_bypass
    {S : Type u → Prop}
    (hBypass : AlgebrizationBypassWitness S) :
    ¬ Algebrizing S := by
  intro hAlg
  have hEq : S hBypass.A₁ ↔ S hBypass.A₂ := hAlg hBypass.A₁ hBypass.A₂
  exact hBypass.fails₂ (hEq.mp hBypass.holds₁)

end Barrier
end Pnp3
