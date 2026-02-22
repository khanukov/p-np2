/-!
  pnp3/Barrier/Relativization.lean

  Minimal formal interface for relativization barriers.

  We do not fix a concrete oracle machine model here. Instead we expose
  oracle-parametric statements and the logical notion of "relativizing".
-/

namespace Pnp3
namespace Barrier

universe u

/-- A statement scheme is relativizing if it is oracle-invariant. -/
def Relativizing (S : Type u → Prop) : Prop :=
  ∀ O₁ O₂ : Type u, S O₁ ↔ S O₂

/-- A witness that a statement scheme is non-relativizing. -/
structure RelativizationBypassWitness (S : Type u → Prop) : Type (u + 1) where
  O₁ : Type u
  O₂ : Type u
  holds₁ : S O₁
  fails₂ : ¬ S O₂

/-- A bypass witness immediately implies that the scheme is not relativizing. -/
theorem not_relativizing_of_bypass
    {S : Type u → Prop}
    (hBypass : RelativizationBypassWitness S) :
    ¬ Relativizing S := by
  intro hRel
  have hEq : S hBypass.O₁ ↔ S hBypass.O₂ := hRel hBypass.O₁ hBypass.O₂
  exact hBypass.fails₂ (hEq.mp hBypass.holds₁)

end Barrier
end Pnp3
