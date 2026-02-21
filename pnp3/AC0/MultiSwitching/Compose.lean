import Core.PDTPartial
import Core.ShrinkageWitness

/-!
  pnp3/AC0/MultiSwitching/Compose.lean

  Composition helpers for partial trees/certificates.
  These are the glue for depth-induction: a trunk and leaf-wise tails
  combine into a deeper partial tree.
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core

/-- Compose a trunk partial PDT with leaf-wise tail partial PDTs. -/
def composePartialDT
    {n ℓ₁ ℓ₂ L₂ : Nat}
    (Q₁ : PartialDT n ℓ₁)
    (Q₂ : ∀ β, β ∈ PDT.leaves Q₁.trunk → PartialDT n ℓ₂)
    (htrunk : ∀ β hβ, PDT.depth (Q₂ β hβ).trunk ≤ L₂) :
    PartialDT n (L₂ + ℓ₂) where
  trunk := Q₁.trunk
  tails := fun β hβ => (Q₂ β hβ).realize
  tail_depth_le := by
    intro β hβ
    have hdepth := (Q₂ β hβ).depth_realize_le
    -- depth(realize) ≤ depth(trunk) + ℓ₂ ≤ L₂ + ℓ₂
    exact (Nat.le_trans hdepth (by
      have h := htrunk β hβ
      exact Nat.add_le_add_right h ℓ₂))

/-- Depth bound for the composed partial tree. -/
lemma depth_realize_le_compose
    {n ℓ₁ ℓ₂ L₂ : Nat}
    (Q₁ : PartialDT n ℓ₁)
    (Q₂ : ∀ β, β ∈ PDT.leaves Q₁.trunk → PartialDT n ℓ₂)
    (htrunk : ∀ β hβ, PDT.depth (Q₂ β hβ).trunk ≤ L₂) :
    PDT.depth (composePartialDT (Q₁ := Q₁) (Q₂ := Q₂) (htrunk := htrunk)).realize
      ≤ PDT.depth Q₁.trunk + (L₂ + ℓ₂) := by
  -- realize depth bound follows from PartialDT.depth_realize_le
  simpa [composePartialDT] using
    (PartialDT.depth_realize_le
      (Q := composePartialDT (Q₁ := Q₁) (Q₂ := Q₂) (htrunk := htrunk)))

end MultiSwitching
end AC0
end Pnp3
