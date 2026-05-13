import Tests.FormulaSupportBoundsFalsifiabilityProbe

/-!
# Log-width adversary: support transport through formula renaming

This slot proves the support-cardinality part of the renaming API needed by the
log-width hardwiring lift.  The `rename` operation is the one introduced by the
falsifiability probe for truth-table formulas: it changes only input indices,
leaving the Boolean tree shape intact.

The key helper below records the exact syntactic support after a rename.  The
requested cardinality theorem then follows from `Finset.card_image_of_injective`
when the renaming map is injective.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace LogWidthAdversary

open ComplexityInterfaces
open Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe

namespace FormulaCircuit

/-- Renaming a formula transports its syntactic support by `Finset.image`. -/
theorem support_rename {m n : Nat} (σ : Fin m → Fin n)
    (c : FormulaCircuit m) :
    FormulaCircuit.support (FormulaCircuit.rename σ c) =
      (FormulaCircuit.support c).image σ := by
  induction c with
  | const b =>
      simp [FormulaCircuit.rename, FormulaCircuit.support]
  | input i =>
      simp [FormulaCircuit.rename, FormulaCircuit.support]
  | not c ih =>
      simp [FormulaCircuit.rename, FormulaCircuit.support, ih]
  | and c₁ c₂ ih₁ ih₂ =>
      simp [FormulaCircuit.rename, FormulaCircuit.support, ih₁, ih₂, Finset.image_union]
  | or c₁ c₂ ih₁ ih₂ =>
      simp [FormulaCircuit.rename, FormulaCircuit.support, ih₁, ih₂, Finset.image_union]

/--
Injective renaming preserves the number of support coordinates.

This is the S5 output theorem for the log-width hardwiring lift.  It is purely
syntactic: because `FormulaCircuit.rename` rewrites each `input i` to
`input (σ i)`, support is the image of the original support; injectivity prevents
collisions in that image.
-/
theorem rename_support_card {m n : Nat} (σ : Fin m → Fin n)
    (hσ : Function.Injective σ) (c : FormulaCircuit m) :
    (FormulaCircuit.support (FormulaCircuit.rename σ c)).card =
      (FormulaCircuit.support c).card := by
  rw [support_rename]
  exact Finset.card_image_of_injective _ hσ

end FormulaCircuit

/-- Slot-level alias with the theorem name advertised by the seed-pack table. -/
theorem rename_support_card {m n : Nat} (σ : Fin m → Fin n)
    (hσ : Function.Injective σ) (c : FormulaCircuit m) :
    (FormulaCircuit.support (FormulaCircuit.rename σ c)).card =
      (FormulaCircuit.support c).card :=
  FormulaCircuit.rename_support_card σ hσ c

end LogWidthAdversary
end AuditRoutes
end Magnification
end Pnp3
