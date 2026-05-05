import Complexity.Interfaces

/-!
# Log-width adversary: formula renaming preserves size

This audit-only module supplies slot S4 of
`seed_packs/fp3b1_log_width_hardwiring_lift/`: the syntactic size
component of the `FormulaCircuit.rename` transport API.

The operation below only rewires input leaves through a coordinate map
`σ : Fin m → Fin n`.  Boolean connectives and constants are preserved
verbatim, so the formula tree has exactly the same number of nodes after
renaming.  The resulting `rename_size` theorem is intentionally local and
contains no lower-bound bridge or final-route content.
-/

namespace Pnp3
namespace ComplexityInterfaces
namespace FormulaCircuit

/--
Rename the input coordinates of a formula circuit.

Given a map `σ : Fin m → Fin n`, `rename σ c` views a formula over `m`
formal inputs as a formula over `n` formal inputs by replacing every leaf
`input i` with `input (σ i)`.  The operation is purely syntactic: constants
and Boolean gates are copied unchanged.
-/
def rename {m n : Nat} (σ : Fin m → Fin n) : FormulaCircuit m → FormulaCircuit n
  | const b => const b
  | input i => input (σ i)
  | not c => not (rename σ c)
  | and c₁ c₂ => and (rename σ c₁) (rename σ c₂)
  | or c₁ c₂ => or (rename σ c₁) (rename σ c₂)

end FormulaCircuit
end ComplexityInterfaces

namespace Magnification
namespace AuditRoutes
namespace LogWidthAdversary

open Pnp3.ComplexityInterfaces

/--
Renaming input coordinates preserves formula size.

This is slot S4's T3(size) lemma.  The proof is structural induction on the
formula: `rename` leaves the constructor shape unchanged and only transforms
`input` indices, while `FormulaCircuit.size` counts constructors.
-/
theorem rename_size {m n : Nat} (σ : Fin m → Fin n)
    (c : FormulaCircuit m) :
    FormulaCircuit.size (FormulaCircuit.rename σ c) =
      FormulaCircuit.size c := by
  induction c with
  | const b =>
      simp [FormulaCircuit.rename, FormulaCircuit.size]
  | input i =>
      simp [FormulaCircuit.rename, FormulaCircuit.size]
  | not c ih =>
      simp [FormulaCircuit.rename, FormulaCircuit.size, ih]
  | and c₁ c₂ ih₁ ih₂ =>
      simp [FormulaCircuit.rename, FormulaCircuit.size, ih₁, ih₂]
  | or c₁ c₂ ih₁ ih₂ =>
      simp [FormulaCircuit.rename, FormulaCircuit.size, ih₁, ih₂]

end LogWidthAdversary
end AuditRoutes
end Magnification
end Pnp3
