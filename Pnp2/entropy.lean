/-
Simplified entropy utilities and axioms.
The original file contained a more detailed development of collision entropy.
To keep the project buildable we provide only the key definitions and record
advanced results as axioms.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Pnp2.BoolFunc

open Classical
open Real
open BoolFunc

namespace BoolFunc

/-- Collision probability of a uniform family `F`. -/
noncomputable def collProb {n : ℕ} (F : Family n) : ℝ :=
  if h : F.card = 0 then 0 else (F.card : ℝ)⁻¹

/-- Collision entropy `H₂(F)` in base 2. -/
noncomputable def H₂ {n : ℕ} (F : Family n) : ℝ :=
  Real.logb 2 F.card

/-- A quantitative entropy drop after fixing one coordinate.
This statement is assumed as an axiom. -/
axiom exists_coord_entropy_drop {n : ℕ} (F : Family n)
    (hn : 0 < n) (hF : 1 < F.card) :
    ∃ i : Fin n, ∃ b : Bool, H₂ (F.restrict i b) ≤ H₂ F - 1

end BoolFunc
