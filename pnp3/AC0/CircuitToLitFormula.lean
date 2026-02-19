import AC0.AC0LitFormula
import Models.Model_PartialMCSP

/-!
  pnp3/AC0/CircuitToLitFormula.lean

  Conversion from `Models.Circuit n` to `AC0LitFormula n d` for some `d`.

  A tree-shaped Boolean circuit over `n` inputs can be converted to a
  literal formula (with `posLit`/`negLit` atoms) using De Morgan's laws
  to push negations to the leaves. The depth of the resulting formula
  equals the depth of the circuit tree.

  The conversion uses a polarity flag `pol : Bool`:
  - `pol = true`: compute the formula for `C.eval x`
  - `pol = false`: compute the formula for `!(C.eval x)`

  This ensures that negations are only applied at the literal level.
-/

namespace Pnp3

/-! ### Circuit depth (defined in Models namespace for dot notation) -/

namespace Models

/-- Depth (longest root-to-leaf path) of a tree-shaped circuit. -/
def Circuit.depth {n : Nat} : Circuit n → Nat
  | Circuit.input _ => 0
  | Circuit.const _ => 0
  | Circuit.not c => c.depth
  | Circuit.and c₁ c₂ => max c₁.depth c₂.depth + 1
  | Circuit.or c₁ c₂ => max c₁.depth c₂.depth + 1

end Models

/-! ### AC0LitFormula padding and conversion -/

namespace AC0

open Core Models

/-! ### Padding: lift a formula to a higher depth -/

/-- Wrap a formula in a trivial `and [f]` to increase depth by 1. -/
def AC0LitFormula.padDepth {n d : Nat} (f : AC0LitFormula n d) :
    AC0LitFormula n (d + 1) :=
  AC0LitFormula.and (AC0LitFormulaList.cons f AC0LitFormulaList.nil)

/-- Pad a formula from depth `d` to depth `d + k` by iterated wrapping. -/
def AC0LitFormula.padToDepth {n : Nat} (d : Nat) :
    (k : Nat) → AC0LitFormula n d → AC0LitFormula n (d + k)
  | 0, f => f
  | k + 1, f =>
      have : d + (k + 1) = (d + k) + 1 := by omega
      this ▸ (AC0LitFormula.padToDepth d k f).padDepth

/-! ### Circuit to literal formula conversion -/

/-- Convert a circuit to a literal formula, pushing negations to leaves.
    `pol = true` means positive polarity (compute `C.eval x`);
    `pol = false` means negative polarity (compute `!(C.eval x)`). -/
noncomputable def circuitToLitFormula {n : Nat} :
    Circuit n → Bool → Σ d, AC0LitFormula n d
  | Circuit.input i, true  => ⟨0, AC0LitFormula.posLit i⟩
  | Circuit.input i, false => ⟨0, AC0LitFormula.negLit i⟩
  | Circuit.const b, pol   => ⟨0, AC0LitFormula.constLit (if pol then b else !b)⟩
  | Circuit.not c, pol     => circuitToLitFormula c (!pol)
  | Circuit.and c₁ c₂, true =>
      let ⟨d₁, f₁⟩ := circuitToLitFormula c₁ true
      let ⟨d₂, f₂⟩ := circuitToLitFormula c₂ true
      let d := max d₁ d₂
      let f₁' := AC0LitFormula.padToDepth d₁ (d - d₁) f₁
      let f₂' := AC0LitFormula.padToDepth d₂ (d - d₂) f₂
      have h₁ : d₁ + (d - d₁) = d := by omega
      have h₂ : d₂ + (d - d₂) = d := by omega
      ⟨d + 1, AC0LitFormula.and
        (AC0LitFormulaList.cons (h₁ ▸ f₁')
          (AC0LitFormulaList.cons (h₂ ▸ f₂') AC0LitFormulaList.nil))⟩
  | Circuit.and c₁ c₂, false =>  -- De Morgan: ¬(a ∧ b) = ¬a ∨ ¬b
      let ⟨d₁, f₁⟩ := circuitToLitFormula c₁ false
      let ⟨d₂, f₂⟩ := circuitToLitFormula c₂ false
      let d := max d₁ d₂
      let f₁' := AC0LitFormula.padToDepth d₁ (d - d₁) f₁
      let f₂' := AC0LitFormula.padToDepth d₂ (d - d₂) f₂
      have h₁ : d₁ + (d - d₁) = d := by omega
      have h₂ : d₂ + (d - d₂) = d := by omega
      ⟨d + 1, AC0LitFormula.or
        (AC0LitFormulaList.cons (h₁ ▸ f₁')
          (AC0LitFormulaList.cons (h₂ ▸ f₂') AC0LitFormulaList.nil))⟩
  | Circuit.or c₁ c₂, true =>
      let ⟨d₁, f₁⟩ := circuitToLitFormula c₁ true
      let ⟨d₂, f₂⟩ := circuitToLitFormula c₂ true
      let d := max d₁ d₂
      let f₁' := AC0LitFormula.padToDepth d₁ (d - d₁) f₁
      let f₂' := AC0LitFormula.padToDepth d₂ (d - d₂) f₂
      have h₁ : d₁ + (d - d₁) = d := by omega
      have h₂ : d₂ + (d - d₂) = d := by omega
      ⟨d + 1, AC0LitFormula.or
        (AC0LitFormulaList.cons (h₁ ▸ f₁')
          (AC0LitFormulaList.cons (h₂ ▸ f₂') AC0LitFormulaList.nil))⟩
  | Circuit.or c₁ c₂, false =>  -- De Morgan: ¬(a ∨ b) = ¬a ∧ ¬b
      let ⟨d₁, f₁⟩ := circuitToLitFormula c₁ false
      let ⟨d₂, f₂⟩ := circuitToLitFormula c₂ false
      let d := max d₁ d₂
      let f₁' := AC0LitFormula.padToDepth d₁ (d - d₁) f₁
      let f₂' := AC0LitFormula.padToDepth d₂ (d - d₂) f₂
      have h₁ : d₁ + (d - d₁) = d := by omega
      have h₂ : d₂ + (d - d₂) = d := by omega
      ⟨d + 1, AC0LitFormula.and
        (AC0LitFormulaList.cons (h₁ ▸ f₁')
          (AC0LitFormulaList.cons (h₂ ▸ f₂') AC0LitFormulaList.nil))⟩

/-- Convert a circuit to a literal formula with positive polarity. -/
noncomputable def circuitToLitFormulaPos {n : Nat} (C : Circuit n) :
    Σ d, AC0LitFormula n d :=
  circuitToLitFormula C true

/-! ### StraightLineCircuit to literal formula

The path from a Boolcube.Circuit (from the Facts package) to a literal formula
goes through the local Models.Circuit type. The Boolcube.Circuit is mirrored
into Models.Circuit, then converted to an AC0LitFormula.
-/

/-- Mirror a Boolcube.Circuit (from Facts package) into the local Models.Circuit type. -/
noncomputable def boolcubeToModelsCircuit {n : Nat} :
    Facts.PsubsetPpoly.Boolcube.Circuit n → Circuit n
  | .var i => Circuit.input i
  | .const b => Circuit.const b
  | .not c => Circuit.not (boolcubeToModelsCircuit c)
  | .and c₁ c₂ => Circuit.and (boolcubeToModelsCircuit c₁) (boolcubeToModelsCircuit c₂)
  | .or c₁ c₂ => Circuit.or (boolcubeToModelsCircuit c₁) (boolcubeToModelsCircuit c₂)

/-- Convert a Boolcube.Circuit (from Facts package) to a literal formula.
    The tree circuit is first mirrored into the local Models.Circuit type,
    then converted to AC0LitFormula. -/
noncomputable def boolcubeCircuitToLitFormula {n : Nat}
    (C : Facts.PsubsetPpoly.Boolcube.Circuit n) :
    Σ d, AC0LitFormula n d :=
  circuitToLitFormula (boolcubeToModelsCircuit C) true

end AC0
end Pnp3
