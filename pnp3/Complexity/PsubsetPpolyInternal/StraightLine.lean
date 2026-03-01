import Complexity.PsubsetPpolyInternal.CircuitTree
import Complexity.PpolyDAG_from_ArchiveStraightLine
import Mathlib.Tactic

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace StraightLine

open Pnp3.Complexity
open Pnp3.Complexity.ArchiveStraightLineAdapter

abbrev GateOp := LegacyStraightOp
abbrev Circuit (n : Nat) := StraightLineCircuit n

abbrev size {n : Nat} (C : Circuit n) : Nat := C.gates

/-- Canonical embedding of old wires into the one-gate extension. -/
def liftWire {n : Nat} (C : Circuit n) :
    Fin (n + C.gates) → Fin (n + (C.gates + 1)) :=
  fun i =>
    ⟨i, by
      have h₁ : (i : Nat) < n + C.gates := i.isLt
      have h₂ : n + C.gates < n + (C.gates + 1) := by
        have := Nat.lt_succ_self (n + C.gates)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
      exact Nat.lt_trans h₁ h₂⟩

/-- Append one gate to a straight-line circuit. -/
def snoc {n : Nat} (C : Circuit n) (op : GateOp (n + C.gates)) : Circuit n where
  gates := C.gates + 1
  gate := fun g =>
    if h : (g : Nat) < C.gates then
      by simpa using (C.gate ⟨g, h⟩)
    else
      by
        have hle : (g : Nat) ≤ C.gates := Nat.lt_succ_iff.mp (by simpa using g.isLt)
        have hge : C.gates ≤ (g : Nat) := Nat.le_of_not_gt h
        have hg : (g : Nat) = C.gates := Nat.le_antisymm hle hge
        simpa [hg] using (show GateOp (n + C.gates) from op)
  output := Fin.last (n + C.gates)

/-- Internal wire semantics under a visible gate budget `g`. -/
def evalWireAux {n : Nat} (C : Circuit n) (x : Boolcube.Point n) :
    (g : Nat) → g ≤ C.gates → Fin (n + g) → Bool
  | g, hg, i =>
      if hIn : (i : Nat) < n then
        x ⟨i, hIn⟩
      else
        let j : Nat := (i : Nat) - n
        have hj : j < g := by
          have hi : (i : Nat) < n + g := i.isLt
          dsimp [j]
          omega
        have hj' : j < C.gates := Nat.lt_of_lt_of_le hj hg
        match C.gate ⟨j, hj'⟩ with
        | .const b => b
        | .not u => !(evalWireAux (C := C) (x := x) j (Nat.le_of_lt hj') u)
        | .and u v =>
            evalWireAux (C := C) (x := x) j (Nat.le_of_lt hj') u &&
              evalWireAux (C := C) (x := x) j (Nat.le_of_lt hj') v
        | .or u v =>
            evalWireAux (C := C) (x := x) j (Nat.le_of_lt hj') u ||
              evalWireAux (C := C) (x := x) j (Nat.le_of_lt hj') v
termination_by g _ _ => g

/-- Internal gate semantics as a thin wrapper over `evalWireAux`. -/
def evalGateAux {n : Nat} (C : Circuit n) (x : Boolcube.Point n) :
    ∀ {g : Nat}, g < C.gates → Bool
  | g, hg =>
      match C.gate ⟨g, hg⟩ with
      | .const b => b
      | .not i => !(evalWireAux (C := C) (x := x) g (Nat.le_of_lt hg) i)
      | .and i j =>
          evalWireAux (C := C) (x := x) g (Nat.le_of_lt hg) i &&
            evalWireAux (C := C) (x := x) g (Nat.le_of_lt hg) j
      | .or i j =>
          evalWireAux (C := C) (x := x) g (Nat.le_of_lt hg) i ||
            evalWireAux (C := C) (x := x) g (Nat.le_of_lt hg) j

/--
Read one wire while rebuilding a gate into a tree circuit.

This helper keeps the `Fin (n + g)`-dependent split localized and makes
inductive gate proofs more robust against simplifier loops.
-/
noncomputable def toCircuitWireOf {n : Nat} (C : Circuit n)
    {g : Nat} (hg : g < C.gates) (i : Fin (n + g))
    (rec : ∀ j : Nat, j < g → j < C.gates → Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit n) :
    Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit n :=
  if h : (i : Nat) < n then
    Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.var ⟨i, h⟩
  else
    let j : Nat := (i : Nat) - n
    have hj : j < g := by
      have hi : (i : Nat) < n + g := i.isLt
      dsimp [j]
      omega
    have hj' : j < C.gates := Nat.lt_trans hj hg
    rec j hj hj'

/--
Read one wire while evaluating a gate under a fixed gate budget.

This is the boolean counterpart of `toCircuitWireOf`.
-/
def evalWireOf {n : Nat} (C : Circuit n) (x : Boolcube.Point n)
    {g : Nat} (hg : g < C.gates) (i : Fin (n + g))
    (rec : ∀ j : Nat, j < g → j < C.gates → Bool) : Bool :=
  if h : (i : Nat) < n then
    x ⟨i, h⟩
  else
    let j : Nat := (i : Nat) - n
    have hj : j < g := by
      have hi : (i : Nat) < n + g := i.isLt
      dsimp [j]
      omega
    have hj' : j < C.gates := Nat.lt_trans hj hg
    rec j hj hj'

/--
Bridge lemma: if recursive payloads agree pointwise, the extracted wire values
agree as well (`toCircuitWireOf` vs `evalWireOf`).
-/
lemma wireOf_eq {n : Nat} (C : Circuit n) (x : Boolcube.Point n)
    {g : Nat} (hg : g < C.gates) (i : Fin (n + g))
    (recTree : ∀ j : Nat, j < g → j < C.gates → Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit n)
    (recEval : ∀ j : Nat, j < g → j < C.gates → Bool)
    (hRec : ∀ (j : Nat) (hj : j < g) (hj' : j < C.gates),
      Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.eval (recTree j hj hj') x = recEval j hj hj') :
    Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.eval (toCircuitWireOf C hg i recTree) x =
      evalWireOf C x hg i recEval := by
  unfold toCircuitWireOf evalWireOf
  by_cases h : (i : Nat) < n
  · simp [h, Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.eval]
  · simp [h]
    exact hRec _ _ _

/-- Internal whole-circuit semantics. -/
def evalInternal {n : Nat} (C : Circuit n) (x : Boolcube.Point n) : Bool :=
  if h : (C.output : Nat) < n then
    x ⟨C.output, h⟩
  else
    let j : Nat := (C.output : Nat) - n
    have hj : j < C.gates := by
      have hi : (C.output : Nat) < n + C.gates := C.output.isLt
      dsimp [j]
      omega
    evalGateAux C x hj

/-- Internal semantics of all wires at full gate budget. -/
def evalWireInternal {n : Nat} (C : Circuit n) (x : Boolcube.Point n) :
    Fin (n + C.gates) → Bool :=
  fun i =>
    if h : (i : Nat) < n then
      x ⟨i, h⟩
    else
      let j : Nat := (i : Nat) - n
      have hj : j < C.gates := by
        have hi : (i : Nat) < n + C.gates := i.isLt
        dsimp [j]
        omega
      evalGateAux C x hj

/-- Canonical straight-line semantics used by the internal simulation layer. -/
abbrev eval {n : Nat} (C : Circuit n) (x : Boolcube.Point n) : Bool :=
  evalInternal C x

/-- Canonical wire semantics at full gate budget. -/
abbrev evalWire {n : Nat} (C : Circuit n) (x : Boolcube.Point n) :
    Fin (n + C.gates) → Bool :=
  evalWireInternal C x

@[simp] lemma evalInternal_eq_evalWireInternal
    {n : Nat} (C : Circuit n) (x : Boolcube.Point n) :
    evalInternal C x = evalWireInternal C x C.output := by
  rfl

@[simp] lemma eval_eq_evalWire
    {n : Nat} (C : Circuit n) (x : Boolcube.Point n) :
    eval C x = evalWire C x C.output := by
  simpa [eval, evalWire] using evalInternal_eq_evalWireInternal (C := C) (x := x)

/-- Translate a wire to a tree circuit under a visible gate budget `g`. -/
noncomputable def toCircuitWireAux {n : Nat} (C : Circuit n) :
    (g : Nat) → g ≤ C.gates → Fin (n + g) → Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit n
  | g, hg, i =>
      if hIn : (i : Nat) < n then
        Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.var ⟨i, hIn⟩
      else
        let j : Nat := (i : Nat) - n
        have hj : j < g := by
          have hi : (i : Nat) < n + g := i.isLt
          dsimp [j]
          omega
        have hj' : j < C.gates := Nat.lt_of_lt_of_le hj hg
        match C.gate ⟨j, hj'⟩ with
        | .const b => Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.const b
        | .not u =>
            Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.not
              (toCircuitWireAux (C := C) j (Nat.le_of_lt hj') u)
        | .and u v =>
            Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.and
              (toCircuitWireAux (C := C) j (Nat.le_of_lt hj') u)
              (toCircuitWireAux (C := C) j (Nat.le_of_lt hj') v)
        | .or u v =>
            Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.or
              (toCircuitWireAux (C := C) j (Nat.le_of_lt hj') u)
              (toCircuitWireAux (C := C) j (Nat.le_of_lt hj') v)
termination_by g _ _ => g

/-- Rebuild a single straight-line gate as a tree circuit. -/
noncomputable def toCircuitGateAux {n : Nat} (C : Circuit n) :
    ∀ {g : Nat}, g < C.gates → Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit n
  | g, hg =>
      match C.gate ⟨g, hg⟩ with
      | .const b => Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.const b
      | .not i =>
          Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.not
            (toCircuitWireAux (C := C) g (Nat.le_of_lt hg) i)
      | .and i j =>
          Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.and
            (toCircuitWireAux (C := C) g (Nat.le_of_lt hg) i)
            (toCircuitWireAux (C := C) g (Nat.le_of_lt hg) j)
      | .or i j =>
          Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.or
            (toCircuitWireAux (C := C) g (Nat.le_of_lt hg) i)
            (toCircuitWireAux (C := C) g (Nat.le_of_lt hg) j)

/-- Interpret a wire of a straight-line circuit as an ordinary tree circuit. -/
noncomputable def toCircuitWire {n : Nat} (C : Circuit n) :
    Fin (n + C.gates) → Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit n :=
  fun i => toCircuitWireAux (C := C) C.gates le_rfl i

/-- Translate the designated output wire of a straight-line circuit. -/
noncomputable def toCircuit {n : Nat} (C : Circuit n) :
    Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit n :=
  toCircuitWire (C := C) C.output

@[simp] lemma evalWireInternal_input
    {n : Nat} (C : Circuit n) (x : Boolcube.Point n) (i : Fin n) :
    evalWireInternal C x
      ⟨i, by
        exact Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right n C.gates)⟩ = x i := by
  unfold evalWireInternal
  simp

lemma evalWireInternal_gate
    {n : Nat} (C : Circuit n) (x : Boolcube.Point n)
    (j : Nat) (hj : j < C.gates) :
    evalWireInternal C x
      ⟨n + j, by
        have : n + j < n + C.gates := Nat.add_lt_add_left hj n
        simpa [Nat.add_assoc] using this⟩ = evalGateAux C x hj := by
  unfold evalWireInternal
  have hNotInput : ¬ (n + j : Nat) < n := by omega
  simp [hNotInput]

@[simp] lemma toCircuitWire_input
    {n : Nat} (C : Circuit n) (i : Fin n) :
    toCircuitWire C
      ⟨i, by
        exact Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right n C.gates)⟩ =
      Pnp3.Internal.PsubsetPpoly.Boolcube.Circuit.var i := by
  unfold toCircuitWire
  unfold toCircuitWireAux
  simp

end StraightLine
end PsubsetPpoly
end Internal
end Pnp3
