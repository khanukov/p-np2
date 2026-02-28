import Complexity.Interfaces
import Mathlib.Tactic

namespace Pnp3
namespace Complexity
namespace ArchiveStraightLineAdapter

open ComplexityInterfaces

/-- Legacy straight-line gate operations used as adapter input format. -/
inductive LegacyStraightOp : Nat → Type
  | const {m : Nat} : Bool → LegacyStraightOp m
  | not {m : Nat} : Fin m → LegacyStraightOp m
  | and {m : Nat} : Fin m → Fin m → LegacyStraightOp m
  | or {m : Nat} : Fin m → Fin m → LegacyStraightOp m

/-- Internal straight-line/DAG-with-sharing format (legacy-compatible). -/
structure LegacyStraightLineCircuit (n : Nat) where
  gates : Nat
  gate : (g : Fin gates) → LegacyStraightOp (n + g.1)
  output : Fin (n + gates)

/-- Neutral name used by the in-repo simulation layer. -/
abbrev StraightLineCircuit := LegacyStraightLineCircuit

/--
Translate a wire index in `Fin (n + g)` into a `DagWire n g`.
-/
def toDagWire {n g : Nat} (i : Fin (n + g)) : DagWire n g := by
  classical
  by_cases h : (i : Nat) < n
  · exact .input ⟨i, h⟩
  · have hge : n ≤ (i : Nat) := Nat.le_of_not_gt h
    let j : Nat := (i : Nat) - n
    have hj : j < g := by
      have hi : (i : Nat) < n + g := i.isLt
      dsimp [j]
      omega
    exact .gate ⟨j, hj⟩

/-- Translate an archive gate operation into a `DagGate`. -/
def toDagOp {n g : Nat} : LegacyStraightOp (n + g) → DagGate n g
  | .const b => .const b
  | .not i => .not (toDagWire (n := n) (g := g) i)
  | .and i j => .and (toDagWire (n := n) (g := g) i) (toDagWire (n := n) (g := g) j)
  | .or i j => .or (toDagWire (n := n) (g := g) i) (toDagWire (n := n) (g := g) j)

/-- Translate an archive straight-line circuit into the canonical `DagCircuit`. -/
def toDag {n : Nat} (C : LegacyStraightLineCircuit n) : DagCircuit n where
  gates := C.gates
  gate := fun g => toDagOp (n := n) (g := g.1) (C.gate g)
  output := toDagWire (n := n) (g := C.gates) C.output

/-- Replace the designated output wire of a straight-line circuit. -/
def withOutput {n : Nat} (C : LegacyStraightLineCircuit n)
    (out : Fin (n + C.gates)) : LegacyStraightLineCircuit n where
  gates := C.gates
  gate := C.gate
  output := out

/--
Archive semantics exported through the canonical DAG evaluator.

This definition intentionally delegates execution to `DagCircuit.eval`, so once
the translator is fixed, downstream correctness goals can be stated against a
single semantics.
-/
def eval {n : Nat} (C : LegacyStraightLineCircuit n) (x : Bitstring n) : Bool :=
  DagCircuit.eval (toDag C) x

/-- Evaluate any wire by setting it as output and reusing `eval`. -/
def evalWire {n : Nat} (C : LegacyStraightLineCircuit n) (x : Bitstring n) :
    Fin (n + C.gates) → Bool :=
  fun i => eval (withOutput C i) x

@[simp] theorem eval_toDag {n : Nat} (C : LegacyStraightLineCircuit n) (x : Bitstring n) :
    DagCircuit.eval (toDag C) x = eval C x := rfl

@[simp] theorem size_toDag {n : Nat} (C : LegacyStraightLineCircuit n) :
    (toDag C).size = C.gates + 1 := rfl

@[simp] theorem eval_eq_evalWire {n : Nat} (C : LegacyStraightLineCircuit n)
    (x : Bitstring n) :
    eval C x = evalWire C x C.output := rfl

/--
Generic lifting lemma: any polynomially bounded archive straight-line family
gives membership in `PpolyDAG`.
-/
theorem ppolyDAG_of_straightLine_family
    {L : Language}
    (polyBound : Nat → Nat)
    (polyBound_poly : ∃ c : Nat, ∀ n, polyBound n ≤ n ^ c + c)
    (family : ∀ n, LegacyStraightLineCircuit n)
    (family_size_le : ∀ n, (toDag (family n)).size ≤ polyBound n)
    (correct : ∀ n (x : Bitstring n), eval (family n) x = L n x) :
    PpolyDAG L := by
  refine ⟨{
    polyBound := polyBound
    polyBound_poly := polyBound_poly
    family := fun n => toDag (family n)
    family_size_le := family_size_le
    correct := ?_
  }, trivial⟩
  intro n x
  exact correct n x

theorem ppolyDAG_of_archive_family
    {L : Language}
    (polyBound : Nat → Nat)
    (polyBound_poly : ∃ c : Nat, ∀ n, polyBound n ≤ n ^ c + c)
    (family : ∀ n, LegacyStraightLineCircuit n)
    (family_size_le : ∀ n, (toDag (family n)).size ≤ polyBound n)
    (correct : ∀ n (x : Bitstring n), eval (family n) x = L n x) :
    PpolyDAG L :=
  ppolyDAG_of_straightLine_family polyBound polyBound_poly family family_size_le correct

end ArchiveStraightLineAdapter
end Complexity
end Pnp3
