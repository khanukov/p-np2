import Pnp4.Frontier.StreamingMagnification.StandardDAGMCSP
import Mathlib.Tactic

/-!
# Total search-MCSP semantics for standard DAG circuits

The table coordinate `i : Fin (2 ^ n)` is interpreted as the `i`-th
assignment in lexicographic order, from `0^n` to `1^n`.  Coordinate zero of
an assignment is its most significant bit.  This convention is deliberately
separate from the least-significant-bit convention used by the older
tree/formula MCSP surface.

The result below is total and tagged.  Its `noCircuit` branch asserts genuine
non-existence, rather than relying on a YES-only promise.  This module fixes
the semantic target and proves the decision/search bridge.  The serialized
fixed-length circuit code and executable exhaustive reference solver live in
`DAGCodec` and the later executable layer; no classical choice is used here
to pretend that this specification is an algorithm.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace TotalSearch

open Pnp3.ComplexityInterfaces
open StandardDAG

/-- An `N = 2^n`-bit truth table for a function on `n` inputs. -/
abbrev TruthTable (n : Nat) := Fin (2 ^ n) -> Bool

/--
The `index`-th Boolean assignment in paper lexicographic order.  Input
coordinate zero is the most significant bit, so for `n = 2` the indices
enumerate `00, 01, 10, 11`.
-/
def lexInput (n : Nat) (index : Fin (2 ^ n)) : Bitstring n :=
  fun coordinate =>
    Nat.testBit index.val (n - 1 - coordinate.val)

/-- The lexicographically ordered truth table computed by a standard DAG. -/
def circuitTruthTable {n : Nat} (circuit : FlatCircuit n) : TruthTable n :=
  fun index => circuit.eval (lexInput n index)

/-- Exact computation of the supplied lexicographic truth table. -/
def Computes {n : Nat} (circuit : FlatCircuit n) (table : TruthTable n) : Prop :=
  circuitTruthTable circuit = table

/-- Exact DAG-MCSP YES predicate at an internal-gate threshold. -/
def HasCircuit (n threshold : Nat) (table : TruthTable n) : Prop :=
  Exists fun circuit : FlatCircuit n =>
    circuit.gateCount <= threshold /\
      circuit.UsesOnlyAndOrNot /\ Computes circuit table

/-- A valid standard DAG bundled with the paper's internal-gate bound. -/
abbrev BoundedCircuit (n threshold : Nat) :=
  { circuit : FlatCircuit n // circuit.gateCount <= threshold }

/--
Semantic tagged search result.  Unlike a promise relation, this type has an
explicit negative constructor.  A later wire-format result carries the
fixed-length serialized code; this proof-level carrier keeps the four
correctness directions transparent.
-/
inductive MCSPResult (n threshold : Nat) where
  | found (circuit : BoundedCircuit n threshold)
  | noCircuit

/-- Exact total-search correctness, including the NO branch. -/
def Correct {n threshold : Nat} (table : TruthTable n) :
    MCSPResult n threshold -> Prop
  | .found circuit => circuit.val.UsesOnlyAndOrNot /\ Computes circuit.val table
  | .noCircuit => Not (HasCircuit n threshold table)

/-- A found result contains a valid bounded DAG computing the whole table. -/
theorem found_sound
    {n threshold : Nat} {table : TruthTable n}
    {circuit : BoundedCircuit n threshold}
    (hCorrect : Correct table (.found circuit)) :
    circuit.val.gateCount <= threshold /\
      circuit.val.UsesOnlyAndOrNot /\ Computes circuit.val table :=
  ⟨circuit.property, hCorrect⟩

/-- If a suitable circuit exists, a correct total result cannot be NO. -/
theorem exists_implies_result_found
    {n threshold : Nat} {table : TruthTable n}
    {result : MCSPResult n threshold}
    (hCorrect : Correct table result)
    (hExists : HasCircuit n threshold table) :
    Exists fun circuit : BoundedCircuit n threshold =>
      result = .found circuit := by
  cases result with
  | found circuit => exact ⟨circuit, rfl⟩
  | noCircuit => exact (hCorrect hExists).elim

/-- A correct `noCircuit` result proves genuine non-existence. -/
theorem noCircuit_sound
    {n threshold : Nat} {table : TruthTable n}
    (hCorrect : Correct table (MCSPResult.noCircuit : MCSPResult n threshold)) :
    Not (HasCircuit n threshold table) :=
  hCorrect

/-- If no suitable circuit exists, every correct total result is NO. -/
theorem noCircuit_complete
    {n threshold : Nat} {table : TruthTable n}
    {result : MCSPResult n threshold}
    (hCorrect : Correct table result)
    (hNone : Not (HasCircuit n threshold table)) :
    result = .noCircuit := by
  cases result with
  | found circuit =>
      exact (hNone ⟨circuit.val, circuit.property, hCorrect.1, hCorrect.2⟩).elim
  | noCircuit => rfl

/-- The decision bit read from a tagged total-search result. -/
def decisionBit {n threshold : Nat} : MCSPResult n threshold -> Bool
  | .found _ => true
  | .noCircuit => false

/-- Total search immediately yields exact decision MCSP. -/
theorem decisionBit_eq_true_iff
    {n threshold : Nat} {table : TruthTable n}
    {result : MCSPResult n threshold}
    (hCorrect : Correct table result) :
    decisionBit result = true <-> HasCircuit n threshold table := by
  cases result with
  | found circuit =>
      constructor
      · intro _
        exact ⟨circuit.val, circuit.property, hCorrect.1, hCorrect.2⟩
      · intro _
        rfl
  | noCircuit =>
      constructor
      · intro h
        simp [decisionBit] at h
      · intro h
        exact (hCorrect h).elim

/-- Materialize the table in the exact left-to-right stream order. -/
def tableBits {n : Nat} (table : TruthTable n) : List Bool :=
  List.ofFn table

@[simp]
theorem tableBits_length {n : Nat} (table : TruthTable n) :
    (tableBits table).length = 2 ^ n := by
  simp [tableBits]

/-! Small reduction checks for the declared lexicographic convention. -/

example : lexInput 2 ⟨0, by decide⟩ ⟨0, by decide⟩ = false := by decide
example : lexInput 2 ⟨1, by decide⟩ ⟨1, by decide⟩ = true := by decide
example : lexInput 2 ⟨2, by decide⟩ ⟨0, by decide⟩ = true := by decide
example : lexInput 2 ⟨3, by decide⟩ ⟨1, by decide⟩ = true := by decide

end TotalSearch
end StreamingMagnification
end Frontier
end Pnp4
