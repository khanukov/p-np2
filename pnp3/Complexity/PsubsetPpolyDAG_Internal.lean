import Complexity.PpolyDAG_from_StraightLine

namespace Pnp3
namespace Complexity

open ComplexityInterfaces
open StraightLineAdapter

/--
Constructive packaging of a straight-line non-uniform family for a language.
-/
structure InPpolyStraightLine (L : Language) where
  polyBound : Nat → Nat
  polyBound_poly : ∃ c : Nat, ∀ n, polyBound n ≤ n ^ c + c
  family : ∀ n, StraightLineCircuit n
  family_size_le : ∀ n, (toDag (family n)).size ≤ polyBound n
  correct : ∀ n (x : Bitstring n), eval (family n) x = L n x

/-- Straight-line non-uniform class. -/
def PpolyStraightLine (L : Language) : Prop :=
  ∃ _ : InPpolyStraightLine L, True

/--
Any straight-line witness induces a canonical DAG witness.

The proof is transparent: it directly repackages the witness through `toDag`
and does not rely on an additional black-box reduction lemma.
-/
theorem ppolyDAG_of_ppolyStraightLine {L : Language} :
    PpolyStraightLine L → PpolyDAG L := by
  intro h
  rcases h with ⟨w, _⟩
  refine ⟨{
    polyBound := w.polyBound
    polyBound_poly := w.polyBound_poly
    family := fun n => toDag (w.family n)
    family_size_le := w.family_size_le
    correct := ?_
  }, trivial⟩
  intro n x
  exact w.correct n x

/-- Inclusion target for the straight-line class. -/
def P_subset_PpolyStraightLine : Prop :=
  ∀ L : Language, P L → PpolyStraightLine L

/--
Internal reduction: proving `P ⊆` straight-line non-uniform circuits
is sufficient to obtain `P ⊆ PpolyDAG`.
-/
theorem P_subset_PpolyDAG_of_P_subset_PpolyStraightLine :
    P_subset_PpolyStraightLine → P_subset_PpolyDAG := by
  intro hSL L hPL
  exact ppolyDAG_of_ppolyStraightLine (hSL L hPL)

end Complexity
end Pnp3
