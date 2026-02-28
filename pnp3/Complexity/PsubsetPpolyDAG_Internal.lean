import Complexity.PpolyDAG_from_ArchiveStraightLine

namespace Pnp3
namespace Complexity

open ComplexityInterfaces
open ArchiveStraightLineAdapter

/--
Constructive packaging of a straight-line non-uniform family for a language.
This is the exact input required by `ppolyDAG_of_straightLine_family`.
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

/-- Any straight-line witness induces a canonical DAG witness. -/
theorem ppolyDAG_of_ppolyStraightLine {L : Language} :
    PpolyStraightLine L → PpolyDAG L := by
  intro h
  rcases h with ⟨w, _⟩
  exact ppolyDAG_of_straightLine_family
    (polyBound := w.polyBound)
    (polyBound_poly := w.polyBound_poly)
    (family := w.family)
    (family_size_le := w.family_size_le)
    (correct := w.correct)

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

/- Backward-compatibility aliases during migration. -/
abbrev InPpolyLegacyStraight := InPpolyStraightLine
abbrev PpolyLegacyStraight := PpolyStraightLine
abbrev P_subset_PpolyLegacyStraight := P_subset_PpolyStraightLine
theorem ppolyDAG_of_ppolyLegacyStraight {L : Language} :
    PpolyLegacyStraight L → PpolyDAG L :=
  ppolyDAG_of_ppolyStraightLine
theorem P_subset_PpolyDAG_of_P_subset_PpolyLegacyStraight :
    P_subset_PpolyLegacyStraight → P_subset_PpolyDAG :=
  P_subset_PpolyDAG_of_P_subset_PpolyStraightLine

end Complexity
end Pnp3
