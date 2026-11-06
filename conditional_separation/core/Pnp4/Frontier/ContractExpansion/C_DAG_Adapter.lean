import Pnp4.AlgorithmsToLowerBounds.BasicCircuitClasses
import Complexity.Interfaces

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/--
The pnp4 circuit-family view of the frozen pnp3 DAG-circuit model.

This is deliberately only an adapter: the carrier, evaluator, and size measure
are exactly the existing pnp3 `DagCircuit` objects.  In particular, this file
introduces no new endpoint, no source theorem, and no alternative DAG semantics.
-/
def C_DAG : CircuitFamilyClass where
  Family n := Pnp3.ComplexityInterfaces.DagCircuit n
  eval := fun {_} C x => Pnp3.ComplexityInterfaces.DagCircuit.eval C x
  size := fun {_} C => Pnp3.ComplexityInterfaces.DagCircuit.size C

/--
A polynomially bounded non-uniform family from a pnp4 circuit class computing a
language slice-by-slice.

The exponent is stored directly in the `n ^ exponent + exponent` form used by
pnp3 `InPpolyDAG`.  This keeps the adapter theorem mathematically transparent:
there is no hidden asymptotic convention or extra size measure to reconcile.
-/
structure PolynomiallyBoundedFamily
    (C : CircuitFamilyClass)
    (L : BitVecLanguage) where
  exponent : Nat
  family : ∀ n : Nat, C.Family n
  size_le : ∀ n : Nat, C.size (family n) ≤ n ^ exponent + exponent
  correct : ∀ n : Nat, ∀ x : AlgorithmsToLowerBounds.BitVec n, C.eval (family n) x = L n x

/--
Every frozen pnp3 `InPpolyDAG` witness is a polynomially bounded `C_DAG` family.

This is the easy direction: unpack the pnp3 polynomial bound and reuse the very
same DAG family, evaluator, and size proof through the `C_DAG` wrapper.
-/
noncomputable def InPpolyDAG_to_C_DAG_family
    {L : Pnp3.ComplexityInterfaces.Language}
    (h : Pnp3.ComplexityInterfaces.InPpolyDAG L) :
    PolynomiallyBoundedFamily C_DAG L := by
  let c := Classical.choose h.polyBound_poly
  have hc : ∀ n, h.polyBound n ≤ n ^ c + c := Classical.choose_spec h.polyBound_poly
  refine
    { exponent := c
      family := h.family
      size_le := ?_
      correct := ?_ }
  · intro n
    exact Nat.le_trans (h.family_size_le n) (hc n)
  · intro n x
    exact h.correct n x

/--
A polynomially bounded `C_DAG` family computing `L` is exactly a pnp3
`InPpolyDAG` witness for `L`.

The proof is just record repackaging.  The polynomial bound is the explicit
schedule stored in `PolynomiallyBoundedFamily`, and the circuits are already
pnp3 `DagCircuit`s because `C_DAG.Family n` is definitionally that type.
-/
def C_DAG_family_to_InPpolyDAG
    {L : Pnp3.ComplexityInterfaces.Language}
    (h : PolynomiallyBoundedFamily C_DAG L) :
    Pnp3.ComplexityInterfaces.InPpolyDAG L where
  polyBound := fun n => n ^ h.exponent + h.exponent
  polyBound_poly := ⟨h.exponent, fun _ => Nat.le_refl _⟩
  family := h.family
  family_size_le := h.size_le
  correct := h.correct

/--
A pnp3 `PpolyDAG` decider can be exposed as length-indexed `C_DAG` deciders
with one global polynomial exponent.

This corollary is intentionally only an adapter/alignment statement.  It does
not construct an NP lower-bound source, a magnification endpoint, or any
`P != NP` consequence.
-/
theorem PpolyDAG_decider_as_C_DAG_decider
    {L : Pnp3.ComplexityInterfaces.Language}
    (h : Pnp3.ComplexityInterfaces.PpolyDAG L) :
    ∃ c : Nat, ∀ n : Nat, ∃ C : C_DAG.Family n,
      C_DAG.size C ≤ n ^ c + c ∧
        ∀ x : AlgorithmsToLowerBounds.BitVec n, C_DAG.eval C x = L n x := by
  rcases h with ⟨hDAG, _⟩
  let hFamily := InPpolyDAG_to_C_DAG_family hDAG
  refine ⟨hFamily.exponent, ?_⟩
  intro n
  exact ⟨hFamily.family n, hFamily.size_le n, hFamily.correct n⟩

end ContractExpansion
end Frontier
end Pnp4
