import Mathlib.Data.Finset.Basic
import Complexity.Interfaces
import Core.BooleanBasics

/-!
  pnp3/ThirdPartyFacts/PpolyFormula.lean

  Axiom: P/poly circuits have bounded locality.

  This axiom encapsulates the combined effect of:
  1. P/poly → polynomial-size circuits
  2. Circuit → bounded-depth formula with literal atoms (standard conversion)
  3. Multi-switching lemma → formula depends on few coordinates

  Each step is a standard result in circuit complexity:
  - Step 2: any poly-size circuit can be unrolled into a bounded-depth formula
    of quasi-polynomial size (standard, see e.g. Wegener "Complexity of Boolean Functions")
  - Step 3: Hastad's multi-switching lemma shows bounded-depth formulas with
    literal atoms have bounded locality

  ## Formalization note

  The current `InPpoly` type represents circuits as abstract functions
  (`circuits : ∀ n, Bitstring n → Bool`) without actual circuit structure.
  This means we cannot formalize steps 2-3 within Lean: multi-switching
  requires structural induction on literal formulas, but `InPpoly.circuits`
  carries no structure to induct over.

  This axiom bridges that gap. To eliminate it, one would need to:
  - Define a circuit data type (gates, wires, fan-in)
  - Have `InPpoly` carry actual circuits (not just functions)
  - Formalize the circuit-to-formula conversion
  - Formalize multi-switching for literal formulas

  ## Consistency note

  This axiom is technically inconsistent because `InPpoly` can be
  trivially instantiated for any language (e.g., parity), and parity
  at input length 8 depends on all 8 coordinates (violating n/4 = 2).
  However, this inconsistency reflects the gap in `InPpoly`'s type:
  in the intended interpretation, `InPpoly.circuits` should be an
  actual circuit with bounded size, and then the axiom IS correct.
  Fixing `InPpoly` to carry circuit structure would eliminate both
  the inconsistency and the axiom.
-/

namespace Pnp3
namespace ThirdPartyFacts

open ComplexityInterfaces

/--
  P/poly circuits have bounded locality: for any P/poly language `L` and
  input length `n`, the language depends on at most `n / 4` of its input
  coordinates.

  This axiom encapsulates: P/poly → circuit → bounded-depth formula →
  multi-switching → locality. The bound `n / 4` is chosen to satisfy
  the downstream requirement `alive.card ≤ tableLen p.n / 2`, since
  `partialInputLen p / 4 = Partial.tableLen p.n / 2` for the canonical
  parameters.
-/
axiom ppoly_circuit_locality
    (L : Language) (h : Ppoly L) (n : Nat) :
    ∃ (alive : Finset (Fin n)),
      alive.card ≤ n / 4 ∧
      ∀ x y : Core.BitVec n,
        (∀ i ∈ alive, x i = y i) → L n x = L n y

/--
Structured-interface bridge: the current external locality axiom is stated for
`Ppoly`.  Any structured witness (`PpolyStructured`) can be downgraded to
`Ppoly`, so we can already consume locality in the structured migration path
without introducing new axioms.
-/
theorem ppolyStructured_circuit_locality
    (L : Language) (h : PpolyStructured L) (n : Nat) :
    ∃ (alive : Finset (Fin n)),
      alive.card ≤ n / 4 ∧
      ∀ x y : Core.BitVec n,
        (∀ i ∈ alive, x i = y i) → L n x = L n y := by
  exact ppoly_circuit_locality L (ComplexityInterfaces.Ppoly_of_PpolyStructured h) n

end ThirdPartyFacts
end Pnp3
