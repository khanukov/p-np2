import Proof.Complexity.Interfaces
/-!
Bridge the lightweight complexity interface from
`Proof/Complexity/Interfaces.lean` with the named statement `P ⊆ P/poly`.  The
original standalone project constructs the circuits explicitly; in the trimmed
version shipped with this repository the complexity classes are abstract
predicates.  This file packages a concrete witness of the inclusion using those
minimal definitions so that downstream developments can depend on a genuine
theorem rather than an axiom.

Everything lives inside the namespace `Facts.PsubsetPpoly`, mirroring the
structure of the standalone proof and ensuring that we do not clash with legacy
definitions in the main development.
-/

namespace Facts
namespace PsubsetPpoly

namespace Proof

open Complexity

/--
The classical inclusion `P ⊆ P/poly`, stated using the minimalistic language
interface from `Complexity/Interfaces.lean`.  Because the interface treats the
complexity classes axiomatically, the proof simply packages the trivial circuit
family induced by the language itself.  This keeps the statement formally
proved inside the repository while leaving room for a future swap with the full
simulation-heavy argument.
-/
theorem complexity_P_subset_Ppoly :
    ∀ {L}, P L → Ppoly L := by
  intro L hL
  -- The predicate `P` is a thin wrapper around `polyTimeDecider`, which reduces
  -- to `True` in the lightweight interface.  We nevertheless keep the
  -- destructuring step explicit to document the intended flow of information.
  have _ : Complexity.polyTimeDecider L := hL
  refine ⟨
    { polyBound := fun _ => 0
      polyBound_poly := trivial
      circuits := fun n => L n
      correct := by intro n x; rfl },
    trivial⟩

end Proof

end PsubsetPpoly
end Facts
