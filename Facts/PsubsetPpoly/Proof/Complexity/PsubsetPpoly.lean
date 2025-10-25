import Proof.Complexity.Interfaces
import Proof.Simulation

/-!
Bridge the constructive proof of `P ⊆ P/poly` with the high-level complexity
class interface.  By separating this file from `Complexity/Interfaces.lean` we
avoid a circular import between the class definitions and the simulation
infrastructure.

The module lives at the outer layer of the `FactPsubsetPpoly` package.  It is the
only place where the bare-hands simulation developed in `Proof/Simulation` is
converted into the abstract language inclusion statement.  Because no other
definitions are introduced here, downstream projects can import this file to
reuse the final theorem without accumulating any extra baggage from the
intermediate construction.

Here we explicitly expose the surrounding `Facts.PsubsetPpoly` namespace so the
inclusion theorem does not collide with the equally named statement in the
legacy codebase.
-/

namespace Facts
namespace PsubsetPpoly

namespace Proof

open Complexity

/--
The classical inclusion `P ⊆ P/poly`, restated in terms of the language
interface from `Complexity/Interfaces.lean`.  Every ingredient referenced in the
proof is defined inside the standalone package, so importing this module gives a
self-contained witness of the inclusion that can be reused verbatim.
-/
theorem complexity_P_subset_Ppoly :
    P ⊆ Ppoly := by
  intro L hL
  rcases hL with ⟨M, c, hRun, hCorrect⟩
  refine ⟨Complexity.inPpoly_of_polyBound (M := M) (c := c) hRun hCorrect, trivial⟩

end Proof

end PsubsetPpoly
end Facts
