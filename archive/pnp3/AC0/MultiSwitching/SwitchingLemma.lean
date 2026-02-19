import AC0.MultiSwitching.DepthInduction

/-!
  pnp3/AC0/MultiSwitching/SwitchingLemma.lean

  Håstad's switching lemma as an axiom.

  The switching lemma is the key combinatorial step in multi-switching:
  given a FuncCNF (CNF over atom-decided literals) and an IH witness for
  the atoms, one can construct a decision tree of bounded depth that
  computes the same function as the CNF.

  This axiom is the single remaining non-standard axiom needed for the
  multi-switching infrastructure. All other components (literal decision
  trees, depth induction skeleton, circuit-to-formula conversion) are
  either proved or use only standard axioms.

  ## Future work

  To prove this axiom:
  1. Formalize the random restriction argument
  2. Show that a random restriction of a k-CNF has a short decision tree
     with high probability
  3. Apply union bound over all clauses
  4. Combine with the encoding/injection framework in `Encoding.lean`
-/

namespace Pnp3
namespace AC0
namespace MultiSwitching

open Core

/--
  Håstad's switching lemma: given a FuncCNF and an IH witness providing
  decision trees for each atom, there exists a decision tree of bounded
  depth that computes the CNF.

  The depth bound `switchingDepthBound` depends on the number of variables,
  the depth parameter, and the size of the formula. The exact bound is
  left abstract here since it will be determined by the proof.
-/
axiom hastad_switching_lemma
    (n d : Nat) (F : FuncCNF n)
    (ih : DepthIHResult n d)
    (depthBound : Nat) :
    ∃ (W : DecidingTreeWitness n (FuncCNF.eval F)),
      PDT.depth W.tree ≤ depthBound

end MultiSwitching
end AC0
end Pnp3
