import Pnp2.DecisionTree

open BoolFunc

namespace Pnp2LegacyTests

/-- A trivial tree has depth zero and one leaf subcube. -/
example :
    (DecisionTree.leaves_as_subcubes (DecisionTree.leaf true : DecisionTree 1)).card = 0 :=
by
  simp [DecisionTree.leaves_as_subcubes]

/-- The depth bound lemma from the legacy library. -/
example (t : DecisionTree 2) :
    (DecisionTree.leaves_as_subcubes t).card ≤ 2 ^ DecisionTree.depth t :=
by
  simpa using DecisionTree.tree_depth_bound (t := t)

end Pnp2LegacyTests
