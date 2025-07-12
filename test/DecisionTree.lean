import Pnp.DecisionTree

open BoolFunc DecisionTree

namespace DecisionTreeTests

/-- A tree with a single leaf has depth zero. -/
example (b : Bool) : depth (DecisionTree.leaf (n:=1) b) = 0 := by
  rfl

end DecisionTreeTests
