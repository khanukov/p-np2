import Pnp2.BoolFunc

namespace BoolFunc

/--
  Simple decision-tree structure for Boolean functions on `n` bits.
  Each internal node queries a coordinate `i` and branches on its value.
-/
inductive DecisionTree (n : ℕ) where
  | leaf : Bool → DecisionTree n
  | node : Fin n → DecisionTree n → DecisionTree n → DecisionTree n
  deriving Repr

namespace DecisionTree

variable {n : ℕ}

/-- Depth of a decision tree. -/
def depth : DecisionTree n → Nat
  | leaf _ => 0
  | node _ t0 t1 => Nat.succ (max (depth t0) (depth t1))

/-- Number of leaves in a decision tree. -/
def leaf_count : DecisionTree n → Nat
  | leaf _ => 1
  | node _ t0 t1 => leaf_count t0 + leaf_count t1

/-- Evaluate the tree on an input point. -/
def eval_tree : DecisionTree n → Point n → Bool
  | leaf b, _ => b
  | node i t0 t1, x => by
      by_cases h : x i
      · exact eval_tree t1 x
      · exact eval_tree t0 x

/-- Path taken by an input to reach a leaf. -/
def path_to_leaf : DecisionTree n → Point n → List (Fin n × Bool)
  | leaf _, _ => []
  | node i t0 t1, x => by
      by_cases h : x i
      · exact (i, true) :: path_to_leaf t1 x
      · exact (i, false) :: path_to_leaf t0 x

/-- Represent leaves as trivial subcubes.  This will be generalised in later versions. -/
def leaves_as_subcubes : DecisionTree n → Finset (Subcube n)
  | leaf _ => {}
  | node _ t0 t1 => leaves_as_subcubes t0 ∪ leaves_as_subcubes t1

/-- Subcube corresponding to a recorded path.  Currently returns a trivial subcube. -/
def subcube_of_path (_p : List (Fin n × Bool)) : Subcube n :=
  { idx := ({} : Finset (Fin n)),
    val := by
      intro i h
      exact False.elim (by simpa using h) }

end DecisionTree

end BoolFunc
