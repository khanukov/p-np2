/-!
  pnp3/Core/PDTSugar.lean

  Helper lemmas (sugar) for working with PDT (Partial Decision Trees).
  These lemmas simplify proofs in constructive switching cases.

  **Purpose:**
  - Simplify depth and leaves calculations
  - Provide @[simp] lemmas for automatic simplification
  - Enable one-line proofs for common patterns

  **Used in:** Depth2_Constructive.lean for PR-1 (single literal)
-/
import Core.PDT
import Core.BooleanBasics

namespace Pnp3
namespace Core
namespace PDT

/-! ### Depth lemmas -/

/-- Depth of a leaf is zero. -/
@[simp] lemma depth_leaf {n : Nat} (β : Subcube n) :
  PDT.depth (PDT.leaf β) = 0 := rfl

/--
Depth of a node is successor of max of children depths.
This unfolds the recursive definition explicitly.
-/
@[simp] lemma depth_node {n : Nat} (i : Fin n) (L R : PDT n) :
  PDT.depth (PDT.node i L R) = Nat.succ (Nat.max (PDT.depth L) (PDT.depth R)) := rfl

/--
Depth of a node with two leaf children is exactly 1.
This is the key lemma for single literal proofs.
-/
lemma depth_node_leaves {n : Nat} (i : Fin n) (β0 β1 : Subcube n) :
  PDT.depth (PDT.node i (PDT.leaf β0) (PDT.leaf β1)) = 1 := by
  simp [depth_node, depth_leaf]

/-- Depth of left child is bounded by depth of node. -/
lemma depth_left_le {n : Nat} {i : Fin n} {L R : PDT n} :
  PDT.depth L ≤ PDT.depth (PDT.node i L R) := by
  simp [depth_node]
  exact Nat.le_succ_of_le (Nat.le_max_left _ _)

/-- Depth of right child is bounded by depth of node. -/
lemma depth_right_le {n : Nat} {i : Fin n} {L R : PDT n} :
  PDT.depth R ≤ PDT.depth (PDT.node i L R) := by
  simp [depth_node]
  exact Nat.le_succ_of_le (Nat.le_max_right _ _)

/-! ### Leaves lemmas -/

/-- Leaves of a leaf node is singleton list. -/
@[simp] lemma leaves_leaf {n : Nat} (β : Subcube n) :
  PDT.leaves (PDT.leaf β) = [β] := rfl

/-- Leaves of a node is concatenation of children leaves. -/
@[simp] lemma leaves_node {n : Nat} (i : Fin n) (L R : PDT n) :
  PDT.leaves (PDT.node i L R) = PDT.leaves L ++ PDT.leaves R := rfl

/--
Leaves of a node with two leaf children.
This gives us the explicit two-element list.
-/
@[simp] lemma leaves_node_leaves {n : Nat} (i : Fin n) (β0 β1 : Subcube n) :
  PDT.leaves (PDT.node i (PDT.leaf β0) (PDT.leaf β1)) = [β0, β1] := by
  simp [leaves_node, leaves_leaf]

/-- A subcube is in leaves of a leaf iff it equals the leaf subcube. -/
lemma mem_leaves_leaf {n : Nat} {β γ : Subcube n} :
  β ∈ PDT.leaves (PDT.leaf γ) ↔ β = γ := by
  simp [leaves_leaf]

/-- Membership in leaves of a node. -/
lemma mem_leaves_node {n : Nat} {β : Subcube n} {i : Fin n} {L R : PDT n} :
  β ∈ PDT.leaves (PDT.node i L R) ↔ β ∈ PDT.leaves L ∨ β ∈ PDT.leaves R := by
  simp [leaves_node, List.mem_append]

/--
For a node with two leaf children, membership is explicit.
This is crucial for selectors_sub in single literal proof.
-/
lemma mem_leaves_node_leaves {n : Nat} {β β0 β1 : Subcube n} {i : Fin n} :
  β ∈ PDT.leaves (PDT.node i (PDT.leaf β0) (PDT.leaf β1)) ↔ β = β0 ∨ β = β1 := by
  simp [mem_leaves_node, mem_leaves_leaf]

/-! ### List length lemmas -/

/-- Leaves of a leaf has length 1. -/
@[simp] lemma leaves_length_leaf {n : Nat} (β : Subcube n) :
  (PDT.leaves (PDT.leaf β)).length = 1 := by
  simp [leaves_leaf]

/-- Leaves of a node has length equal to sum of children. -/
lemma leaves_length_node {n : Nat} (i : Fin n) (L R : PDT n) :
  (PDT.leaves (PDT.node i L R)).length =
    (PDT.leaves L).length + (PDT.leaves R).length := by
  simp [leaves_node, List.length_append]

/-- Leaves of a node with two leaf children has length 2. -/
@[simp] lemma leaves_length_node_leaves {n : Nat} (i : Fin n) (β0 β1 : Subcube n) :
  (PDT.leaves (PDT.node i (PDT.leaf β0) (PDT.leaf β1))).length = 2 := by
  simp [leaves_length_node]

/-! ### Utility lemmas -/

/--
If a subcube is in the leaves of a tree, it's a valid subcube.
(This is trivially true but useful for type-checking.)
-/
lemma subcube_of_mem_leaves {n : Nat} {β : Subcube n} {t : PDT n}
    (h : β ∈ PDT.leaves t) : β = β := rfl

/--
Non-emptiness: leaves list is always non-empty.
-/
lemma leaves_nonempty {n : Nat} (t : PDT n) :
  (PDT.leaves t).length > 0 := by
  induction t with
  | leaf β => simp
  | node i L R ihL ihR =>
    simp [leaves_length_node]
    omega

end PDT
end Core
end Pnp3
