import Pnp2.BoolFunc
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

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

/-- The recorded path never exceeds the depth of the tree. -/
lemma path_to_leaf_length_le_depth (t : DecisionTree n) (x : Point n) :
    (path_to_leaf t x).length ≤ depth t := by
  induction t generalizing x with
  | leaf b =>
      simp [path_to_leaf, depth]
  | node i t0 t1 ih0 ih1 =>
      by_cases h : x i
      · have hlen := ih1 x
        have := Nat.le_trans hlen (Nat.le_max_right (depth t0) (depth t1))
        simpa [path_to_leaf, depth, h] using Nat.succ_le_succ this
      · have hlen := ih0 x
        have := Nat.le_trans hlen (Nat.le_max_left (depth t0) (depth t1))
        simpa [path_to_leaf, depth, h] using Nat.succ_le_succ this

/-- A decision tree with depth `d` has at most `2 ^ d` leaves. -/
lemma leaf_count_le_pow_depth (t : DecisionTree n) :
    leaf_count t ≤ 2 ^ depth t := by
  induction t with
  | leaf b =>
      simp [leaf_count, depth]
  | node i t0 t1 ih0 ih1 =>
      have h0 : leaf_count t0 ≤ 2 ^ max (depth t0) (depth t1) :=
        le_trans ih0 <| by
          have : depth t0 ≤ max (depth t0) (depth t1) := le_max_left _ _
          exact pow_le_pow_right' (by decide : (1 : ℕ) ≤ 2) this
      have h1 : leaf_count t1 ≤ 2 ^ max (depth t0) (depth t1) :=
        le_trans ih1 <| by
          have : depth t1 ≤ max (depth t0) (depth t1) := le_max_right _ _
          exact pow_le_pow_right' (by decide : (1 : ℕ) ≤ 2) this
      have hsum : leaf_count t0 + leaf_count t1 ≤
          2 * 2 ^ max (depth t0) (depth t1) := by
        have := Nat.add_le_add h0 h1
        simpa [two_mul] using this
      have hpow : 2 * 2 ^ max (depth t0) (depth t1) =
          2 ^ (Nat.succ (max (depth t0) (depth t1))) := by
        simp [Nat.pow_succ, Nat.mul_comm]
      simpa [depth, hpow] using hsum

/-- Represent leaves as trivial subcubes.  This will be generalised in later versions. -/
def leaves_as_subcubes : DecisionTree n → Finset (Subcube n)
  | leaf _ => {}
  | node _ t0 t1 => leaves_as_subcubes t0 ∪ leaves_as_subcubes t1

/--
The number of leaf subcubes is bounded by `2 ^ depth`. This follows from
`leaf_count_le_pow_depth` by unfolding the `leaves_as_subcubes` definition
and showing that the number of leaves coincides with the number of trivial
subcubes produced from them. The proof mirrors the version in `pnp` and is
included here so that the legacy `Pnp2` library exposes the same API as the
modern code.
-/
lemma leaves_as_subcubes_card_le_pow_depth (t : DecisionTree n) :
    (leaves_as_subcubes t).card ≤ 2 ^ depth t := by
  induction t with
  | leaf b =>
      simp [leaves_as_subcubes, depth]
  | node i t0 t1 ih0 ih1 =>
      have hunion :
          (leaves_as_subcubes t0 ∪ leaves_as_subcubes t1).card ≤
            (leaves_as_subcubes t0).card + (leaves_as_subcubes t1).card := by
        simpa using
          (Finset.card_union_le (s := leaves_as_subcubes t0)
            (t := leaves_as_subcubes t1))
      have hsum : (leaves_as_subcubes t0).card + (leaves_as_subcubes t1).card ≤
          2 ^ depth t0 + 2 ^ depth t1 := Nat.add_le_add ih0 ih1
      have h0 : 2 ^ depth t0 ≤ 2 ^ max (depth t0) (depth t1) := by
        have : depth t0 ≤ max (depth t0) (depth t1) := le_max_left _ _
        exact pow_le_pow_right' (by decide : (1 : ℕ) ≤ 2) this
      have h1 : 2 ^ depth t1 ≤ 2 ^ max (depth t0) (depth t1) := by
        have : depth t1 ≤ max (depth t0) (depth t1) := le_max_right _ _
        exact pow_le_pow_right' (by decide : (1 : ℕ) ≤ 2) this
      have hsum2 : 2 ^ depth t0 + 2 ^ depth t1 ≤ 2 * 2 ^ max (depth t0) (depth t1) := by
        have := Nat.add_le_add h0 h1
        simpa [two_mul] using this
      have h : (leaves_as_subcubes t0 ∪ leaves_as_subcubes t1).card ≤ 2 * 2 ^ max (depth t0) (depth t1) :=
        le_trans hunion (le_trans hsum hsum2)
      have hpow : 2 * 2 ^ max (depth t0) (depth t1) =
          2 ^ (Nat.succ (max (depth t0) (depth t1))) := by
        simp [Nat.pow_succ, Nat.mul_comm]
      simpa [leaves_as_subcubes, depth, hpow] using h

/--
A convenient alias for `leaves_as_subcubes_card_le_pow_depth` matching the
modern `pnp` library. It states the depth bound using the short name
`tree_depth_bound`.
-/
lemma tree_depth_bound (t : DecisionTree n) :
    (leaves_as_subcubes t).card ≤ 2 ^ depth t :=
  leaves_as_subcubes_card_le_pow_depth (t := t)

/--
Subcube corresponding to a recorded path.  Each pair `(i, b)` fixes
coordinate `i` to the Boolean value `b`.
Later occurrences overwrite earlier ones. -/
def subcube_of_path : List (Fin n × Bool) → Subcube n
  | [] =>
      { idx := {},
        val := by
          intro i h
          exact False.elim (Finset.notMem_empty _ h) }
  | (i, b) :: p =>
      let R := subcube_of_path p
      { idx := insert i R.idx,
        val := by
          intro j hj
          by_cases hji : j = i
          · subst hji; exact b
          · have hjR : j ∈ R.idx := by
              rcases Finset.mem_insert.mp hj with hj | hj
              · exact False.elim (hji hj)
              · exact hj
            exact R.val j hjR }

@[simp] lemma mem_subcube_of_path_nil (x : Point n) :
    (subcube_of_path (n := n) []).mem x := by
  intro i hi
  exact False.elim (Finset.notMem_empty _ hi)

@[simp] lemma subcube_of_path_nil_idx :
    (subcube_of_path (n := n) ([] : List (Fin n × Bool))).idx = ({} : Finset (Fin n)) :=
  rfl

@[simp] lemma subcube_of_path_cons_idx (i : Fin n) (b : Bool) (p : List (Fin n × Bool)) :
    (subcube_of_path ((i, b) :: p)).idx = insert i (subcube_of_path p).idx :=
  rfl

/-!
Collect all leaf subcubes of a decision tree together with their Boolean labels.
The helper `coloredSubcubesAux` threads the current path as an accumulator.
-/

/- Auxiliary recursion accumulating the path to the current node.  The list `p`
   stores the coordinate decisions made so far. -/
def coloredSubcubesAux : DecisionTree n → List (Fin n × Bool) →
    Finset (Bool × Subcube n)
  | leaf b, p => {⟨b, subcube_of_path p⟩}
  | node i t0 t1, p =>
      coloredSubcubesAux t0 ((i, false) :: p) ∪
        coloredSubcubesAux t1 ((i, true) :: p)

/-- All coloured subcubes of a decision tree. -/
def coloredSubcubes (t : DecisionTree n) : Finset (Bool × Subcube n) :=
  coloredSubcubesAux t []

@[simp] lemma coloredSubcubesAux_leaf (b : Bool) (p : List (Fin n × Bool)) :
    coloredSubcubesAux (n := n) (leaf b) p = {⟨b, subcube_of_path p⟩} := by
  simp [coloredSubcubesAux]

@[simp] lemma coloredSubcubes_leaf (b : Bool) :
  coloredSubcubes (n := n) (leaf b) = {⟨b, subcube_of_path (n := n) []⟩} := by
  simp [coloredSubcubes]

/-!
The number of coloured subcubes produced by a decision tree does not
exceed the number of leaves.  This technical lemma is useful when
bounding the overall size of decision-tree based covers.
-/
lemma coloredSubcubesAux_card_le_leaf_count (t : DecisionTree n)
    (p : List (Fin n × Bool)) :
    (coloredSubcubesAux (n := n) t p).card ≤ leaf_count t := by
  classical
  induction t generalizing p with
  | leaf b =>
      simp [coloredSubcubesAux, leaf_count]
  | node i t0 t1 ih0 ih1 =>
      have h0 := ih0 ((i, false) :: p)
      have h1 := ih1 ((i, true) :: p)
      have hunion :
          (coloredSubcubesAux t0 ((i, false) :: p) ∪
            coloredSubcubesAux t1 ((i, true) :: p)).card ≤
            (coloredSubcubesAux t0 ((i, false) :: p)).card +
              (coloredSubcubesAux t1 ((i, true) :: p)).card := by
        simpa using
          (Finset.card_union_le (s := coloredSubcubesAux t0 ((i, false) :: p))
            (t := coloredSubcubesAux t1 ((i, true) :: p)))
      have hsum :
          (coloredSubcubesAux t0 ((i, false) :: p)).card +
            (coloredSubcubesAux t1 ((i, true) :: p)).card ≤
              leaf_count t0 + leaf_count t1 :=
        Nat.add_le_add h0 h1
      have h := le_trans hunion hsum
      simpa [coloredSubcubesAux, leaf_count] using h

lemma coloredSubcubes_card_le_leaf_count (t : DecisionTree n) :
    (coloredSubcubes (n := n) t).card ≤ leaf_count t := by
  simpa [coloredSubcubes] using
    (coloredSubcubesAux_card_le_leaf_count (n := n) (t := t) (p := []))

/-- The number of coloured subcubes of a decision tree is bounded by
`2 ^ depth`.  This follows from `coloredSubcubes_card_le_leaf_count` and
`leaf_count_le_pow_depth`. -/
lemma coloredSubcubes_card_le_pow_depth (t : DecisionTree n) :
    (coloredSubcubes (n := n) t).card ≤ 2 ^ depth t := by
  have h₁ := coloredSubcubes_card_le_leaf_count (n := n) (t := t)
  have h₂ := leaf_count_le_pow_depth (t := t)
  exact le_trans h₁ h₂

/-- Evaluate a leaf. -/
@[simp] lemma eval_tree_leaf (b : Bool) (x : Point n) :
    eval_tree (leaf b) x = b := rfl

/-- Evaluate a node. -/
@[simp] lemma eval_tree_node (i : Fin n) (t0 t1 : DecisionTree n) (x : Point n) :
    eval_tree (node i t0 t1) x = (if x i then eval_tree t1 x else eval_tree t0 x) := by
  by_cases h : x i
  · simp [eval_tree, h]
  · simp [eval_tree, h]

/-- Extend membership in a path subcube by fixing one more coordinate. -/
lemma mem_subcube_of_path_cons_of_mem (x : Point n) (p : List (Fin n × Bool))
    (i : Fin n) (b : Bool)
    (hx : (subcube_of_path p).mem x) (hxi : x i = b) :
    (subcube_of_path ((i, b) :: p)).mem x := by
  intro j hj
  rcases Finset.mem_insert.mp hj with hj | hj
  · subst hj; simpa [subcube_of_path, hxi]
  · have hxj := hx j hj
    by_cases hji : j = i
    · subst hji; simpa [subcube_of_path, hxi] using hxi
    · simp [subcube_of_path, hj, hji, hxj]

/-- Every input lies in the subcube described by its path to a leaf. -/
lemma mem_subcube_of_path_path_to_leaf (t : DecisionTree n) (x : Point n) :
    (subcube_of_path (path_to_leaf t x)).mem x := by
  induction t generalizing x with
  | leaf b =>
      simpa [path_to_leaf, subcube_of_path] using
        (mem_subcube_of_path_nil (n := n) (x := x))
  | node i t0 t1 ih0 ih1 =>
      by_cases h : x i
      · have h' := ih1 x
        simpa [path_to_leaf, h] using
          mem_subcube_of_path_cons_of_mem (x := x) (p := path_to_leaf t1 x)
            (i := i) (b := true) h' (by simpa [h])
      · have h' := ih0 x
        simpa [path_to_leaf, h] using
          mem_subcube_of_path_cons_of_mem (x := x) (p := path_to_leaf t0 x)
            (i := i) (b := false) h' (by simpa [h])

end DecisionTree

end BoolFunc
