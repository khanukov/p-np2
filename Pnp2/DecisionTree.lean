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

/-! ### Membership lemmas for `subcube_of_path`
These helper lemmas will be convenient when reasoning about
paths extracted from a decision tree.  They mirror the structure
of the path and show how membership in the corresponding subcube
is checked coordinatewise. -/

@[simp] lemma mem_subcube_of_path_cons {x : Point n} {i : Fin n}
    {b : Bool} {p : List (Fin n × Bool)} :
    (subcube_of_path ((i, b) :: p)).mem x ↔ x i = b ∧ (subcube_of_path p).mem x := by
  constructor
  · intro hx
    constructor
    · -- The head constraint forces coordinate `i` to equal `b`.
      have hmem : i ∈ insert i (subcube_of_path p).idx := by simp
      simpa using hx i hmem
    · -- Remaining coordinates satisfy the tail subcube.
      have hp : (subcube_of_path p).mem x := by
        intro j hj
        have hmem : j ∈ insert i (subcube_of_path p).idx := by
          exact Finset.mem_insert.mpr (Or.inr hj)
        have hxj := hx j hmem
        by_cases hji : j = i
        · subst hji
          have hmemi : i ∈ insert i (subcube_of_path p).idx := by simp
          simpa using hx i hmemi
        · simpa [subcube_of_path, hji, hj] using hxj
      exact hp
  · intro hx
    rcases hx with ⟨hi, hp⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with hji | hjp
    · subst hji; simpa using hi
    · have hxj := hp j hjp
      simpa [subcube_of_path, hjp] using hxj

/-! The recorded path from `path_to_leaf` indeed describes a subcube
containing the original input. -/
lemma mem_subcube_path_to_leaf (t : DecisionTree n) (x : Point n) :
    (subcube_of_path (path_to_leaf t x)).mem x := by
  induction t generalizing x with
  | leaf b =>
      simp [path_to_leaf, subcube_of_path]
  | node i t0 t1 ih0 ih1 =>
      by_cases h : x i
      · have := ih1 x
        simp [path_to_leaf, subcube_of_path, h] at this
        exact this
      · have := ih0 x
        simp [path_to_leaf, subcube_of_path, h] at this
        exact this

end DecisionTree

end BoolFunc
