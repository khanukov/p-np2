import Pnp2.BoolFunc
import Pnp2.BoolFunc.Sensitivity
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

namespace BoolFunc

-- Silence auxiliary linter warnings in this foundational file.
set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

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

/-- `agreesWithAssignments x p` means that the point `x` satisfies all assignments
in the list `p`.  Each pair `(i, b)` in `p` demands that the `i`-th coordinate of
`x` equals `b`. -/
def agreesWithAssignments (x : Point n) (p : List (Fin n × Bool)) : Prop :=
  ∀ q ∈ p, x q.1 = q.2

@[simp] lemma agreesWithAssignments_nil (x : Point n) :
    agreesWithAssignments (n := n) x [] := by
  intro q hq; cases hq

lemma agreesWithAssignments_cons {x : Point n} {i : Fin n} {b : Bool}
    {p : List (Fin n × Bool)} :
    agreesWithAssignments (n := n) x ((i, b) :: p) ↔
      x i = b ∧ agreesWithAssignments (n := n) x p := by
  constructor
  · intro h; refine ⟨h (i, b) (by simp), ?_⟩
    intro q hq; exact h q (List.mem_cons.mpr (Or.inr hq))
  · rintro ⟨hx, hrest⟩ q hq
    have := List.mem_cons.mp hq
    cases this with
    | inl hq' => cases hq'; simpa using hx
    | inr hq' => exact hrest q hq'



/-- Depth of a decision tree. -/
def depth : DecisionTree n → Nat
  | leaf _ => 0
  | node _ t0 t1 => Nat.succ (max (depth t0) (depth t1))

/-- Number of leaves in a decision tree. -/
def leaf_count : DecisionTree n → Nat
  | leaf _ => 1
  | node _ t0 t1 => leaf_count t0 + leaf_count t1

/-- A decision tree always has at least one leaf. -/
lemma leaf_count_pos (t : DecisionTree n) : 0 < leaf_count t := by
  induction t with
  | leaf b =>
      simp [leaf_count]
  | node i t0 t1 ih0 ih1 =>
      have : 0 < leaf_count t0 + leaf_count t1 :=
        Nat.add_pos_left (n := leaf_count t1) ih0
      simpa [leaf_count] using this

/-- Evaluate the tree on an input point. -/
def eval_tree : DecisionTree n → Point n → Bool
  | leaf b, _ => b
  | node i t0 t1, x => by
      by_cases h : x i
      · exact eval_tree t1 x
      · exact eval_tree t0 x

/-- Evaluate a leaf. -/
@[simp] lemma eval_tree_leaf (b : Bool) (x : Point n) :
    eval_tree (leaf b) x = b := rfl

/-- Evaluate a node. -/
@[simp] lemma eval_tree_node (i : Fin n) (t0 t1 : DecisionTree n) (x : Point n) :
    eval_tree (node i t0 t1) x =
      (if x i then eval_tree t1 x else eval_tree t0 x) := by
  by_cases h : x i
  · simp [eval_tree, h]
  · simp [eval_tree, h]

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

/--
`ofAssignments p b` builds a decision tree that sequentially checks the
assignments listed in `p`.  If the input point satisfies every pair `(i, v)` in
`p`, evaluation returns the Boolean `b`.  The first mismatch immediately
terminates the search with the opposite colour `!b`.

This constructor will later allow us to convert a (possibly large) set of fixed
coordinates into a shallow branch of the full decision tree.
-/
def ofAssignments : List (Fin n × Bool) → Bool → DecisionTree n
  | [], b => leaf b
  | (i, v) :: p, b =>
      if v then
        -- The coordinate `i` should be `true`.  The `false` branch is rejected
        -- immediately with the opposite colour, while the `true` branch
        -- continues checking the remaining assignments.
        node i (leaf (!b)) (ofAssignments p b)
      else
        -- Symmetrically, expect `x i = false`.
        node i (ofAssignments p b) (leaf (!b))

/--
Evaluating `ofAssignments p b` on a point that agrees with all assignments in
`p` yields the colour `b`.
-/
lemma eval_ofAssignments_of_agrees {p : List (Fin n × Bool)} {x : Point n}
    {b : Bool} (hx : agreesWithAssignments (n := n) x p) :
    eval_tree (ofAssignments (n := n) p b) x = b := by
  induction p with
  | nil =>
      -- No assignments: the tree is a single leaf.
      simp [ofAssignments] at hx ⊢
  | cons hd tl ih =>
      -- Break down the agreement condition for the head and tail.
      rcases hd with ⟨i, v⟩
      have h := (agreesWithAssignments_cons (x := x) (i := i) (b := v)
        (p := tl)).1 hx
      rcases h with ⟨hix, htl⟩
      -- The head assignment determines which branch is taken.
      cases v
      · -- Expect `x i = false`.
        simp [ofAssignments, hix, ih htl]
      · -- Expect `x i = true`.
        simp [ofAssignments, hix, ih htl]

/--
The depth of `ofAssignments p b` is bounded by the length of the assignment
list.  Each pair `(i, v)` contributes at most one additional level.
-/
lemma depth_ofAssignments_le {p : List (Fin n × Bool)} {b : Bool} :
    depth (ofAssignments (n := n) p b) ≤ p.length := by
  induction p with
  | nil =>
      simp [ofAssignments, depth]
  | cons hd tl ih =>
      rcases hd with ⟨i, v⟩
      -- The constructed node adds one level atop the recursion on `tl`.
      have h := Nat.succ_le_succ ih
      cases v
      · simpa [ofAssignments, depth, List.length] using h
      · simpa [ofAssignments, depth, List.length] using h

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
The set of subcubes obtained from the leaves may identify duplicate leaves.
Consequently, its cardinality never exceeds the raw leaf count.
-/
lemma leaves_as_subcubes_card_le_leaf_count (t : DecisionTree n) :
    (leaves_as_subcubes t).card ≤ leaf_count t := by
  induction t with
  | leaf b =>
      simp [leaves_as_subcubes, leaf_count]
  | node i t0 t1 ih0 ih1 =>
      -- First bound the union by the sum of the cardinalities.
      have h_union :=
        (Finset.card_union_le (s := leaves_as_subcubes t0)
          (t := leaves_as_subcubes t1))
      -- Combine with the inductive hypotheses for the two subtrees.
      have h :=
        le_trans h_union (Nat.add_le_add ih0 ih1)
      -- Clean up the arithmetic to match the goal statement.
      simpa [leaves_as_subcubes, leaf_count,
             Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

/--
The number of leaf subcubes is bounded by `2 ^ depth`. This is a direct
consequence of `leaves_as_subcubes_card_le_leaf_count` and the bound on the
total number of leaves.
-/
lemma leaves_as_subcubes_card_le_pow_depth (t : DecisionTree n) :
    (leaves_as_subcubes t).card ≤ 2 ^ depth t := by
  -- Relate the number of distinct leaf subcubes to the raw leaf count.
  have h_leaves := leaves_as_subcubes_card_le_leaf_count (t := t)
  -- Bound the leaf count by a power of two using the depth estimate.
  have h_depth := leaf_count_le_pow_depth (t := t)
  exact le_trans h_leaves h_depth

/--
A convenient alias for `leaves_as_subcubes_card_le_pow_depth` matching the
the legacy library. It states the depth bound using the short name
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

lemma subcube_of_path_cons (i : Fin n) (b : Bool) (p : List (Fin n × Bool)) :
    subcube_of_path ((i, b) :: p) = (subcube_of_path p).extend i b := by
  classical
  -- Two subcubes are equal once their index sets and assigned values coincide.
  refine Subcube.ext ?_ ?_
  · -- Index sets agree by `subcube_of_path_cons_idx` and the definition of `extend`.
    simp [subcube_of_path_cons_idx, Subcube.extend]
  · intro j hj
    -- Values align whether or not the queried coordinate is `i`.
    by_cases hji : j = i
    · subst hji; simp [subcube_of_path, Subcube.extend]
    · have hjR : j ∈ (subcube_of_path p).idx := by
        -- Membership in the extended index set reduces to the tail.
        simpa [Subcube.extend, subcube_of_path_cons_idx, hji] using hj
      simp [subcube_of_path, Subcube.extend, hji, hjR]

/-- Inserting the same coordinate twice does not change the recorded index
set.  This `simp` lemma helps eliminate redundant assignments in technical
arguments about decision-tree paths. -/
@[simp] lemma subcube_of_path_cons_cons_idx (i : Fin n) (b₁ b₂ : Bool)
    (p : List (Fin n × Bool)) :
    (subcube_of_path ((i, b₁) :: (i, b₂) :: p)).idx =
      (subcube_of_path ((i, b₁) :: p)).idx := by
  classical
  simp [subcube_of_path_cons_idx, Finset.insert_eq_of_mem]


/-!
Dropping a repeated assignment for the same coordinate does not alter the
resulting subcube.  The lemma `subcube_of_path_cons_cons` upgrades the previous
index-set statement to an equality of the entire subcube.  It allows us to
erase redundant coordinates when manipulating paths.
-/
@[simp] lemma subcube_of_path_cons_cons (i : Fin n) (b₁ b₂ : Bool)
    (p : List (Fin n × Bool)) :
    subcube_of_path ((i, b₁) :: (i, b₂) :: p)
      = subcube_of_path ((i, b₁) :: p) := by
  classical
  -- Two subcubes are equal once their index sets and value functions coincide.
  refine Subcube.ext ?_ ?_
  · -- Index sets are identical by the previous lemma.
    simpa using
      (subcube_of_path_cons_cons_idx (n := n) (i := i)
        (b₁ := b₁) (b₂ := b₂) (p := p))
  · intro j hj
    -- Values agree whether `j` coincides with `i` or not.
    by_cases hji : j = i
    · subst hji; simp [subcube_of_path]
    · -- Membership in the left index set implies membership in the right one,
      -- allowing the values to be compared directly.
      have hjR : j ∈ (subcube_of_path ((i, b₂) :: p)).idx := by
        -- unfold the index set and eliminate the impossible `j = i` case
        simpa [subcube_of_path_cons_idx, hji] using hj
      have hjS : j ∈ (subcube_of_path p).idx := by
        -- removing the head assignment still leaves `j` in the index set
        simpa [subcube_of_path_cons_idx, hji] using hjR
      simp [subcube_of_path, hji, hjR, hjS]

/--
Fixing two distinct coordinates `i` and `j` in either order yields the same
subcube as long as neither index occurs later in the path.  This technical
lemma allows us to swap adjacent coordinate assignments when analysing decision
tree paths.  It will be combined with `subcube_of_path_cons_cons` to remove
duplicate assignments in subsequent proofs.
-/
@[simp] lemma subcube_of_path_cons_swap (i j : Fin n) (bi bj : Bool)
    (p : List (Fin n × Bool))
    (hi : i ∉ (subcube_of_path (n := n) p).idx)
    (hj : j ∉ (subcube_of_path (n := n) p).idx)
    (hij : i ≠ j) :
    subcube_of_path (n := n) ((i, bi) :: (j, bj) :: p)
      = subcube_of_path (n := n) ((j, bj) :: (i, bi) :: p) := by
  classical
  -- Two subcubes are equal once their index sets and value functions coincide.
  refine Subcube.ext ?_ ?_
  · -- The index sets consist of inserting `i` and `j` into the tail index set;
    -- insertion of distinct elements commutes.
    ext k; simp [subcube_of_path, Finset.insert_comm, hij]
  · intro k hk
    -- Analyse the value assigned to each index.
    by_cases hki : k = i
    · subst hki; simp [subcube_of_path, hij]
    · by_cases hkj : k = j
      · subst hkj; simp [subcube_of_path, hij, Ne.symm hij]
      · -- For indices different from `i` and `j` the value comes from the tail.
        have hkP : k ∈ (subcube_of_path (n := n) p).idx := by
          -- Decode membership in the left index set step by step.
          have hk' : k ∈ insert i (insert j (subcube_of_path (n := n) p).idx) := by
            simpa [subcube_of_path] using hk
          have hk'' : k ∈ insert j (subcube_of_path (n := n) p).idx :=
            (Finset.mem_insert.mp hk').resolve_left hki
          exact (Finset.mem_insert.mp hk'').resolve_left hkj
        have hkR : k ∈ (subcube_of_path (n := n) ((j, bj) :: p)).idx := by
          simpa [subcube_of_path, hkj, hkP]
        have hkS : k ∈ (subcube_of_path (n := n) ((i, bi) :: p)).idx := by
          simpa [subcube_of_path, hki, hkP]
        simp [subcube_of_path, hki, hkj, hkR, hkS, hkP]

/-- Dropping a redundant assignment is stable under arbitrary prefixes.  If a
coordinate `i` is fixed twice consecutively anywhere in the path, the resulting
subcube is unaffected.  This generalises `subcube_of_path_cons_cons` from the
head of the list to an arbitrary position. -/
@[simp] lemma subcube_of_path_append_cons_cons (i : Fin n) (b₁ b₂ : Bool)
    (p q : List (Fin n × Bool)) :
    subcube_of_path (n := n) (p ++ (i, b₁) :: (i, b₂) :: q)
      = subcube_of_path (n := n) (p ++ (i, b₁) :: q) := by
  classical
  induction p with
  | nil =>
      -- The duplicate occurs at the front, where
      -- `subcube_of_path_cons_cons` applies directly.
      simpa [subcube_of_path_cons_cons]
  | cons hd tl ih =>
      -- Peel off the prefix step by step and appeal to the induction
      -- hypothesis on the tail using structural equality of subcubes.
      cases' hd with j b
      refine Subcube.ext ?idx ?val
      · -- index sets coincide after rewriting the tail via `ih`.
        simp [List.cons_append, subcube_of_path, ih]
      · intro k hk
        -- For the value function consider whether `k = j`.
        by_cases hkj : k = j
        · subst hkj; simp [List.cons_append, subcube_of_path]
        · simp [List.cons_append, subcube_of_path, hkj, ih]

/-!  Swapping assignments for two distinct coordinates is also stable under
arbitrary prefixes.  If neither `i` nor `j` appears in the tail `q`, then
the order of the consecutive assignments `(i, bi)` and `(j, bj)` does not
affect the resulting subcube.  This generalises
`subcube_of_path_cons_swap` away from the head of the list. -/
@[simp] lemma subcube_of_path_append_cons_swap (i j : Fin n) (bi bj : Bool)
    (p q : List (Fin n × Bool))
    (hi : i ∉ (subcube_of_path (n := n) q).idx)
    (hj : j ∉ (subcube_of_path (n := n) q).idx)
    (hij : i ≠ j) :
    subcube_of_path (n := n) (p ++ (i, bi) :: (j, bj) :: q)
      = subcube_of_path (n := n) (p ++ (j, bj) :: (i, bi) :: q) := by
  classical
  induction p with
  | nil =>
      -- At the front the statement coincides with `subcube_of_path_cons_swap`.
      simpa using
        (subcube_of_path_cons_swap (n := n) (i := i) (j := j)
          (bi := bi) (bj := bj) (p := q) (hi := hi) (hj := hj) (hij := hij))
  | cons hd tl ih =>
      -- Peel off the prefix and reuse the induction hypothesis on the tail.
      cases' hd with k b
      refine Subcube.ext ?idx ?val
      · simp [List.cons_append, subcube_of_path, ih]
      · intro m hm
        by_cases hmk : m = k
        · subst hmk; simp [List.cons_append, subcube_of_path]
        · simp [List.cons_append, subcube_of_path, hmk, ih]

/-!
`subcube_of_path` collects the indices encountered along a decision-tree path.
Since each step inserts at most one new coordinate, the resulting index set has
cardinality bounded by the length of the path.  This simple bound will be
useful when turning recorded paths into subcubes with dimension estimates.
-/
lemma subcube_of_path_idx_card_le (p : List (Fin n × Bool)) :
    (subcube_of_path (n := n) p).idx.card ≤ p.length := by
  classical
  induction p with
  | nil =>
      simp [subcube_of_path]
  | cons hd tl ih =>
      cases' hd with i b
      have hcard : (insert i (subcube_of_path tl).idx).card ≤
          (subcube_of_path tl).idx.card + 1 := by
        simpa using Finset.card_insert_le (s := (subcube_of_path tl).idx) (a := i)
      have hlen : (subcube_of_path tl).idx.card + 1 ≤ tl.length + 1 :=
        Nat.succ_le_succ ih
      have h := Nat.le_trans hcard hlen
      simpa [subcube_of_path] using h

/-!
Fixing the coordinates along a path reduces the subcube dimension by at
most the length of the path.  Equivalently, the resulting subcube still
has at least `n - p.length` free coordinates.
-/
lemma subcube_of_path_dimension_ge (p : List (Fin n × Bool)) :
    n - p.length ≤ (subcube_of_path (n := n) p).dimension := by
  classical
  -- We know how many coordinates were fixed in `subcube_of_path`.
  have hidx := subcube_of_path_idx_card_le (n := n) (p := p)
  -- `Nat.sub_le_sub_left` converts the bound on fixed coordinates to a
  -- bound on the remaining dimension.
  have h := Nat.sub_le_sub_left hidx n
  simpa [Subcube.dimension] using h

/-!  
`subcube_of_path` extracts the set of indices touched along a path.  Each
index appearing in the list `p` therefore occurs in `(subcube_of_path p).idx`.
Conversely, no other indices are inserted, so the index set is always a
subset of the coordinates listed in `p`.  This observation helps to
translate assumptions about duplicated indices in paths into constraints on
the resulting subcubes.
-/
lemma subcube_of_path_idx_subset_map_fst_toFinset
    (p : List (Fin n × Bool)) :
    (subcube_of_path (n := n) p).idx ⊆ (p.map Prod.fst).toFinset := by
  classical
  induction p with
  | nil =>
      intro i hi
      simpa using hi
  | cons hd tl ih =>
      rcases hd with ⟨i, b⟩
      intro j hj
      have hj' : j = i ∨ j ∈ (subcube_of_path (n := n) tl).idx :=
        Finset.mem_insert.mp hj
      have : j ∈ insert i ((tl.map Prod.fst).toFinset) := by
        cases hj' with
        | inl hji =>
            subst hji
            exact Finset.mem_insert.mpr (Or.inl rfl)
        | inr hjtl =>
            have : j ∈ (tl.map Prod.fst).toFinset := ih hjtl
            exact Finset.mem_insert.mpr (Or.inr this)
      simpa [List.map_cons] using this

/--
If an index appears in the set extracted by `subcube_of_path`, then the
corresponding coordinate must have occurred somewhere along the original
path.  This is the converse direction to
`mem_subcube_idx_of_mem_path` and is frequently used to translate
membership facts about subcubes back to statements about the underlying
decision-tree paths.
-/
lemma mem_path_of_mem_subcube_idx (i : Fin n) (p : List (Fin n × Bool))
    (hi : i ∈ (subcube_of_path (n := n) p).idx) :
    i ∈ p.map Prod.fst := by
  -- Convert the index-set membership to a membership in the finset of
  -- coordinates appearing along the path, then interpret it back as a
  -- list membership.
  have hi' :=
    subcube_of_path_idx_subset_map_fst_toFinset (n := n) (p := p) hi
  simpa [List.mem_toFinset] using hi'

/-- Split a path at the last occurrence of a coordinate.  The resulting suffix
contains no further assignments for that coordinate.  This lemma is a purely
list-based statement used to manipulate decision-tree paths. -/
lemma path_split_last {p : List (Fin n × Bool)} {j : Fin n}
    (hj : j ∈ p.map Prod.fst) :
    ∃ b p₁ p₂, p = p₁ ++ (j, b) :: p₂ ∧ j ∉ p₂.map Prod.fst := by
  classical
  revert j
  induction p with
  | nil =>
      intro j hj; cases hj
  | cons hd tl ih =>
      intro j hj
      by_cases hjtail : j ∈ tl.map Prod.fst
      ·
        -- The last occurrence lies in the tail: recurse and extend the prefix.
        obtain ⟨b, p₁, p₂, hsplit, hnot⟩ := ih hjtail
        refine ⟨b, hd :: p₁, p₂, ?_, hnot⟩
        simp [hsplit, List.cons_append]
      ·
        -- No further occurrences in the tail: the head must contain `j`.
        have hjhead : j = hd.1 := by
          have : j = hd.1 ∨ j ∈ tl.map Prod.fst := by
            simpa [List.map, List.mem_cons] using hj
          cases this with
          | inl h => exact h
          | inr h => exact (hjtail h).elim
        refine ⟨hd.2, [], tl, ?_, ?_⟩
        · simp [hjhead]
        · simpa [hjtail]

/-- Split a path at the *first* occurrence of a coordinate `j`.  The prefix
`p₁` contains no mention of `j`, while the suffix `p₂` begins with the
corresponding assignment. -/
lemma path_split_first {p : List (Fin n × Bool)} {j : Fin n}
    (hj : j ∈ p.map Prod.fst) :
    ∃ b p₁ p₂, p = p₁ ++ (j, b) :: p₂ ∧ j ∉ p₁.map Prod.fst := by
  classical
  revert j
  induction p with
  | nil =>
      intro j hj; cases hj
  | cons hd tl ih =>
      intro j hj
      by_cases hjhead : j = hd.1
      · subst hjhead
        refine ⟨hd.2, [], tl, ?_, by simp⟩
        simp
      ·
        have hjtail : j ∈ tl.map Prod.fst := by
          simpa [hjhead, List.map, List.mem_cons] using hj
        obtain ⟨b, p₁, p₂, hsplit, hnot⟩ := ih hjtail
        refine ⟨b, hd :: p₁, p₂, ?_, ?_⟩
        · simp [hsplit, List.cons_append]
        · simpa [hjhead] using hnot

/-- A coordinate occurring in the index set of `subcube_of_path p` can be
isolated as the last occurrence in the underlying path.  The tail after this
occurrence is guaranteed to be free of further mentions of the coordinate. -/
lemma subcube_of_path_idx_split_last
    {p : List (Fin n × Bool)} {j : Fin n}
    (hj : j ∈ (subcube_of_path (n := n) p).idx) :
    ∃ b p₁ p₂, p = p₁ ++ (j, b) :: p₂ ∧
      j ∉ (subcube_of_path (n := n) p₂).idx := by
  classical
  -- Translate membership in the index set to a membership in the list of
  -- coordinates along the path.
  have hj_list : j ∈ p.map Prod.fst := by
    have hj_finset :
        j ∈ (p.map Prod.fst).toFinset :=
      subcube_of_path_idx_subset_map_fst_toFinset (n := n) (p := p) hj
    simpa [List.mem_toFinset] using hj_finset
  -- Split the path at the last occurrence of `j`.
  obtain ⟨b, p₁, p₂, hsplit, hnot⟩ := path_split_last (p := p) (j := j) hj_list
  refine ⟨b, p₁, p₂, hsplit, ?_⟩
  -- If `j` were still present in the index set of the suffix, it would also
  -- appear in the list of coordinates, contradicting `hnot`.
  intro hjmem
  have : j ∈ (p₂.map Prod.fst).toFinset :=
    subcube_of_path_idx_subset_map_fst_toFinset (n := n) (p := p₂) hjmem
  have : j ∈ p₂.map Prod.fst := by simpa [List.mem_toFinset] using this
  exact hnot this

/-- A coordinate in the index set of `subcube_of_path p` can be isolated as the
first occurrence in the underlying path.  The prefix before this occurrence is
guaranteed to avoid further mentions of the coordinate. -/
lemma subcube_of_path_idx_split_first
    {p : List (Fin n × Bool)} {j : Fin n}
    (hj : j ∈ (subcube_of_path (n := n) p).idx) :
    ∃ b p₁ p₂, p = p₁ ++ (j, b) :: p₂ ∧
      j ∉ (subcube_of_path (n := n) p₁).idx := by
  classical
  -- Translate membership in the index set to a membership in the list of
  -- coordinates along the path.
  have hj_list : j ∈ p.map Prod.fst := by
    have hj_finset :
        j ∈ (p.map Prod.fst).toFinset :=
      subcube_of_path_idx_subset_map_fst_toFinset (n := n) (p := p) hj
    simpa [List.mem_toFinset] using hj_finset
  -- Split the path at the first occurrence of `j`.
  obtain ⟨b, p₁, p₂, hsplit, hnot⟩ := path_split_first (p := p) (j := j) hj_list
  refine ⟨b, p₁, p₂, hsplit, ?_⟩
  -- If `j` were present in the index set of the prefix, it would also appear in
  -- the list of coordinates, contradicting `hnot`.
  intro hjmem
  have : j ∈ (p₁.map Prod.fst).toFinset :=
    subcube_of_path_idx_subset_map_fst_toFinset (n := n) (p := p₁) hjmem
  have : j ∈ p₁.map Prod.fst := by simpa [List.mem_toFinset] using this
  exact hnot this

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

@[simp] lemma coloredSubcubes_node (i : Fin n) (t₀ t₁ : DecisionTree n) :
  coloredSubcubes (n := n) (node i t₀ t₁) =
    coloredSubcubesAux (n := n) t₀ [(i, false)] ∪
      coloredSubcubesAux (n := n) t₁ [(i, true)] := by
  simp [coloredSubcubes, coloredSubcubesAux]

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

end DecisionTree

/-!
Turning a set of monochromatic subcubes into a concrete decision tree.
The construction proceeds in two steps:

1.  `ofRectCoverList` consumes a list of coloured subcubes.  Each
    element `(b, R)` is turned into a small decision tree testing
    membership in `R` and returning the colour `b` on success while
    falling back to the remainder of the list otherwise.
2.  `ofRectCover` packages a finite set of rectangles together with the
    required monochromaticity witnesses and invokes `ofRectCoverList`.

This section also derives a simple bound on the number of leaves of the
resulting tree, allowing later conversions between covers and decision
trees.
-/

namespace Subcube

variable {n : ℕ}

/--
Convert a subcube into an explicit list of fixed coordinates together
with their Boolean values.  This representation is convenient for
iteratively constructing decision trees.
-/
noncomputable def toList (R : Subcube n) : List (Fin n × Bool) :=
  let l := R.idx.attach.toList
  -- sort coordinates to obtain a canonical order
  let l' := l.mergeSort (fun a b => a.1 < b.1)
  l'.map (fun i => (i.1, R.val i.1 i.2))

@[simp] lemma toList_length (R : Subcube n) :
    (Subcube.toList (n := n) R).length = R.idx.card := by
  classical
  unfold Subcube.toList
  -- `mergeSort` and `map` preserve the length of the list of fixed coordinates.
  simp

lemma toList_length_le (R : Subcube n) :
    (Subcube.toList (n := n) R).length ≤ n := by
  classical
  -- Using the explicit formula from `toList_length`, the bound reduces to the
  -- obvious inequality `R.idx.card ≤ n`.
  simpa [toList_length (n := n) (R := R)] using
    (Finset.card_le_univ (s := R.idx))

/--
The list of fixed coordinates produced by `Subcube.toList` contains no
duplicate indices.  This follows because the indices come from a `Finset`
(`R.idx`), and `mergeSort` preserves the no-duplicate property.
-/
lemma toList_nodup_fst (R : Subcube n) :
    (Subcube.toList (n := n) R).map Prod.fst |>.Nodup := by
  classical
  -- Unfold the definition and introduce names for intermediate lists.
  unfold Subcube.toList
  set l := R.idx.attach.toList
  set l' := l.mergeSort (fun a b => a.1 < b.1)

  -- The list of attached elements from a `Finset` is free of duplicates.
  -- `toList` of a `Finset` is inherently `Nodup`.
  have hl_nodup : l.Nodup := by
    -- unfold the auxiliary definition `l` to apply the lemma.
    simpa [l] using (R.idx.attach.nodup_toList)

  -- `mergeSort` preserves the `Nodup` property.
  have hl'_nodup : l'.Nodup := by
    -- rewrite `l'` in terms of `mergeSort` to apply the lemma.
    simpa [l'] using
      (List.nodup_mergeSort (l := l) (le := fun a b => a.1 < b.1)).mpr hl_nodup

  -- Mapping `Subtype.val` over the sorted list keeps it `Nodup`.
  have hmap_nodup : (l'.map Subtype.val).Nodup :=
    ((List.nodup_map_iff (f := Subtype.val) (l := l') Subtype.val_injective).2
      hl'_nodup)

  -- The first components of the pairs extracted by `toList` are exactly the
  -- values obtained by mapping `Subtype.val` over `l'`.
  have hfst :
      (l'.map (fun i => (i.1, R.val i.1 i.2))).map Prod.fst =
        l'.map Subtype.val := by
    simp [List.map_map]

  -- Substitute and conclude.
  simpa [hfst] using hmap_nodup

/--
Every subcube contains at least one point.  A witness can be constructed by
assigning the prescribed values on the fixed coordinates and an arbitrary
default value elsewhere (we choose `false`).
-/
lemma nonempty (R : Subcube n) : ∃ x : Point n, R.mem x := by
  classical
  -- Define the candidate point.
  let x : Point n := fun i => if h : i ∈ R.idx then R.val i h else false
  refine ⟨x, ?_⟩
  -- On coordinates fixed by `R`, `x` agrees by construction.
  intro i hi
  simp [x, hi]

end Subcube

open Subcube
namespace DecisionTree

variable {n : ℕ}

/--
If a point belongs to a subcube `R`, then it satisfies every assignment encoded
in `R.toList`.
-/
lemma agreesWithAssignments_toList_of_mem {R : Subcube n} {x : Point n}
    (hx : x ∈ₛ R) :
    agreesWithAssignments (n := n) x (Subcube.toList (n := n) R) := by
  classical
  intro q hq
  unfold Subcube.toList at hq
  -- unpack membership in the mapped list
  rcases List.mem_map.mp hq with ⟨i, hi, rfl⟩
  -- the proof component of `i` certifies membership in `R.idx`
  exact hx i.1 i.2

/--
From a successful assignment check against `R.toList` one can reconstruct
membership in the original subcube.  This is the converse of
`agreesWithAssignments_toList_of_mem` and will be useful when reasoning about
failures of `matchSubcube`.
-/
lemma mem_of_agreesWithAssignments_toList {R : Subcube n} {x : Point n}
    (h : agreesWithAssignments (n := n) x (Subcube.toList (n := n) R)) :
    x ∈ₛ R := by
  classical
  intro i hi
  have hi_set : ((⟨i, hi⟩) : {j : Fin n // j ∈ R.idx}) ∈ R.idx.attach := by
    simpa [Finset.mem_attach]
  have hi_list : ((⟨i, hi⟩) : {j : Fin n // j ∈ R.idx}) ∈ R.idx.attach.toList := by
    simpa using (List.mem_toList).2 hi_set
  have hi_merge : ((⟨i, hi⟩) : {j : Fin n // j ∈ R.idx}) ∈
      R.idx.attach.toList.mergeSort (fun a b => a.1 < b.1) :=
    (List.mem_mergeSort (le := fun a b : {j : Fin n // j ∈ R.idx} => a.1 < b.1)
      (a := ⟨i, hi⟩) (l := R.idx.attach.toList)).2 hi_list
  have hmem : (i, R.val i hi) ∈
      (R.idx.attach.toList.mergeSort (fun a b => a.1 < b.1)).map
        (fun j => (j.1, R.val j.1 j.2)) :=
    List.mem_map.2 ⟨⟨i, hi⟩, hi_merge, rfl⟩
  simpa using h _ hmem

/-- Convert a subcube with a prescribed colour into a linear decision-tree
branch.  The tree checks every fixed coordinate of `R` in turn and returns `b`
if all assignments match. -/
noncomputable def ofSubcube (R : Subcube n) (b : Bool) : DecisionTree n :=
  ofAssignments (Subcube.toList (n := n) R) b

/-- Membership in `R` forces evaluation of `ofSubcube R b` to yield `b`. -/
lemma eval_ofSubcube_of_mem {R : Subcube n} {x : Point n} {b : Bool}
    (hx : x ∈ₛ R) :
    eval_tree (ofSubcube (n := n) R b) x = b := by
  classical
  have hagrees :=
    agreesWithAssignments_toList_of_mem (n := n) (R := R) (x := x) hx
  simpa [ofSubcube] using
    (eval_ofAssignments_of_agrees (n := n)
      (p := Subcube.toList (n := n) R) (x := x) (b := b) hagrees)

/-- The depth of `ofSubcube R b` is bounded by the number of fixed coordinates. -/
lemma depth_ofSubcube_le (R : Subcube n) {b : Bool} :
    depth (ofSubcube (n := n) R b) ≤ R.idx.card := by
  simpa [ofSubcube, Subcube.toList_length (n := n) (R := R)] using
    (depth_ofAssignments_le (n := n) (p := Subcube.toList (n := n) R)
      (b := b))

/--
The codimension of a subcube bounds the depth of the decision tree
`ofSubcube`.  This reformulation is often convenient when a lower
estimate on the dimension is available.
-/
lemma depth_ofSubcube_le_codim (R : Subcube n) {b : Bool} :
    depth (ofSubcube (n := n) R b) ≤ n - R.dimension := by
  classical
  -- We rewrite the codimension `n - dimension` as the number of fixed
  -- coordinates `idx.card`.
  have hle : R.idx.card ≤ n := by
    simpa using (Finset.card_le_univ (s := R.idx))
  have hcodim : n - R.dimension = R.idx.card := by
    -- `dimension` is defined as `n - idx.card`.
    have := Nat.sub_sub_self hle
    simpa [Subcube.dimension] using this
  -- Now apply the previous bound in terms of `idx.card`.
  simpa [hcodim] using (depth_ofSubcube_le (n := n) (R := R) (b := b))

/-
`matchSubcube p b t` builds a decision tree which checks the coordinate
assignments recorded in the list `p`.  If the input satisfies all
constraints, the tree returns the constant Boolean `b`.  Any mismatch
causes evaluation of the fallback tree `t`.
-/
noncomputable def matchSubcube : List (Fin n × Bool) → Bool → DecisionTree n → DecisionTree n
  | [], b, _ => leaf b
  | (i, true) :: p, b, t =>
      node i t (matchSubcube p b t)
  | (i, false) :: p, b, t =>
      node i (matchSubcube p b t) t

/-- If `x` agrees with every assignment in `p`, `matchSubcube p b t`
returns the constant colour `b` regardless of the fallback tree `t`. -/
lemma eval_matchSubcube_agrees {p : List (Fin n × Bool)} {b : Bool}
    {t : DecisionTree n} {x : Point n}
    (h : agreesWithAssignments (n := n) x p) :
    eval_tree (matchSubcube (n := n) p b t) x = b := by
  classical
  induction p with
  | nil => simpa [matchSubcube] using h
  | cons hd tl ih =>
      rcases hd with ⟨i, b'⟩
      have hcons :=
        (agreesWithAssignments_cons (x:=x) (i:=i) (b:=b') (p:=tl)) |>.mp h
      cases b' with
      | false =>
          have hx : x i = false := hcons.1
          have ih' := ih hcons.2
          simpa [matchSubcube, hx] using ih'
      | true =>
          have hx : x i = true := hcons.1
          have ih' := ih hcons.2
          simpa [matchSubcube, hx] using ih'

/--
When the point `x` satisfies every assignment in `p`, the execution of
`matchSubcube p b t` visits nodes in exactly the same order as the list
`p` records.  Consequently `path_to_leaf` reproduces `p` verbatim.-/
lemma path_to_leaf_matchSubcube_agrees {p : List (Fin n × Bool)} {b : Bool}
    {t : DecisionTree n} {x : Point n}
    (h : agreesWithAssignments (n := n) x p) :
    path_to_leaf (matchSubcube (n := n) p b t) x = p := by
  classical
  induction p with
  | nil =>
      -- With no assignments the tree collapses to a leaf, producing an empty path.
      simp [matchSubcube, path_to_leaf]
  | cons hd tl ih =>
      rcases hd with ⟨i, v⟩
      -- Split the agreement condition into the head assignment and the tail.
      have hcons :
          x i = v ∧ agreesWithAssignments (n := n) x tl :=
        (agreesWithAssignments_cons (x := x) (i := i) (b := v) (p := tl)).1 h
      -- Recurse on the tail after following the corresponding branch.
      cases v
      · have := ih hcons.2
        simp [matchSubcube, path_to_leaf, hcons.1, this]
      · have := ih hcons.2
        simp [matchSubcube, path_to_leaf, hcons.1, this]

/--
If the input `x` violates at least one assignment in `p`, evaluating
`matchSubcube p b t` is the same as evaluating the fallback tree `t`.
-/
lemma eval_matchSubcube_not_agrees {p : List (Fin n × Bool)} {b : Bool}
    {t : DecisionTree n} {x : Point n}
    (h : ¬ agreesWithAssignments (n := n) x p) :
    eval_tree (matchSubcube (n := n) p b t) x = eval_tree t x := by
  classical
  induction p with
  | nil =>
      have : False := by simpa using h
      exact this.elim
  | cons hd tl ih =>
      rcases hd with ⟨i, b'⟩
      have hcons : ¬ (x i = b' ∧ agreesWithAssignments (n := n) x tl) := by
        simpa [agreesWithAssignments_cons] using h
      have hx_or := not_and_or.mp hcons
      cases b' with
      | false =>
          cases hx_or with
          | inl hxne =>
              have hxi : x i = true := by
                cases h' : x i <;> simpa [h'] using hxne
              simp [matchSubcube, hxi]
          | inr htl =>
              by_cases hxi : x i = false
              · have := ih htl
                simp [matchSubcube, hxi, this]
              ·
                have hxi' : x i = true := by
                  cases h' : x i <;> simpa [h'] using hxi
                simp [matchSubcube, hxi']
      | true =>
          cases hx_or with
          | inl hxne =>
              have hxi : x i = false := by
                cases h' : x i <;> simpa [h'] using hxne
              simp [matchSubcube, hxi]
          | inr htl =>
              by_cases hxi : x i = true
              · have := ih htl
                simp [matchSubcube, hxi, this]
              ·
                have hxi' : x i = false := by
                  cases h' : x i <;> simpa [h'] using hxi
                simp [matchSubcube, hxi']

/--
Convert a list of coloured subcubes into a decision tree.  Earlier
rectangles in the list take precedence over later ones.
-/
noncomputable def ofRectCoverList (default : Bool) : List (Bool × Subcube n) → DecisionTree n
  | [] => leaf default
  | (b, R) :: rs =>
      matchSubcube (Subcube.toList (n := n) R) b (ofRectCoverList default rs)

/--
`ofRectCover` turns a finite set of rectangles into a decision tree.
Each rectangle is assigned a colour using the accompanying proof of
monochromaticity.  The resulting decision tree computes a Boolean family
which agrees with all rectangles in the cover.
-/
noncomputable def ofRectCover (default : Bool) (F : Family n)
    (Rset : Finset (Subcube n))
    (hmono : ∀ R ∈ Rset, Subcube.monochromaticForFamily R F) :
    DecisionTree n :=
  let colored : List (Bool × Subcube n) :=
    Rset.attach.toList.map (fun R =>
      (Classical.choose (hmono R.1 R.2), R.1))
  ofRectCoverList (n := n) default colored

/-!
At present we do not develop detailed bounds relating the size of the
input rectangle set to the leaf count or depth of `ofRectCover`.  The
primary goal of this section is to provide a concrete tree structure; a
more refined analysis can be added once needed.
-/
@[simp] lemma eval_ofRectCoverList_nil (default : Bool) (x : Point n) :
    eval_tree (ofRectCoverList (n := n) default []) x = default := rfl

lemma eval_ofRectCoverList_cons_mem {default : Bool} {b : Bool}
    {R : Subcube n} {rs : List (Bool × Subcube n)} {x : Point n}
    (hx : x ∈ₛ R) :
    eval_tree (ofRectCoverList (n := n) default ((b, R) :: rs)) x = b := by
  have hmatch :=
    agreesWithAssignments_toList_of_mem (n := n) (R := R) (x := x) hx
  simpa using
    (eval_matchSubcube_agrees (n := n)
      (p := Subcube.toList (n := n) R)
      (b := b) (t := ofRectCoverList (n := n) default rs)
      (x := x) hmatch)

/--
If every rectangle of the list `colored` that contains a point `x` is labelled
`true` and at least one such rectangle exists, then evaluating
`ofRectCoverList colored` on `x` yields `true`.  This lemma is the engine behind
the correctness proof for `CoverRes.eval_true`.
-/
lemma eval_ofRectCoverList_true_of_mem
    {default : Bool} {colored : List (Bool × Subcube n)} {x : Point n}
    (hex : ∃ p ∈ colored, Subcube.mem p.snd x)
    (hall : ∀ (p : Bool × Subcube n), p ∈ colored → Subcube.mem p.snd x → p.fst = true) :
    eval_tree (ofRectCoverList (n := n) default colored) x = true := by
  classical
  induction colored with
  | nil =>
      rcases hex with ⟨p, hp, _⟩
      cases hp
  | cons hd tl ih =>
      rcases hd with ⟨b, R⟩
      by_cases hxR : x ∈ₛ R
      ·
        -- The head rectangle contains `x`; the evaluation equals its colour.
        have hb : b = true := by
          have := hall (p := (b, R)) (by simp) (by simpa using hxR)
          simpa using this
        have := eval_ofRectCoverList_cons_mem
          (n := n) (default := default) (b := b) (R := R) (rs := tl)
          (x := x) hxR
        simpa [ofRectCoverList, hb] using this
      ·
        -- Otherwise reduce to the tail of the list.
        have hnot : ¬ agreesWithAssignments (n := n) x
            (Subcube.toList (n := n) R) := by
          intro hagrees
          have hxmem : x ∈ₛ R :=
            mem_of_agreesWithAssignments_toList (n := n) (x := x) (R := R) hagrees
          exact hxR hxmem
        have hall_tl : ∀ p ∈ tl, Subcube.mem p.snd x → p.fst = true := by
          intro p hp hxP
          have hp' : p ∈ (b, R) :: tl := List.mem_cons_of_mem _ hp
          exact hall p hp' hxP
        have hex_tl : ∃ p ∈ tl, Subcube.mem p.snd x := by
          rcases hex with ⟨p, hp, hxP⟩
          have hp' : p = (b, R) ∨ p ∈ tl := List.mem_cons.mp hp
          cases hp' with
          | inl hpr =>
              cases hpr
              exact (hxR hxP).elim
          | inr htl =>
              exact ⟨p, htl, hxP⟩
        have htail := ih hex_tl hall_tl
        have := eval_matchSubcube_not_agrees (n := n)
            (p := Subcube.toList (n := n) R) (b := b)
            (t := ofRectCoverList (n := n) default tl) (x := x) hnot
        simpa [ofRectCoverList, this, htail]

/--
If every rectangle in the list `colored` that contains a point `x` is labelled
`false` (or there is no such rectangle), then evaluating
`ofRectCoverList colored` on `x` yields `false`.  The default value of the tree
is also `false`, so the lemma does not require an existence hypothesis.
-/
lemma eval_ofRectCoverList_false_of_forall
    {colored : List (Bool × Subcube n)} {x : Point n}
    (hall : ∀ p ∈ colored, Subcube.mem p.snd x → p.fst = false) :
    eval_tree (ofRectCoverList (n := n) false colored) x = false := by
  classical
  induction colored with
  | nil =>
      -- No rectangles: evaluation falls back to the default value.
      simp [ofRectCoverList]
  | cons hd tl ih =>
      rcases hd with ⟨b, R⟩
      -- Check whether the head rectangle contains `x`.
      by_cases hxR : x ∈ₛ R
      ·
        -- The head colour matches the evaluation.
        have hb : b = false :=
          hall (p := (b, R)) (by simp) (by simpa using hxR)
        have := eval_ofRectCoverList_cons_mem
          (n := n) (default := false) (b := b) (R := R)
          (rs := tl) (x := x) hxR
        simpa [ofRectCoverList, hb] using this
      ·
        -- Otherwise reduce to the tail.
        have hnot : ¬ agreesWithAssignments (n := n) x
            (Subcube.toList (n := n) R) := by
          intro hagrees
          have hxmem : x ∈ₛ R :=
            mem_of_agreesWithAssignments_toList (n := n) (x := x)
              (R := R) hagrees
          exact hxR hxmem
        have hall_tl : ∀ p ∈ tl, Subcube.mem p.snd x → p.fst = false := by
          intro p hp hxP
          have hp' : p ∈ (b, R) :: tl := List.mem_cons_of_mem _ hp
          exact hall p hp' hxP
        have htail := ih hall_tl
        have := eval_matchSubcube_not_agrees (n := n)
            (p := Subcube.toList (n := n) R) (b := b)
            (t := ofRectCoverList (n := n) false tl) (x := x) hnot
        simpa [ofRectCoverList, this, htail]
/--
The `matchSubcube` construction adds a chain of decision nodes checking each
assignment in `p` before consulting the fallback tree `t`.  Consequently the
number of leaves grows linearly with the length of `p`.
The exact count is `leaf_count t * p.length + 1`.
-/
lemma leaf_count_matchSubcube (p : List (Fin n × Bool)) (b : Bool)
    (t : DecisionTree n) :
    leaf_count (matchSubcube (n := n) p b t)
      = leaf_count t * p.length + 1 := by
  induction p with
  | nil =>
      simp [matchSubcube, leaf_count]
    | cons hd tl ih =>
      rcases hd with ⟨i, bi⟩
      cases bi
      case false =>
        simp [matchSubcube, leaf_count, ih, Nat.mul_succ, Nat.add_comm,
          Nat.add_left_comm]
      case true =>
        simp [matchSubcube, leaf_count, ih, Nat.mul_succ, Nat.add_comm,
          Nat.add_left_comm]

/--
The depth of `matchSubcube p b t` is at most the depth of the fallback tree
`t` plus the length of the assignment list `p`.  Each entry of `p` introduces
one additional decision node, yielding a linear overhead.
-/
lemma depth_matchSubcube_le (p : List (Fin n × Bool)) (b : Bool)
    (t : DecisionTree n) :
    depth (matchSubcube (n := n) p b t) ≤ depth t + p.length := by
  induction p with
  | nil =>
      -- No assignments: the construction collapses to a leaf.
      simp [matchSubcube, depth]
    | cons hd tl ih =>
        rcases hd with ⟨i, bi⟩
        cases bi
        case false =>
            -- Branching on `(i, false)` places the recursive call on the left.
            -- Bound both children of the node by `depth t + tl.length` and apply
            -- `max` monotonicity.
            have h0 : depth t ≤ depth t + tl.length := Nat.le_add_right _ _
            have h1 : depth (matchSubcube (n := n) tl b t) ≤ depth t + tl.length := ih
            have hmax :
                max (depth (matchSubcube (n := n) tl b t)) (depth t)
                    ≤ depth t + tl.length :=
              max_le_iff.mpr ⟨h1, h0⟩
            have := Nat.succ_le_succ hmax
            -- The resulting bound matches `depth t + (tl.length + 1)` after
            -- rewriting.
            simpa [matchSubcube, depth, Nat.add_comm, Nat.add_left_comm,
                  Nat.add_assoc] using this
        case true =>
            -- Symmetric case: the recursive call sits on the right branch.
            have h0 : depth t ≤ depth t + tl.length := Nat.le_add_right _ _
            have h1 : depth (matchSubcube (n := n) tl b t) ≤ depth t + tl.length := ih
            have hmax :
                max (depth t) (depth (matchSubcube (n := n) tl b t))
                    ≤ depth t + tl.length :=
              max_le_iff.mpr ⟨h0, h1⟩
            have := Nat.succ_le_succ hmax
            simpa [matchSubcube, depth, Nat.add_comm, Nat.add_left_comm,
                  Nat.add_assoc] using this

/--
Specialised branching on a given `Subcube`.  The resulting decision tree
checks all fixed coordinates of `R`; if the input lies inside `R`, it returns
the constant colour `b`.  Otherwise evaluation falls back to the tree `t`.
-/
noncomputable def branchOnSubcube (R : Subcube n) (b : Bool)
    (t : DecisionTree n) : DecisionTree n :=
  matchSubcube (Subcube.toList (n := n) R) b t

/-- Evaluating `branchOnSubcube R b t` on a point of `R` yields `b`. -/
lemma eval_branchOnSubcube_mem {R : Subcube n} {x : Point n} {b : Bool}
    {t : DecisionTree n} (hx : x ∈ₛ R) :
    eval_tree (branchOnSubcube (n := n) R b t) x = b := by
  classical
  unfold branchOnSubcube
  have hagrees :=
    agreesWithAssignments_toList_of_mem (n := n) (R := R) (x := x) hx
  simpa using
    eval_matchSubcube_agrees (n := n)
      (p := Subcube.toList (n := n) R) (b := b) (t := t) (x := x) hagrees

/--
If the point `x` lies outside `R`, `branchOnSubcube` delegates evaluation to
the fallback tree `t`.
-/
lemma eval_branchOnSubcube_not_mem {R : Subcube n} {x : Point n} {b : Bool}
    {t : DecisionTree n} (hx : Subcube.mem R x → False) :
    eval_tree (branchOnSubcube (n := n) R b t) x = eval_tree t x := by
  classical
  unfold branchOnSubcube
  have hagrees :
      ¬ agreesWithAssignments (n := n) x (Subcube.toList (n := n) R) := by
    intro h
    have hxmem : Subcube.mem R x :=
      mem_of_agreesWithAssignments_toList (n := n) (x := x) (R := R) h
    exact hx hxmem
  simpa using
    eval_matchSubcube_not_agrees (n := n)
      (p := Subcube.toList (n := n) R) (b := b) (t := t) (x := x) hagrees

/--
Evaluating `branchOnSubcube R b t` can be described by an `if` expression: the
tree returns `b` on points inside `R` and otherwise falls back to the tree `t`.
This consolidated statement is often convenient when reasoning about coverings
that branch on a known subcube.
-/
lemma eval_branchOnSubcube (R : Subcube n) (b : Bool)
    (t : DecisionTree n) (x : Point n) [Decidable (x ∈ₛ R)] :
    eval_tree (branchOnSubcube (n := n) R b t) x =
      if x ∈ₛ R then b else eval_tree t x := by
  classical
  by_cases hx : x ∈ₛ R
  · -- Inside the subcube the tree returns the fixed colour `b`.
    simpa [hx] using
      (eval_branchOnSubcube_mem (n := n) (R := R) (x := x) (b := b)
        (t := t) hx)
  · -- Outside `R` evaluation delegates to the fallback tree `t`.
    have hx' : Subcube.mem R x → False := by
      intro hmem; exact hx hmem
    simpa [hx] using
      (eval_branchOnSubcube_not_mem (n := n) (R := R) (x := x) (b := b)
        (t := t) hx')

/--
The depth of `branchOnSubcube R b t` increases by at most the number of fixed
coordinates of `R` compared to the fallback tree `t`.
-/
lemma depth_branchOnSubcube_le (R : Subcube n) (b : Bool)
    (t : DecisionTree n) :
    depth (branchOnSubcube (n := n) R b t) ≤
        depth t + R.idx.card := by
  unfold branchOnSubcube
  simpa [Subcube.toList_length (n := n) (R := R)] using
    depth_matchSubcube_le (n := n)
      (p := Subcube.toList (n := n) R) (b := b) (t := t)

/-
The following helper lemma will be useful when analysing coloured subcubes
after pre‑pending an assignment to the path.  Intuitively, removing the
leading assignment can only enlarge the described subcube.
-/
/--
Bounding the number of leaves produced by `ofRectCoverList`.
Each rectangle contributes at most a multiplicative factor of
`(length (Subcube.toList R) + 1)` to the total leaf count.
-/
lemma leaf_count_ofRectCoverList_le (default : Bool) :
    ∀ rs : List (Bool × Subcube n),
      leaf_count (ofRectCoverList (n := n) default rs) ≤
        List.foldr (fun r acc =>
          ((Subcube.toList (n := n) r.2).length.succ) * acc) 1 rs := by
  intro rs; induction rs with
  | nil =>
      have h : leaf_count (ofRectCoverList (n := n) default []) = 1 := by
        simp [ofRectCoverList, leaf_count]
      simpa [h, List.foldr] using (Nat.le_refl 1)
  | cons hd tl ih =>
      rcases hd with ⟨b, R⟩
      -- Let `t` denote the tree built from the tail.
      set t := ofRectCoverList (n := n) default tl
      -- Length of the assignment list describing `R`.
      set len := (Subcube.toList (n := n) R).length
      -- Exact leaf count for the head rectangle.
      have hmatch := leaf_count_matchSubcube
        (n := n) (p := Subcube.toList (n := n) R) (b := b) (t := t)
      -- The tree `t` has at least one leaf.
      have hpos : 1 ≤ t.leaf_count := Nat.succ_le_of_lt (leaf_count_pos _)
      -- Bound the new leaves created by matching `R`.
      have hstep :
          leaf_count (matchSubcube (n := n) (Subcube.toList (n := n) R) b t)
              ≤ t.leaf_count * (len.succ) := by
        -- Start from the exact formula and replace the trailing `+ 1` by `+ t.leaf_count`.
        have hle : t.leaf_count * len + 1 ≤ t.leaf_count * len + t.leaf_count :=
          Nat.add_le_add_left hpos (t.leaf_count * len)
        have hmul : t.leaf_count * len + t.leaf_count = t.leaf_count * (len.succ) := by
          have := Nat.mul_succ t.leaf_count len
          -- `mul_succ` yields `a * (b + 1) = a * b + a`.
          simpa [len, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this.symm
        have : leaf_count (matchSubcube (n := n) (Subcube.toList (n := n) R) b t)
            ≤ t.leaf_count * len + t.leaf_count := by
          simpa [hmatch, len] using hle
        simpa [hmul] using this
      -- Apply the inductive hypothesis for the tail and multiply the bound.
      have hrec := ih
      have hmul := Nat.mul_le_mul_left (len.succ) hrec
      have hmul' : t.leaf_count * (len.succ) ≤
          (len.succ) * List.foldr (fun r acc => ((Subcube.toList (n := n) r.2).length.succ) * acc) 1 tl := by
        simpa [t, len, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
          using hmul
      -- Combine the bounds.
      have : leaf_count (ofRectCoverList (n := n) default ((b, R) :: tl)) ≤
          (len.succ) * List.foldr (fun r acc => ((Subcube.toList (n := n) r.2).length.succ) * acc) 1 tl := by
        calc
          leaf_count (ofRectCoverList (n := n) default ((b, R) :: tl))
              = leaf_count (matchSubcube (n := n) (Subcube.toList (n := n) R) b t) := by rfl
          _ ≤ t.leaf_count * (len.succ) := hstep
          _ ≤ (len.succ) *
              List.foldr (fun r acc => ((Subcube.toList (n := n) r.2).length.succ) * acc) 1 tl := hmul'
      -- Rewrite in terms of `R` and `tl`.
      simpa [List.foldr, len, t, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
        using this

/--
Bounding the depth of `ofRectCoverList`.  The construction consumes the list
from head to tail, matching each rectangle before consulting the remainder of
the tree.  Consequently every rectangle contributes at most the length of its
assignment list to the final depth.
-/
lemma depth_ofRectCoverList_le (default : Bool) :
    ∀ rs : List (Bool × Subcube n),
      depth (ofRectCoverList (n := n) default rs) ≤
        List.foldr (fun r acc =>
          (Subcube.toList (n := n) r.2).length + acc) 0 rs := by
  intro rs; induction rs with
  | nil =>
      -- The empty list produces a single leaf with zero depth.
      simp [ofRectCoverList, depth]
  | cons hd tl ih =>
      rcases hd with ⟨b, R⟩
      -- Recursive tree built from the tail of the list.
      set t := ofRectCoverList (n := n) default tl
      -- Length of the path describing the current rectangle.
      set len := (Subcube.toList (n := n) R).length
      -- Bound the depth added by matching the rectangle in front of `t`.
      have hmatch := depth_matchSubcube_le
        (n := n) (p := Subcube.toList (n := n) R) (b := b) (t := t)
      -- Combine with the inductive hypothesis for the tail.
      have hbound :
          depth (ofRectCoverList (n := n) default ((b, R) :: tl)) ≤
            depth t + len := by
        simpa [t, len] using hmatch
      have htail : depth t + len ≤
          List.foldr
              (fun r acc => (Subcube.toList (n := n) r.2).length + acc) 0 tl + len :=
        Nat.add_le_add_right ih len
      have := le_trans hbound htail
      -- Reorder the sums to match the desired fold on the entire list.
      simpa [List.foldr, t, len, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using this

/--
Bound the number of leaves produced by `ofRectCover`.  The statement
specialises `leaf_count_ofRectCoverList_le` to the list extracted from a
finite set of rectangles.  Each rectangle contributes at most a factor of
`(length (Subcube.toList R) + 1)` to the final leaf count.
-/
lemma leaf_count_ofRectCover_le (default : Bool) (F : Family n)
    (Rset : Finset (Subcube n))
    (hmono : ∀ R ∈ Rset, Subcube.monochromaticForFamily R F) :
    leaf_count (ofRectCover (n := n) default F Rset hmono) ≤
      List.foldr
        (fun R acc => ((Subcube.toList (n := n) R.1).length.succ) * acc)
        1 Rset.attach.toList := by
  classical
  -- Expand the definition of `ofRectCover` and apply the list-based bound.
  set colored :=
    Rset.attach.toList.map (fun R =>
      (Classical.choose (hmono R.1 R.2), R.1)) with hcolored
  have h := leaf_count_ofRectCoverList_le
      (n := n) (default := default) (rs := colored)
  -- The map in `colored` only affects the Boolean colour; remove it.
  simpa [ofRectCover, hcolored, List.foldr_map] using h

/--
Bounding the depth of the decision tree constructed by `ofRectCover`.
Each rectangle contributes at most the length of its assignment list to
the overall depth.
-/
lemma depth_ofRectCover_le (default : Bool) (F : Family n)
    (Rset : Finset (Subcube n))
    (hmono : ∀ R ∈ Rset, Subcube.monochromaticForFamily R F) :
    depth (ofRectCover (n := n) default F Rset hmono) ≤
      List.foldr
        (fun R acc => (Subcube.toList (n := n) R.1).length + acc)
        0 Rset.attach.toList := by
  classical
  set colored :=
    Rset.attach.toList.map (fun R =>
      (Classical.choose (hmono R.1 R.2), R.1)) with hcolored
  have h := depth_ofRectCoverList_le
      (n := n) (default := default) (rs := colored)
  simpa [ofRectCover, hcolored, List.foldr_map] using h

/--
The number of coloured subcubes produced by `ofRectCover` is bounded by the
same product that controls the leaf count.  Each rectangle contributes a factor
of the length of its assignment list plus one, mirroring the construction of
the underlying decision tree.
-/
lemma coloredSubcubes_ofRectCover_card_le (default : Bool) (F : Family n)
    (Rset : Finset (Subcube n))
    (hmono : ∀ R ∈ Rset, Subcube.monochromaticForFamily R F) :
    (coloredSubcubes
        (ofRectCover (n := n) default F Rset hmono)).card ≤
      List.foldr
        (fun R acc => ((Subcube.toList (n := n) R.1).length.succ) * acc)
        1 Rset.attach.toList := by
  -- First bound the number of coloured subcubes by the number of leaves.
  have h₁ :=
    coloredSubcubes_card_le_leaf_count
      (t := ofRectCover (n := n) default F Rset hmono)
  -- Then apply the leaf-count bound specialised to `ofRectCover`.
  have h₂ :=
    leaf_count_ofRectCover_le
      (n := n) (default := default)
      (F := F) (Rset := Rset) (hmono := hmono)
  -- Combine the two inequalities to obtain the final estimate.
  exact le_trans h₁ h₂

lemma mem_subcube_of_path_cons_of_mem (x : Point n) (p : List (Fin n × Bool))
    (i : Fin n) (b : Bool)
    (hx : (subcube_of_path p).mem x) (hxi : x i = b) :
    (subcube_of_path ((i, b) :: p)).mem x := by
  intro j hj
  rcases Finset.mem_insert.mp hj with hj | hj
  · subst hj; simp [subcube_of_path, hxi]
  · have hxj := hx j hj
    by_cases hji : j = i
    · subst hji; simp [subcube_of_path, hxi]
    · simp [subcube_of_path, hji, hxj]

/-!
If `x` lies in the subcube obtained by extending `p` with the decision
`(i, b)`, then `x` also lies in the original subcube for `p` and its
`i`-th coordinate agrees with the chosen bit `b`.  This is the converse
direction of `mem_subcube_of_path_cons_of_mem` and is convenient when
reasoning about recorded paths.
-/
/-!
Membership in an extended path subcube in particular enforces the
value chosen at the new coordinate.  This helper lemma extracts that
fact without making any claims about the remaining path.
-/
lemma mem_subcube_of_path_cons_fixed (x : Point n) (p : List (Fin n × Bool))
    (i : Fin n) (b : Bool)
    (hx : (subcube_of_path ((i, b) :: p)).mem x) :
    x i = b := by
  -- Evaluate the membership condition at the newly inserted index.
  have := hx i (by simp)
  simpa [subcube_of_path] using this

/--
Если точка удовлетворяет расширенному списку присваиваний `p ++ q`,
то она также удовлетворяет хвостовой части `q`.
-/
lemma agreesWithAssignments_tail_of_append (x : Point n)
    (p q : List (Fin n × Bool))
    (h : agreesWithAssignments (n := n) x (p ++ q)) :
    agreesWithAssignments (n := n) x q := by
  induction p with
  | nil =>
      simpa using h
  | cons hd tl ih =>
      rcases hd with ⟨i, b⟩
      -- Раскрываем условие для головы и рекурсивно обрабатываем хвост.
      have h' :=
        (agreesWithAssignments_cons (x := x) (i := i) (b := b)
          (p := tl ++ q)).1 h
      exact ih h'.2

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
            (i := i) (b := true) h' (by simp [h])
      · have h' := ih0 x
        simpa [path_to_leaf, h] using
          mem_subcube_of_path_cons_of_mem (x := x) (p := path_to_leaf t0 x)
            (i := i) (b := false) h' (by simp [h])

/-!  The index set of the subcube obtained from the path to a leaf has
cardinality bounded by the depth of the tree.  This follows from
`path_to_leaf_length_le_depth` combined with `subcube_of_path_idx_card_le`.
-/
lemma path_to_leaf_idx_card_le_depth (t : DecisionTree n) (x : Point n) :
    (subcube_of_path (path_to_leaf t x)).idx.card ≤ depth t := by
  have hlen := path_to_leaf_length_le_depth (t := t) (x := x)
  have := subcube_of_path_idx_card_le (n := n) (p := path_to_leaf t x)
  exact le_trans this hlen

/-!
The subcube obtained from following `x` down the tree retains at least
`n - depth t` free coordinates.  This follows from the bound on the
index set above.
-/
lemma path_to_leaf_dimension_ge_n_minus_depth (t : DecisionTree n) (x : Point n) :
    n - depth t ≤ (subcube_of_path (path_to_leaf t x)).dimension := by
  classical
  have hidx := path_to_leaf_idx_card_le_depth (t := t) (x := x)
  have h := Nat.sub_le_sub_left hidx n
  simpa [Subcube.dimension] using h

/--
Every evaluation/path pair produced by a decision tree appears in the set of
coloured subcubes.  The path accumulated by `coloredSubcubesAux` is reversed
relative to `path_to_leaf`, hence the `List.reverse` operation below. -/
lemma eval_pair_mem_coloredSubcubesAux (t : DecisionTree n) (x : Point n)
    (p : List (Fin n × Bool)) :
    ⟨eval_tree t x, subcube_of_path ((path_to_leaf t x).reverse ++ p)⟩ ∈
      coloredSubcubesAux (n := n) t p := by
  classical
  induction t generalizing x p with
  | leaf b =>
      simp [path_to_leaf, eval_tree, coloredSubcubesAux]
  | node i t0 t1 ih0 ih1 =>
      by_cases hxi : x i
      · have hmem := ih1 x ((i, true) :: p)
        have : (path_to_leaf (node i t0 t1) x).reverse ++ p =
            (path_to_leaf t1 x).reverse ++ (i, true) :: p := by
          simp [path_to_leaf, hxi, List.reverse_cons, List.append_assoc]
        simpa [coloredSubcubesAux, eval_tree, path_to_leaf, hxi, this]
          using Finset.mem_union.mpr (Or.inr hmem)
      · have hmem := ih0 x ((i, false) :: p)
        have : (path_to_leaf (node i t0 t1) x).reverse ++ p =
            (path_to_leaf t0 x).reverse ++ (i, false) :: p := by
          simp [path_to_leaf, hxi, List.reverse_cons, List.append_assoc]
        simpa [coloredSubcubesAux, eval_tree, path_to_leaf, hxi, this]
          using Finset.mem_union.mpr (Or.inl hmem)

lemma eval_pair_mem_coloredSubcubes (t : DecisionTree n) (x : Point n) :
    ⟨eval_tree t x, subcube_of_path ((path_to_leaf t x).reverse)⟩ ∈
      coloredSubcubes (n := n) t := by
  simpa [coloredSubcubes] using
    eval_pair_mem_coloredSubcubesAux (t := t) (x := x) (p := [])

/-!  The list of coordinates along a path records the bit seen at each
input position.  Every entry therefore agrees with the corresponding
coordinate of the input that generated the path. -/
lemma path_to_leaf_agrees (t : DecisionTree n) (x : Point n) :
    ∀ q ∈ path_to_leaf t x, x q.1 = q.2 := by
  induction t generalizing x with
  | leaf b =>
      intro q hq
      simp [path_to_leaf] at hq
  | node i t0 t1 ih0 ih1 =>
      intro q hq
      by_cases hxi : x i
      · have h := ih1 x
        simp [path_to_leaf, hxi] at hq
        cases hq with
        | inl hq => cases hq; simp [hxi]
        | inr hq => exact h q hq
      · have h := ih0 x
        simp [path_to_leaf, hxi] at hq
        cases hq with
        | inl hq => cases hq; simp [hxi]
        | inr hq => exact h q hq

/-!  A reformulation of `path_to_leaf_agrees` in terms of the
    `agreesWithAssignments` predicate.  It records that the point `x`
    generating the path satisfies every assignment along that path. -/
lemma agreesWithAssignments_path_to_leaf (t : DecisionTree n)
    (x : Point n) :
    agreesWithAssignments (n := n) x (path_to_leaf t x) :=
  path_to_leaf_agrees (t := t) (x := x)

/-!  If a point `y` satisfies all coordinate decisions recorded along the
    path of an input `x`, then the decision tree yields the same result on
    `y` as on `x`.  Intuitively, `y` follows the exact same branches as `x`.-/
lemma eval_tree_of_agrees_path (t : DecisionTree n) (x y : Point n)
    (h : agreesWithAssignments (n := n) y (path_to_leaf t x)) :
    eval_tree t y = eval_tree t x := by
  induction t generalizing x y with
  | leaf b =>
      -- With no queries, every point reaches the same leaf.
      simp [path_to_leaf] at h
      simpa [eval_tree, path_to_leaf] using h
  | node i t0 t1 ih0 ih1 =>
      -- The first decision inspects coordinate `i`.
      by_cases hxi : x i
      · -- `x` takes the `true` branch.
        have hcons :=
          (agreesWithAssignments_cons (x := y) (i := i) (b := true)
            (p := path_to_leaf t1 x)).1
            (by simpa [path_to_leaf, hxi] using h)
        rcases hcons with ⟨hyi, htail⟩
        have := ih1 (x := x) (y := y) htail
        have hyi' : y i = true := hyi
        simpa [eval_tree, path_to_leaf, hxi, hyi'] using this
      · -- `x` takes the `false` branch.
        have hcons :=
          (agreesWithAssignments_cons (x := y) (i := i) (b := false)
            (p := path_to_leaf t0 x)).1
            (by simpa [path_to_leaf, hxi] using h)
        rcases hcons with ⟨hyi, htail⟩
        have := ih0 (x := x) (y := y) htail
        have hyi' : y i = false := hyi
        simpa [eval_tree, path_to_leaf, hxi, hyi'] using this

/-!  If every entry of `p` agrees with the corresponding coordinate of `x`,
then `x` lies in the subcube described by `p`. -/
lemma mem_subcube_of_path_of_agrees (x : Point n) :
    ∀ p : List (Fin n × Bool), (∀ q ∈ p, x q.1 = q.2) →
      (subcube_of_path (n := n) p).mem x := by
  intro p
  induction p with
  | nil =>
      intro _; simp [mem_subcube_of_path_nil (n := n) (x := x)]
  | cons q p ih =>
      intro h
      rcases q with ⟨i, b⟩
      have hx_tail : (subcube_of_path (n := n) p).mem x :=
        ih (fun q hq => h q (by simp [hq]))
      have hxi : x i = b := h ⟨i, b⟩ (by simp)
      exact mem_subcube_of_path_cons_of_mem (x := x) (p := p) (i := i) (b := b) hx_tail hxi

lemma mem_subcube_of_path_reverse_path_to_leaf (t : DecisionTree n) (x : Point n) :
    (subcube_of_path ((path_to_leaf t x).reverse)).mem x := by
  classical
  have hagree := path_to_leaf_agrees (t := t) (x := x)
  have hrev : ∀ q ∈ (path_to_leaf t x).reverse, x q.1 = q.2 := by
    intro q hq
    have hq' : q ∈ path_to_leaf t x := by simpa using List.mem_reverse.mpr hq
    exact hagree q hq'
  exact mem_subcube_of_path_of_agrees (x := x) (p := (path_to_leaf t x).reverse) hrev

/-!
Membership in a path-defined subcube is equivalent to the point satisfying
all assignments along that path.  The forward direction is shown by peeling
off the head assignment and applying the induction hypothesis to the tail.
-/
lemma agreesOf_mem_subcube_of_path (x : Point n)
    (p : List (Fin n × Bool))
    (hnodup : (p.map Prod.fst).Nodup) :
    (subcube_of_path (n := n) p).mem x →
      agreesWithAssignments (n := n) x p := by
  classical
  induction p with
  | nil =>
      intro _
      -- The empty path imposes no constraints.
      simpa [agreesWithAssignments_nil (n := n) (x := x)]
  | cons q p ih =>
      rcases q with ⟨i, b⟩
      intro hx
      -- Split the nodup assumption for the tail and the new head index.
      have hnodup_cons : List.Nodup (List.map Prod.fst ((i, b) :: p)) := by
        simpa [List.map_cons] using hnodup
      have hi_not : i ∉ (List.map Prod.fst p) :=
        (List.nodup_cons).1 hnodup_cons |>.1
      have hnodup_tail : (List.map Prod.fst p).Nodup :=
        (List.nodup_cons).1 hnodup_cons |>.2
      -- Membership enforces the head assignment and membership in the tail.
      have hxi : x i = b :=
        mem_subcube_of_path_cons_fixed (n := n) (x := x)
          (p := p) (i := i) (b := b) hx
      -- Show that `i` does not occur among the indices of the tail subcube.
      have hi : i ∉ (subcube_of_path (n := n) p).idx := by
        intro hi_mem
        have hi' : i ∈ (List.map Prod.fst p).toFinset :=
          subcube_of_path_idx_subset_map_fst_toFinset
            (n := n) (p := p) hi_mem
        have : i ∈ List.map Prod.fst p := by
          simpa [List.mem_toFinset] using hi'
        exact hi_not this
      -- Having established freshness of `i`, membership descends to the tail.
      have hx_tail : (subcube_of_path (n := n) p).mem x := by
        intro j hj
        have hj' : j ∈ insert i (subcube_of_path (n := n) p).idx :=
          Finset.mem_insert.mpr (Or.inr hj)
        have hxj := hx j hj'
        have hji : j ≠ i := by
          intro hji; subst hji; exact hi hj
        simpa [subcube_of_path, hji] using hxj
      have hagree_tail : agreesWithAssignments (n := n) x p :=
        ih hnodup_tail hx_tail
      -- Reassemble the full agreement statement.
      exact (agreesWithAssignments_cons (x := x)
        (i := i) (b := b) (p := p)).2 ⟨hxi, hagree_tail⟩

@[simp] lemma mem_subcube_of_path_iff_agrees (x : Point n)
    (p : List (Fin n × Bool)) (hnodup : (p.map Prod.fst).Nodup) :
    (subcube_of_path (n := n) p).mem x ↔
      agreesWithAssignments (n := n) x p := by
  constructor
  · exact agreesOf_mem_subcube_of_path (n := n) (x := x) (p := p) hnodup
  · intro hagree
    -- The converse direction reuses `mem_subcube_of_path_of_agrees`.
    exact mem_subcube_of_path_of_agrees (n := n) (x := x) (p := p) hagree

/-
Удаление ведущего присваивания ослабляет подкуб.  Это справедливо лишь в
случае, когда рассматриваемая координата не встречается в хвосте пути:
иначе позже в списке может быть зафиксировано другое значение, и
включение перестанет выполняться.
-/
lemma mem_subcube_of_path_cons_subset (x : Point n)
    (i : Fin n) (b : Bool) (p : List (Fin n × Bool))
    (hi : i ∉ (subcube_of_path (n := n) p).idx)
    (hx : (subcube_of_path ((i, b) :: p)).mem x) :
    (subcube_of_path p).mem x := by
  -- Проверяем все индексы, фиксированные в хвосте пути.
  intro j hj
  have hj' : j ∈ insert i (subcube_of_path (n := n) p).idx :=
    Finset.mem_insert.mpr (Or.inr hj)
  have hxj := hx j hj'
  have hji : j ≠ i := by
    intro hji; subst hji; exact hi hj
  simpa [subcube_of_path, hji] using hxj

/--
Membership in an extended path subcube is equivalent to satisfying the new
coordinate and belonging to the original subcube, provided the coordinate is
fresh.  This bundles the two helper lemmas
`mem_subcube_of_path_cons_fixed` and `mem_subcube_of_path_cons_subset` into a
single reusable equivalence.-/
@[simp] lemma mem_subcube_of_path_cons (x : Point n)
    (i : Fin n) (b : Bool) (p : List (Fin n × Bool))
    (hi : i ∉ (subcube_of_path (n := n) p).idx) :
    (subcube_of_path ((i, b) :: p)).mem x ↔
      x i = b ∧ (subcube_of_path p).mem x := by
  constructor
  · intro hx
    -- The head assignment fixes the value at coordinate `i`.
    have hxi :=
      mem_subcube_of_path_cons_fixed (n := n) (x := x) (p := p)
        (i := i) (b := b) hx
    -- Membership in the extended subcube descends to the tail.
    have hx_tail :=
      mem_subcube_of_path_cons_subset (n := n) (x := x) (i := i)
        (b := b) (p := p) hi hx
    exact ⟨hxi, hx_tail⟩
  · rintro ⟨hxi, hx_tail⟩
    -- Conversely, satisfying the head and tail assignments yields membership
    -- in the extended subcube.
    exact mem_subcube_of_path_cons_of_mem (n := n) (x := x) (p := p)
      (i := i) (b := b) hx_tail hxi

/-- Adding a constraint on a different coordinate preserves the freshness of
an index.  If `i` does not occur in the index set extracted from `p`, then it
also does not occur after consing a pair for a distinct coordinate `j`.
This technical lemma will be used when analysing how paths grow in recursive
constructions. -/
lemma not_mem_subcube_of_path_cons
    (i j : Fin n) (b : Bool) (p : List (Fin n × Bool))
    (hi : i ∉ (subcube_of_path (n := n) p).idx) (hij : i ≠ j) :
    i ∉ (subcube_of_path ((j, b) :: p)).idx := by
  intro hi'
  -- Membership in the extended index set splits into two possibilities:
  -- either the new coordinate coincides with `i` or it already belonged to the
  -- previous path.  Both contradict the assumptions.
  obtain h | h := Finset.mem_insert.mp
    (by simpa [subcube_of_path_cons_idx] using hi')
  · exact hij h
  · exact hi h

/-- If a coordinate never appears along a path, it is absent from the index set
recorded by `subcube_of_path` for that path. -/
lemma not_mem_subcube_of_path_of_not_mem_fst (i : Fin n)
    (p : List (Fin n × Bool)) (hip : i ∉ p.map Prod.fst) :
    i ∉ (subcube_of_path (n := n) p).idx := by
  induction p with
  | nil => simpa
  | cons hd tl ih =>
      cases' hd with j b
      have hip' : i ≠ j ∧ i ∉ tl.map Prod.fst := by
        simpa [List.map_cons, List.mem_cons, not_or] using hip
      have hij : i ≠ j := hip'.1
      have hip'' : i ∉ tl.map Prod.fst := hip'.2
      have hi := ih hip''
      simpa [List.map_cons] using
        (not_mem_subcube_of_path_cons (n := n) (i := i)
          (j := j) (b := b) (p := tl) hi hij)

/--
If the list of coordinates remains `Nodup` after prefixing `(i, b)`, then the
index set of the tail path does not contain `i`.  This is a convenient
bridging lemma when converting between syntactic freshness on paths and the
semantic statement about subcube indices.-/
lemma not_mem_subcube_of_path_of_nodup_head (i : Fin n) (b : Bool)
    (p : List (Fin n × Bool))
    (hnodup : (((i, b) :: p).map Prod.fst).Nodup) :
    i ∉ (subcube_of_path (n := n) p).idx := by
  -- From `Nodup` we know `i` is absent from `p.map Prod.fst`, and the previous
  -- lemma transports this fact to the index set recorded by `subcube_of_path`.
  have hip : i ∉ p.map Prod.fst :=
    (List.nodup_cons).1 hnodup |>.1
  exact not_mem_subcube_of_path_of_not_mem_fst (n := n) (i := i) (p := p) hip

/--
Если координата `i` отсутствует в списке индексов пути `p`, то
удаление ведущего присваивания `(i, b)` сохраняет принадлежность точки
подкубу, описанному хвостом `p`.  Свежесть `i` формулируется на уровне
списка, что удобно в индуктивных аргументах.-/
lemma mem_subcube_of_path_cons_subset_of_not_mem_fst (x : Point n)
    (i : Fin n) (b : Bool) (p : List (Fin n × Bool))
    (hi : i ∉ p.map Prod.fst)
    (hx : (subcube_of_path ((i, b) :: p)).mem x) :
    (subcube_of_path p).mem x := by
  -- Переводим условие свежести из списка в индексное множество и
  -- применяем базовую лемму `mem_subcube_of_path_cons_subset`.
  refine mem_subcube_of_path_cons_subset (n := n) (x := x) (i := i)
      (b := b) (p := p)
      (hi := not_mem_subcube_of_path_of_not_mem_fst (n := n) (i := i)
        (p := p) hi) hx

/-- Membership of a coordinate in the list of assignments implies membership in
the index set of the associated subcube. -/
lemma mem_subcube_idx_of_mem_path (i : Fin n)
    (p : List (Fin n × Bool)) (hi : i ∈ p.map Prod.fst) :
    i ∈ (subcube_of_path (n := n) p).idx := by
  induction p with
  | nil => cases hi
  | cons hd tl ih =>
      cases' hd with j b
      have hmem' : i = j ∨ ∃ b', (i, b') ∈ tl := by
        simpa [List.map_cons, List.mem_cons] using hi
      rcases hmem' with hji | ⟨b', htl⟩
      · subst hji; simp [subcube_of_path_cons, Subcube.extend]
      · have hidx := ih (List.mem_map.mpr ⟨(i, b'), htl, rfl⟩)
        exact Finset.mem_insert.mpr (Or.inr hidx)

/--
Если координата отсутствует в `idx` подкуба, построенного по пути `p`,
то она не встречается и в самом пути.  Эта форма контрапозиции
используется для обеспечения свежести индексов при анализе ветвлений
деревьев решений.-/
lemma not_mem_path_of_not_mem_subcube_idx (i : Fin n)
    (p : List (Fin n × Bool))
    (hi : i ∉ (subcube_of_path (n := n) p).idx) :
    i ∉ p.map Prod.fst := by
  intro hip
  have hi' := mem_subcube_idx_of_mem_path (n := n) (i := i) (p := p) hip
  exact hi hi'

/-- Consing a fresh coordinate preserves the `Nodup` property on the list of
first components.  This helper lemma streamlines many path manipulations. -/
lemma nodup_map_fst_cons {i : Fin n} {b : Bool} {p : List (Fin n × Bool)}
    (hi : i ∉ p.map Prod.fst) (h : (p.map Prod.fst).Nodup) :
    (((i, b) :: p).map Prod.fst).Nodup := by
  simpa [List.map_cons] using List.nodup_cons.mpr ⟨hi, h⟩

/--
If consing `(i, b)` yields a list of distinct indices, then `i` could not
have appeared in the original path.  This is the converse direction to
`nodup_map_fst_cons` and is handy when the fresh coordinate is witnessed via
`Nodup` on the extended path.-/
lemma not_mem_map_fst_of_cons_nodup {i : Fin n} {b : Bool}
    {p : List (Fin n × Bool)}
    (h : (((i, b) :: p).map Prod.fst).Nodup) :
    i ∉ p.map Prod.fst := by
  classical
  -- Extract the `i ∉` component from `List.nodup_cons` on the mapped list.
  have hip : i ∉ p.map Prod.fst ∧ (p.map Prod.fst).Nodup :=
    List.nodup_cons.mp (by simpa [List.map_cons] using h)
  exact hip.1

/--
A variant of `nodup_map_fst_cons` where freshness is provided via the index
set of the corresponding subcube.  This form is convenient when the available
information is phrased in terms of `subcube_of_path p`. -/
lemma nodup_map_fst_cons_of_not_mem_idx {i : Fin n} {b : Bool}
    {p : List (Fin n × Bool)}
    (hi : i ∉ (subcube_of_path (n := n) p).idx)
    (h : (p.map Prod.fst).Nodup) :
    (((i, b) :: p).map Prod.fst).Nodup := by
  have hip : i ∉ p.map Prod.fst :=
    not_mem_path_of_not_mem_subcube_idx (n := n) (i := i) (p := p) hi
  exact nodup_map_fst_cons (n := n) (i := i) (b := b) (p := p) hip h

/--
If a pair `(j, b)` occurs in a path `p` whose indices are `Nodup`, then the
value assigned to `j` by `subcube_of_path p` is exactly `b`.  The statement is
uniform in the proof `hj` witnessing membership of `j` in the index set of the
resulting subcube.
-/
lemma val_mem_subcube_of_path (p : List (Fin n × Bool))
    (hnodup : (p.map Prod.fst).Nodup)
    {j : Fin n} {b : Bool} (hmem : (j, b) ∈ p) :
    ∀ hj : j ∈ (subcube_of_path (n := n) p).idx,
      (subcube_of_path (n := n) p).val j hj = b := by
  induction p with
  | nil =>
      intro hj; cases hmem
  | cons hd tl ih =>
      rcases hd with ⟨i, bi⟩
      -- Split the nodup hypothesis and the membership information.
      have hnodup_cons : (List.map Prod.fst ((i, bi) :: tl)).Nodup := hnodup
      have hi_not : i ∉ (tl.map Prod.fst) :=
        (List.nodup_cons).1 hnodup_cons |>.1
      have hnodup_tl : (tl.map Prod.fst).Nodup :=
        (List.nodup_cons).1 hnodup_cons |>.2
      have hmem' : (j, b) = (i, bi) ∨ (j, b) ∈ tl := by
        simpa [List.mem_cons] using hmem
      intro hj
      rcases hmem' with hji | htl
      · -- The head assignment matches `(j, b)`.
        cases hji
        -- In this case the value is given directly by the head pair.
        simp [subcube_of_path]  -- `simp` resolves the `by_cases` on `j = i`.
      · -- The pair occurs in the tail; deduce freshness of `j`.
        have hji : j ≠ i := by
          intro hji; subst hji
          exact hi_not (List.mem_map.2 ⟨(j, b), htl, rfl⟩)
        -- Extract membership in the tail subcube from `hj`.
        have hj_tail : j ∈ (subcube_of_path (n := n) tl).idx := by
          have := Finset.mem_insert.mp hj
          rcases this with hj | hj
          · exact False.elim (hji hj)
          · exact hj
        -- Apply the induction hypothesis on the tail.
        have := ih hnodup_tl htl hj_tail
        -- Evaluate the value function using the recursive definition.
        simpa [subcube_of_path, hji, hj_tail] using this

/--
A subcube can be reconstructed from the list of assignments produced by
`Subcube.toList`.  This shows that the list representation faithfully encodes the
subcube, both on its index set and on the values fixed at those indices.
-/
lemma subcube_of_path_eq_self (R : Subcube n) :
    subcube_of_path (n := n) (Subcube.toList (n := n) R) = R := by
  classical
  -- Compare index sets and value functions separately.
  ext j
  · -- Index sets coincide.
    constructor
    · intro hj
      have hmem :=
        subcube_of_path_idx_subset_map_fst_toFinset (n := n)
          (p := Subcube.toList (n := n) R) hj
      have hmem' : j ∈ (Subcube.toList (n := n) R).map Prod.fst := by
        simpa using hmem
      simpa [Subcube.toList] using hmem'
    · intro hj
      have hpair : (j, R.val j hj) ∈ Subcube.toList (n := n) R := by
        unfold Subcube.toList
        set l := R.idx.attach.toList
        set l' := l.mergeSort (fun a b => a.1 < b.1)
        have hjl : ((⟨j, hj⟩) : {i // i ∈ R.idx}) ∈ l := by
          simpa [l] using (List.mem_toList.mpr (Finset.mem_attach _ _))
        have hjl' : ((⟨j, hj⟩) : {i // i ∈ R.idx}) ∈ l' :=
          (List.mem_mergeSort (le := fun a b : {i // i ∈ R.idx} => a.1 < b.1)
            (a := ⟨j, hj⟩) (l := l)).2 hjl
        exact List.mem_map.2 ⟨⟨j, hj⟩, hjl', rfl⟩
      -- Convert pair membership to membership of the first component.
      have hi : j ∈ (Subcube.toList (n := n) R).map Prod.fst :=
        List.mem_map.2 ⟨(j, R.val j hj), hpair, rfl⟩
      have hidx := mem_subcube_idx_of_mem_path (n := n) (i := j)
          (p := Subcube.toList (n := n) R) hi
      simpa using hidx
  · -- Values attached to each index match the original subcube.
    -- `hj` witnesses that `j` lies in the reconstructed index set.
    rename_i hj
    have hi_map :=
      subcube_of_path_idx_subset_map_fst_toFinset (n := n)
        (p := Subcube.toList (n := n) R) hj
    have hi_list : j ∈ (Subcube.toList (n := n) R).map Prod.fst := by
      simpa using hi_map
    rcases List.mem_map.1 hi_list with ⟨⟨k, b⟩, hk_mem, hk_fst⟩
    have hk : k = j := by simpa using hk_fst
    -- Unfold the definition of `toList` to expose the witness in `R.idx`.
    unfold Subcube.toList at hk_mem
    rcases List.mem_map.1 hk_mem with ⟨t, ht_mem, ht_eq⟩
    -- The element `t` of the merged list corresponds to index `j`.
    have hk' : t.1 = k := by cases ht_eq; rfl
    have hb : b = R.val t.1 t.2 := by cases ht_eq; rfl
    -- Membership of `j` in `R.idx`.
    have hjR : j ∈ R.idx := by
      subst hk
      subst hk'
      simpa using t.2
    -- The pair `(j, R.val j hjR)` indeed appears in `R.toList`.
    have hpair : (j, R.val j hjR) ∈ Subcube.toList (n := n) R := by
      subst hk
      subst hk'
      subst hb
      simpa [Subcube.toList] using List.mem_map.2 ⟨t, ht_mem, rfl⟩
    -- Apply the value reconstruction lemma.
    have :=
      val_mem_subcube_of_path (n := n)
        (p := Subcube.toList (n := n) R)
        (hnodup := toList_nodup_fst (n := n) (R := R))
        (j := j) (b := R.val j hjR) hpair hj
    simpa using this

/-!
Every evaluation of the decision tree is witnessed by a suitably
labelled subcube in `coloredSubcubes` containing the input.  This
packages `eval_pair_mem_coloredSubcubes` together with the path
membership property and will be convenient when constructing covers
from decision trees.
-/
lemma coloredSubcubes_cover_eval (t : DecisionTree n) :
    ∀ x : Point n,
      ∃ R : Subcube n, (eval_tree t x, R) ∈ coloredSubcubes (n := n) t ∧ x ∈ₛ R := by
  intro x
  classical
  -- Subcube obtained from the path taken by `x`.
  let R := subcube_of_path ((path_to_leaf t x).reverse)
  have hmem : (eval_tree t x, R) ∈ coloredSubcubes (n := n) t :=
    eval_pair_mem_coloredSubcubes (t := t) (x := x)
  have hxR : x ∈ₛ R :=
    mem_subcube_of_path_reverse_path_to_leaf (t := t) (x := x)
  exact ⟨R, hmem, by simpa [R] using hxR⟩

/-!
Specialisations of `coloredSubcubes_cover_eval` to the concrete colours
`true` and `false`.  These forms emphasise that the sets of
subcubes labelled with a fixed colour cover exactly the inputs mapped to
that colour by the decision tree.
-/
lemma coloredSubcubes_cover_true (t : DecisionTree n) :
    ∀ x : Point n, eval_tree t x = true →
      ∃ R : Subcube n, (true, R) ∈ coloredSubcubes (n := n) t ∧ x ∈ₛ R := by
  intro x hx
  classical
  obtain ⟨R, hmem, hxR⟩ := coloredSubcubes_cover_eval (t := t) (x := x)
  refine ⟨R, ?_, hxR⟩
  -- Rewrite the membership using the fact that `eval_tree t x = true`.
  simpa [hx] using hmem

lemma coloredSubcubes_cover_false (t : DecisionTree n) :
    ∀ x : Point n, eval_tree t x = false →
      ∃ R : Subcube n, (false, R) ∈ coloredSubcubes (n := n) t ∧ x ∈ₛ R := by
  intro x hx
  classical
  obtain ⟨R, hmem, hxR⟩ := coloredSubcubes_cover_eval (t := t) (x := x)
  refine ⟨R, ?_, hxR⟩
  -- Rewrite the membership using the fact that `eval_tree t x = false`.
  simpa [hx] using hmem

/-- Consecutively fixing the same coordinate in the accumulated path has no
effect on the resulting coloured subcubes.  This lemma generalises the simple
subcube equality `subcube_of_path_cons_cons` to the sets of coloured subcubes
produced by a decision tree.  The repeated assignment may occur after an
arbitrary prefix `p`. -/
@[simp] lemma coloredSubcubesAux_cons_cons (t : DecisionTree n)
    (i : Fin n) (b₁ b₂ : Bool)
    (p q : List (Fin n × Bool)) :
    coloredSubcubesAux (n := n) t (p ++ (i, b₁) :: (i, b₂) :: q)
      = coloredSubcubesAux (n := n) t (p ++ (i, b₁) :: q) := by
  classical
  induction t generalizing p with
  | leaf c =>
      -- At a leaf the set of coloured subcubes is a singleton, so the claim
      -- reduces to the corresponding statement about `subcube_of_path`.
      simp [coloredSubcubesAux, subcube_of_path_append_cons_cons,
        List.append_assoc, List.cons_append]
  | node j t0 t1 ih0 ih1 =>
      -- The recursion threads the prefix through both subtrees.  We rewrite
      -- using the inductive hypotheses specialised to the extended prefixes.
      have h0 := ih0 (((j, false) :: p))
      have h1 := ih1 (((j, true) :: p))
      have h0' : coloredSubcubesAux (n := n) t0
          ((j, false) :: (p ++ (i, b₁) :: (i, b₂) :: q))
            = coloredSubcubesAux (n := n) t0
              ((j, false) :: (p ++ (i, b₁) :: q)) := by
        simpa [List.append_assoc, List.cons_append] using h0
      have h1' : coloredSubcubesAux (n := n) t1
          ((j, true) :: (p ++ (i, b₁) :: (i, b₂) :: q))
            = coloredSubcubesAux (n := n) t1
              ((j, true) :: (p ++ (i, b₁) :: q)) := by
        simpa [List.append_assoc, List.cons_append] using h1
      simp [coloredSubcubesAux, h0', h1']

/-! Swapping assignments for two distinct coordinates leaves the set of
coloured subcubes unchanged as long as neither coordinate appears later in the
path.  This lemma transports `subcube_of_path_append_cons_swap` to the coloured
subcube construction. -/
@[simp] lemma coloredSubcubesAux_cons_swap (t : DecisionTree n)
    (i j : Fin n) (bi bj : Bool)
    (p q : List (Fin n × Bool))
    (hi : i ∉ (subcube_of_path (n := n) q).idx)
    (hj : j ∉ (subcube_of_path (n := n) q).idx)
    (hij : i ≠ j) :
    coloredSubcubesAux (n := n) t (p ++ (i, bi) :: (j, bj) :: q)
      = coloredSubcubesAux (n := n) t (p ++ (j, bj) :: (i, bi) :: q) := by
  classical
  induction t generalizing p with
  | leaf c =>
      -- At a leaf the statement reduces to equality of the underlying
      -- subcubes, which follows from
      -- `subcube_of_path_append_cons_swap`.
      have hswap :=
        subcube_of_path_append_cons_swap (n := n) (i := i) (j := j)
          (bi := bi) (bj := bj) (p := p) (q := q)
          (hi := hi) (hj := hj) (hij := hij)
      simpa [coloredSubcubesAux, hswap, List.append_assoc,
        List.cons_append]
  | node k t0 t1 ih0 ih1 =>
      -- Recurse on both subtrees with the prefix extended by the branching
      -- coordinate `k`.
      have h0 := ih0 ((k, false) :: p)
      have h1 := ih1 ((k, true) :: p)
      have h0' : coloredSubcubesAux (n := n) t0
          ((k, false) :: (p ++ (i, bi) :: (j, bj) :: q))
            = coloredSubcubesAux (n := n) t0
              ((k, false) :: (p ++ (j, bj) :: (i, bi) :: q)) := by
        simpa [List.append_assoc, List.cons_append] using h0
      have h1' : coloredSubcubesAux (n := n) t1
          ((k, true) :: (p ++ (i, bi) :: (j, bj) :: q))
            = coloredSubcubesAux (n := n) t1
              ((k, true) :: (p ++ (j, bj) :: (i, bi) :: q)) := by
        simpa [List.append_assoc, List.cons_append] using h1
      simp [coloredSubcubesAux, h0', h1']

/--
Permutation helper moving a coordinate `(j, bj)` across a prefix `p₁`.  The
proof proceeds by iteratively swapping neighbouring assignments via
`coloredSubcubesAux_cons_swap`.  It is stated here for later use in the
permutation lemma and remains to be formalised.
-/
lemma coloredSubcubesAux_cons_bubble (t : DecisionTree n)
    (i j : Fin n) (bi bj : Bool) (p₁ p₂ : List (Fin n × Bool))
    (hi : i ∉ (subcube_of_path (n := n) p₂).idx)
    (hj : j ∉ (subcube_of_path (n := n) p₂).idx)
    (hij : i ≠ j)
    (hj₁ : j ∉ p₁.map Prod.fst) :
    coloredSubcubesAux (n := n) t
        ((i, bi) :: p₁ ++ (j, bj) :: p₂)
      = coloredSubcubesAux (n := n) t
        ((j, bj) :: (i, bi) :: p₁ ++ p₂) := by
  classical
  -- TODO: prove by induction on `p₁` using `coloredSubcubesAux_cons_swap`.
  sorry

/--
Specialised version of `coloredSubcubesAux_cons_subset` for a node that branches
on the very same coordinate as the one being removed.  In this case no path
permutation is required: membership already lies in the appropriate branch of
the shortened colour set.
-/
lemma coloredSubcubesAux_cons_subset_node_same (t₀ t₁ : DecisionTree n)
    (i : Fin n) (b : Bool) (p : List (Fin n × Bool)) (br : Bool × Subcube n)
    (hmem : br ∈ coloredSubcubesAux (n := n)
        (DecisionTree.node i t₀ t₁) ((i, b) :: p)) :
    ∃ brRec ∈ coloredSubcubesAux (n := n)
        (DecisionTree.node i t₀ t₁) p,
      ∀ ⦃x : Point n⦄, Subcube.mem br.2 x → Subcube.mem brRec.2 x := by
  classical
  -- Expand membership in the colour set of the node.
  have hcases :
      br ∈ coloredSubcubesAux (n := n) t₀ ((i, false) :: (i, b) :: p) ∪
            coloredSubcubesAux (n := n) t₁ ((i, true) :: (i, b) :: p) := by
    simpa [coloredSubcubesAux] using hmem
  rcases Finset.mem_union.mp hcases with hleft | hright
  · -- The subcube originates from the left subtree.
    have hset :
        coloredSubcubesAux (n := n) t₀ ((i, false) :: (i, b) :: p)
          = coloredSubcubesAux (n := n) t₀ ((i, false) :: p) := by
      simpa [List.nil_append] using
        (coloredSubcubesAux_cons_cons (t := t₀)
          (i := i) (b₁ := false) (b₂ := b) (p := []) (q := p))
    have hleft' : br ∈ coloredSubcubesAux (n := n) t₀ ((i, false) :: p) := by
      simpa [hset] using hleft
    have hmemRec :
        br ∈ coloredSubcubesAux (n := n)
            (DecisionTree.node i t₀ t₁) p :=
      Finset.mem_union.mpr (Or.inl hleft')
    refine ⟨br, hmemRec, ?_⟩
    intro x hx; simpa using hx
  · -- The subcube stems from the right subtree.
    have hset :
        coloredSubcubesAux (n := n) t₁ ((i, true) :: (i, b) :: p)
          = coloredSubcubesAux (n := n) t₁ ((i, true) :: p) := by
      simpa [List.nil_append] using
        (coloredSubcubesAux_cons_cons (t := t₁)
          (i := i) (b₁ := true) (b₂ := b) (p := []) (q := p))
    have hright' : br ∈ coloredSubcubesAux (n := n) t₁ ((i, true) :: p) := by
      simpa [hset] using hright
    have hmemRec :
        br ∈ coloredSubcubesAux (n := n)
            (DecisionTree.node i t₀ t₁) p :=
      Finset.mem_union.mpr (Or.inr hright')
    refine ⟨br, hmemRec, ?_⟩
    intro x hx; simpa using hx

  /-!
The final, yet unproven, case of `coloredSubcubesAux_cons_subset` deals with
removing an assignment `(i, b)` from the path when the decision node queries a
different coordinate `j` that already occurs somewhere in the tail `p`.  To
handle this situation one has to commute `j` towards the front of `p`, a task
achieved by repeatedly applying `coloredSubcubesAux_cons_swap` in tandem with
the path normalisation lemma `subcube_of_path_append_cons_swap`.  Once the
first occurrence of `j` is exposed, the previously established lemma
`coloredSubcubesAux_cons_subset_node_same` can be invoked.

The swapping argument has not yet been formalised; replacing the earlier axiom
with the lemma below concentrates the remaining work in a single proof
obligation, marked by `sorry`.
-/
lemma coloredSubcubesAux_cons_subset_node_perm (t₀ t₁ : DecisionTree n)
    (i j : Fin n) (b : Bool) (p : List (Fin n × Bool))
    (br : Bool × Subcube n)
    (hmem : br ∈ coloredSubcubesAux (n := n)
                (DecisionTree.node j t₀ t₁) ((i, b) :: p))
    (hi : i ∉ (subcube_of_path (n := n) p).idx)
    (hj : j ∈ (subcube_of_path (n := n) p).idx)
    (hij : i ≠ j) :
    ∃ brRec ∈ coloredSubcubesAux (n := n)
          (DecisionTree.node j t₀ t₁) p,
        ∀ ⦃x : Point n⦄, Subcube.mem br.2 x → Subcube.mem brRec.2 x := by
  classical
  -- We isolate the *first* occurrence of `j` inside the tail path `p`.  The
  -- auxiliary lemma `subcube_of_path_idx_split_first` yields a decomposition
  -- `p = p₁ ++ (j, bj) :: p₂` where the prefix `p₁` avoids any mention of
  -- `j`.  This condition is crucial for the subsequent swapping argument
  -- which requires the segment preceding `(j, bj)` to be free of `j` entirely.
  obtain ⟨bj, p₁, p₂, hsplit, hjp₁⟩ :=
    subcube_of_path_idx_split_first (n := n) (p := p) (j := j) hj
  -- Rewrite the membership assumption using the split path.  The goal is to
  -- eventually bubble the `(j, bj)` assignment to the very front so that
  -- `coloredSubcubesAux_cons_subset_node_same` becomes applicable.
  have hmem' :
      br ∈ coloredSubcubesAux (n := n)
        (DecisionTree.node j t₀ t₁)
        ((i, b) :: (p₁ ++ (j, bj) :: p₂)) := by
    simpa [hsplit, List.cons_append, List.append_assoc] using hmem
  -- The combinatorial heart of the argument is an induction that repeatedly
  -- swaps neighbouring coordinate assignments, implemented by the lemma
  -- `coloredSubcubesAux_cons_swap`.  Because the prefix `p₁` contains no
  -- mention of `j` (captured by `hjp₁`), the pair `(j, bj)` can be moved
  -- leftwards across the prefix until it becomes the head of the entire path.
  --
  -- The intricate bookkeeping required for this permutation – in particular
  -- maintaining the `Nodup` conditions on index sets and updating membership
  -- proofs after each swap – has not yet been formalised.  Finishing the proof
  -- will require an induction on the length of the prefix `p₁`, invoking the
  -- swapping lemma at each step.
  --
  -- Once the path is normalised to `(j, bj) :: (i, b) :: p₁ ++ p₂`, the existing
  -- lemma `coloredSubcubesAux_cons_subset_node_same` can be employed to drop
  -- the head assignment and obtain the required ancestor subcube.
  --
  -- Implementing this reasoning remains future work.
  -- To expose the first occurrence of `j` as the head of the path we successively
  -- swap it with the preceding entries of `p₁`.  Each step relies on the
  -- established lemma `coloredSubcubesAux_cons_swap` and the fact that the
  -- preceding prefix `p₁` avoids `j` (`hjp₁`).
  --
  -- The final permuted form is captured by the following equality of colour
  -- sets:
  have hperm :
      coloredSubcubesAux (n := n) (DecisionTree.node j t₀ t₁)
          ((i, b) :: (p₁ ++ (j, bj) :: p₂))
        = coloredSubcubesAux (n := n) (DecisionTree.node j t₀ t₁)
          ((j, bj) :: (i, b) :: (p₁ ++ p₂)) := by
    -- Move the pair `(j, bj)` to the very front by repeatedly swapping with the
    -- elements of `p₁`.  The helper lemma `coloredSubcubesAux_cons_bubble`
    -- performs exactly this bubbling operation.
    have hi_p2 : i ∉ (subcube_of_path (n := n) p₂).idx := by
      -- TODO: deduce from `hi` using the inclusion of index sets.
      sorry
    have hj_p2 : j ∉ (subcube_of_path (n := n) p₂).idx := by
      -- Membership in the prefix is incompatible with the index set of the
      -- suffix obtained from `subcube_of_path_idx_split_first`.
      -- TODO: derive from `hjp₁`.
      sorry
    have hjp₁' : j ∉ p₁.map Prod.fst := by
      -- Translate the index-set exclusion `hjp₁` to the list representation.
      -- TODO: prove using `subcube_of_path_idx_subset_map_fst_toFinset`.
      sorry
    simpa [List.cons_append, List.append_assoc] using
      (coloredSubcubesAux_cons_bubble (t := DecisionTree.node j t₀ t₁)
        (i := i) (j := j) (bi := b) (bj := bj)
        (p₁ := p₁) (p₂ := p₂)
        (hi := hi_p2) (hj := hj_p2) (hij := hij) (hj₁ := hjp₁'))
  have hmemNorm :
      br ∈ coloredSubcubesAux (n := n)
        (DecisionTree.node j t₀ t₁)
        ((j, bj) :: (i, b) :: (p₁ ++ p₂)) := by
    simpa [hperm, List.cons_append, List.append_assoc] using hmem'
  -- With the normalised path in hand, applying
  -- `coloredSubcubesAux_cons_subset_node_same` would yield the desired result.
  -- The remaining steps are therefore postponed.
  -- TODO: complete the permutation argument and final application.
  sorry

/--
The helper `coloredSubcubesAux_cons_subset` shows that removing the most
recent assignment from the path enlarges the described subcube.  It will be
useful when relating subcubes produced by different branches of a decision
tree.
-/
lemma coloredSubcubesAux_cons_subset (t : DecisionTree n) (i : Fin n) (b : Bool)
    (p : List (Fin n × Bool)) (br : Bool × Subcube n)
    (hmem : br ∈ coloredSubcubesAux (n := n) t ((i, b) :: p))
    (hi : i ∉ (subcube_of_path (n := n) p).idx) :
    ∃ brRec ∈ coloredSubcubesAux (n := n) t p,
      ∀ ⦃x : Point n⦄, Subcube.mem br.2 x → Subcube.mem brRec.2 x := by
  classical
  -- We analyse the structure of the tree.  Removing the head assignment from
  -- the accumulated path corresponds to enlarging the recorded subcube.  The
  -- path `p` is generalised to allow recursive calls with extended paths.
  induction t generalizing p with
  | leaf c =>
      -- The set of coloured subcubes is a singleton, so membership forces
      -- `br` to be this unique element.
      have hsingle : br = ⟨c, subcube_of_path ((i, b) :: p)⟩ := by
        refine Finset.mem_singleton.mp ?_
        simpa [coloredSubcubesAux] using hmem
      subst hsingle
      refine ⟨⟨c, subcube_of_path p⟩, ?_, ?_⟩
      · -- The corresponding element with the shortened path belongs to the
        -- colour set generated from `p` alone.
        simpa [coloredSubcubesAux]
      · -- Membership in the smaller subcube implies membership in the larger
        -- one obtained by dropping the head assignment.
        intro x hx
        exact mem_subcube_of_path_cons_subset (n := n) (x := x)
          (i := i) (b := b) (p := p) (hi := hi) hx
  | node j t0 t1 ih0 ih1 =>
      -- When the root of the tree branches on the same coordinate that is
      -- being removed, the specialised lemma
      -- `coloredSubcubesAux_cons_subset_node_same` immediately provides the
      -- desired ancestor subcube.
      by_cases hji : i = j
      ·
        subst hji
        exact
          coloredSubcubesAux_cons_subset_node_same
            (t₀ := t0) (t₁ := t1) (i := i) (b := b)
            (p := p) (br := br) (hmem := hmem)
      ·
        -- Otherwise the branching coordinate `j` differs from `i`.  If `j`
        -- does not appear in the tail path `p` we may invoke the companion
        -- lemma `coloredSubcubesAux_cons_subset_node_diff`.  The remaining
        -- situation where `j` occurs inside `p` requires a more delicate
        -- permutation argument and is left for future work.
        have hij : i ≠ j := hji
        by_cases hj : j ∈ (subcube_of_path (n := n) p).idx
        ·
          -- When `j` already occurs in the tail path we rely on the
          -- permutation axiom to reorder assignments inside `p` before
          -- applying the inductive hypotheses on the appropriate branch.
          exact
            coloredSubcubesAux_cons_subset_node_perm
              (t₀ := t0) (t₁ := t1) (i := i) (j := j) (b := b)
              (p := p) (br := br) (hmem := hmem) (hi := hi)
              (hj := hj) (hij := hij)
        ·
          have hj' : j ∉ (subcube_of_path (n := n) p).idx := hj
          -- Expand membership in the colour set of the node.
          have hcases :
              br ∈ coloredSubcubesAux (n := n) t0 ((j, false) :: (i, b) :: p) ∪
                    coloredSubcubesAux (n := n) t1 ((j, true) :: (i, b) :: p) := by
            simpa [coloredSubcubesAux] using hmem
          rcases Finset.mem_union.mp hcases with hleft | hright
          · -- The subcube comes from the left subtree.
            have hswap :=
              coloredSubcubesAux_cons_swap (t := t0)
                (i := j) (j := i) (bi := false) (bj := b)
                (p := ([])) (q := p) (hi := hj') (hj := hi) (hij := hij.symm)
            have hleft' :
                br ∈ coloredSubcubesAux (n := n) t0 ((i, b) :: (j, false) :: p) := by
              simpa [List.nil_append] using
                (Eq.mp (congrArg (fun s => br ∈ s) hswap) hleft)
            have hi' :
                i ∉ (subcube_of_path (n := n) ((j, false) :: p)).idx :=
              not_mem_subcube_of_path_cons (n := n)
                (i := i) (j := j) (b := false) (p := p) (hi := hi) (hij := hij)
            obtain ⟨brRec, hmemRec, hsub⟩ :=
              ih0 ((j, false) :: p) hleft' hi'
            have hmemRec' :
                brRec ∈ coloredSubcubesAux (n := n)
                  (DecisionTree.node j t0 t1) p :=
              Finset.mem_union.mpr (Or.inl hmemRec)
            exact ⟨brRec, hmemRec', hsub⟩
          · -- The subcube comes from the right subtree.
            have hswap :=
              coloredSubcubesAux_cons_swap (t := t1)
                (i := j) (j := i) (bi := true) (bj := b)
                (p := ([])) (q := p) (hi := hj') (hj := hi) (hij := hij.symm)
            have hright' :
                br ∈ coloredSubcubesAux (n := n) t1 ((i, b) :: (j, true) :: p) := by
              simpa [List.nil_append] using
                (Eq.mp (congrArg (fun s => br ∈ s) hswap) hright)
            have hi' :
                i ∉ (subcube_of_path (n := n) ((j, true) :: p)).idx :=
              not_mem_subcube_of_path_cons (n := n)
                (i := i) (j := j) (b := true) (p := p) (hi := hi) (hij := hij)
            obtain ⟨brRec, hmemRec, hsub⟩ :=
              ih1 ((j, true) :: p) hright' hi'
            have hmemRec' :
                brRec ∈ coloredSubcubesAux (n := n)
                  (DecisionTree.node j t0 t1) p :=
              Finset.mem_union.mpr (Or.inr hmemRec)
            exact ⟨brRec, hmemRec', hsub⟩

/--
Any coloured subcube `br` produced by `coloredSubcubesAux t p` corresponds to a
sub-cube of the one defined by the initial path `p`.  The proof proceeds by
induction on the tree.
-/
lemma subcube_of_coloredSubcubesAux_le_subcube_of_path (t : DecisionTree n)
    (p : List (Fin n × Bool)) (br : Bool × Subcube n)
    (hmem : br ∈ coloredSubcubesAux (n := n) t p)
    (hnodup : (p.map Prod.fst).Nodup) :
    ∀ x, br.2.mem x → (subcube_of_path (n := n) p).mem x := by
  classical
  induction t generalizing p br with
  | leaf c =>
      intro x hx
      have : br = ⟨c, subcube_of_path (n := n) p⟩ := by
        simpa [coloredSubcubesAux] using Finset.mem_singleton.mp hmem
      cases this
      simpa
  | node j t₀ t₁ ih₀ ih₁ =>
      intro x hx
      have h_union : br ∈
          coloredSubcubesAux (n := n) t₀ ((j, false) :: p) ∪
          coloredSubcubesAux (n := n) t₁ ((j, true) :: p) := by
        simpa [coloredSubcubesAux] using hmem
      rcases Finset.mem_union.mp h_union with h_left | h_right
      · -- `br` arises from the left subtree, i.e. from assigning `j = false`.
        -- To recurse we must show that the root coordinate `j` is fresh for
        -- the tail path `p`.  Intuitively this holds because every extension of
        -- the path adds a new coordinate, but formalising it requires a yet
        -- unproven permutation lemma (`coloredSubcubesAux_cons_subset_node_perm`).
        -- Once that lemma is available we can derive `j ∉ p.map Prod.fst` and
        -- consequently `j ∉ (subcube_of_path p).idx`.
        have hi_notin : j ∉ (subcube_of_path (n := n) p).idx := by
          -- TODO: replace this placeholder using the forthcoming permutation
          -- argument for `coloredSubcubesAux`.
          sorry
        have hnodup' : ((j, false) :: p).map Prod.fst |>.Nodup :=
          nodup_map_fst_cons_of_not_mem_idx (n := n) (i := j) (b := false)
            (p := p) (hi := hi_notin) hnodup
        have h_sub := ih₀ ((j, false) :: p) br h_left hnodup' x hx
        exact mem_subcube_of_path_cons_subset (n := n) (x := x) (i := j)
          (b := false) (p := p) hi_notin h_sub
      · -- Symmetric argument for the right subtree (`j = true`).
        -- As above, we require freshness of `j` with respect to `p`, which
        -- will be obtainable once the permutation lemma has been established.
        have hi_notin : j ∉ (subcube_of_path (n := n) p).idx := by
          -- TODO: populate using `coloredSubcubesAux_cons_subset_node_perm`.
          sorry
        have hnodup' : ((j, true) :: p).map Prod.fst |>.Nodup :=
          nodup_map_fst_cons_of_not_mem_idx (n := n) (i := j) (b := true)
            (p := p) (hi := hi_notin) hnodup
        have h_sub := ih₁ ((j, true) :: p) br h_right hnodup' x hx
        exact mem_subcube_of_path_cons_subset (n := n) (x := x) (i := j)
          (b := true) (p := p) hi_notin h_sub

/--
Removing a single leading assignment enlarges the described subcube.  This
specialised variant of `coloredSubcubesAux_cons_subset` handles the case of an
empty tail path, which suffices for early steps of the cover construction.
-/
lemma coloredSubcubesAux_cons_subset_nil (t : DecisionTree n) (i : Fin n)
    (b : Bool) (br : Bool × Subcube n)
    (hmem : br ∈ coloredSubcubesAux (n := n) t [(i, b)]) :
    ∃ brRec ∈ coloredSubcubesAux (n := n) t [],
      ∀ ⦃x : Point n⦄, Subcube.mem br.2 x → Subcube.mem brRec.2 x := by
  classical
  have hi : i ∉ (subcube_of_path (n := n) ([] : List (Fin n × Bool))).idx := by
    simp
  simpa using
    (coloredSubcubesAux_cons_subset (t := t) (i := i) (b := b) (p := [])
      (br := br) (hmem := hmem) (hi := hi))

/--
Removing a leading assignment for a coordinate `i` at the root of a node that
branches on a different coordinate `j`.  When both `i` and `j` are absent from
the tail path `p`, the coloured subcube descends to the corresponding branch of
the shortened path.
-/
lemma coloredSubcubesAux_cons_subset_node_diff (t₀ t₁ : DecisionTree n)
    (i j : Fin n) (b : Bool) (p : List (Fin n × Bool))
    (br : Bool × Subcube n)
    (hmem : br ∈ coloredSubcubesAux (n := n)
                (DecisionTree.node j t₀ t₁) ((i, b) :: p))
    (hi : i ∉ (subcube_of_path (n := n) p).idx)
    (hj : j ∉ (subcube_of_path (n := n) p).idx)
    (hij : i ≠ j) :
    ∃ brRec ∈ coloredSubcubesAux (n := n)
          (DecisionTree.node j t₀ t₁) p,
        ∀ ⦃x : Point n⦄, Subcube.mem br.2 x → Subcube.mem brRec.2 x := by
  classical
  -- Expand membership in the colour set of the node.
  have hcases :
      br ∈ coloredSubcubesAux (n := n) t₀ ((j, false) :: (i, b) :: p) ∪
            coloredSubcubesAux (n := n) t₁ ((j, true) :: (i, b) :: p) := by
    simpa [coloredSubcubesAux] using hmem
  rcases Finset.mem_union.mp hcases with hleft | hright
  · -- The subcube comes from the left subtree.
    have hswap :=
      coloredSubcubesAux_cons_swap (t := t₀)
        (i := j) (j := i) (bi := false) (bj := b)
        (p := ([])) (q := p) (hi := hj) (hj := hi)
        (hij := hij.symm)
    have hleft' :
        br ∈ coloredSubcubesAux (n := n) t₀ ((i, b) :: (j, false) :: p) := by
      simpa [List.nil_append] using
        (Eq.mp (congrArg (fun s => br ∈ s) hswap) hleft)
    have hi' :
        i ∉ (subcube_of_path (n := n) ((j, false) :: p)).idx :=
      not_mem_subcube_of_path_cons (n := n)
        (i := i) (j := j) (b := false) (p := p) (hi := hi) (hij := hij)
    obtain ⟨brRec, hmemRec, hsub⟩ :=
      (coloredSubcubesAux_cons_subset (t := t₀)
        (i := i) (b := b) (p := (j, false) :: p)
        (br := br) (hmem := hleft') (hi := hi'))
    have hmemRec' :
        brRec ∈ coloredSubcubesAux (n := n)
          (DecisionTree.node j t₀ t₁) p :=
      Finset.mem_union.mpr (Or.inl hmemRec)
    exact ⟨brRec, hmemRec', hsub⟩
  · -- The subcube comes from the right subtree.
    have hswap :=
      coloredSubcubesAux_cons_swap (t := t₁)
        (i := j) (j := i) (bi := true) (bj := b)
        (p := ([])) (q := p) (hi := hj) (hj := hi)
        (hij := hij.symm)
    have hright' :
        br ∈ coloredSubcubesAux (n := n) t₁ ((i, b) :: (j, true) :: p) := by
      simpa [List.nil_append] using
        (Eq.mp (congrArg (fun s => br ∈ s) hswap) hright)
    have hi' :
        i ∉ (subcube_of_path (n := n) ((j, true) :: p)).idx :=
      not_mem_subcube_of_path_cons (n := n)
        (i := i) (j := j) (b := true) (p := p) (hi := hi) (hij := hij)
    obtain ⟨brRec, hmemRec, hsub⟩ :=
      (coloredSubcubesAux_cons_subset (t := t₁)
        (i := i) (b := b) (p := (j, true) :: p)
        (br := br) (hmem := hright') (hi := hi'))
    have hmemRec' :
        brRec ∈ coloredSubcubesAux (n := n)
          (DecisionTree.node j t₀ t₁) p :=
      Finset.mem_union.mpr (Or.inr hmemRec)
    exact ⟨brRec, hmemRec', hsub⟩

/--
If a coloured subcube `br` obtained from `branchOnSubcube R b t` does not
coincide with the primary subcube `R`, then it must arise from the fallback
tree `t`.  In that case `br.2` is contained in some coloured subcube produced
directly by `t`.  The proof proceeds by induction on the path used by
`matchSubcube` to encode `R`.
-/
lemma coloredSubcubes_branchOnSubcube_subset {R : Subcube n} {b : Bool}
    {t : DecisionTree n} {br : Bool × Subcube n}
    (hmem : br ∈ coloredSubcubes (n := n) (branchOnSubcube (n := n) R b t))
    (hne : br.2 ≠ R) :
    ∃ brRec ∈ coloredSubcubes (n := n) t,
      ∀ ⦃x : Point n⦄, Subcube.mem br.2 x → Subcube.mem brRec.2 x := by
  classical
  -- We generalise the statement to arbitrary assignment lists `p` and prove it
  -- by induction on `p`.
  have h_gen : ∀ p : List (Fin n × Bool),
      (p.map Prod.fst).Nodup →
      br ∈ coloredSubcubes (n := n) (matchSubcube (n := n) p b t) →
      br.2 ≠ subcube_of_path (n := n) p →
      ∃ brRec ∈ coloredSubcubes (n := n) t,
        ∀ ⦃x : Point n⦄, Subcube.mem br.2 x → Subcube.mem brRec.2 x := by
    intro p hnodup
    induction p generalizing br with
    | nil =>
        intro hmem hne
        -- The tree is `leaf b`. Its only coloured subcube is `subcube_of_path []`,
        -- contradicting `hne`.
        simp [matchSubcube, coloredSubcubes, coloredSubcubesAux] at hmem
        cases hmem
        simp [subcube_of_path] at hne
    | cons hd tl ih =>
        intro hmem hne
        rcases hd with ⟨i, v⟩
        -- Analyse which branch of the node produced `br`.
        cases v
        · -- Case `v = false`: node `i (matchSubcube tl b t) t`.
          have hmem_unfolded :
              br ∈ coloredSubcubesAux (n := n) (matchSubcube (n := n) tl b t) [(i, false)] ∪
                    coloredSubcubesAux (n := n) t [(i, true)] := by
            simpa [matchSubcube, coloredSubcubes, coloredSubcubesAux] using hmem
          rcases Finset.mem_union.mp hmem_unfolded with h_main | h_branch
          · -- Path continues along the main branch.
            -- After stripping the head assignment we expect to obtain a
            -- coloured subcube produced by `matchSubcube tl b t`.  Showing that
            -- this ancestor does not coincide with `subcube_of_path tl` will
            -- allow an application of the inductive hypothesis.
            -- TODO: formalise this argument and derive the required
            -- contradiction with `hne`.
            sorry
          · -- Path deviates into the fallback tree `t`.
            have h_path : br ∈ coloredSubcubesAux (n := n) t [(i, true)] := h_branch
            obtain ⟨brRec, hmemRec, hsub⟩ :=
              coloredSubcubesAux_cons_subset_nil (t := t) (i := i) (b := true)
                (br := br) (hmem := h_path)
            exact ⟨brRec, by simpa [coloredSubcubes] using hmemRec, hsub⟩
        · -- Case `v = true`: node `i t (matchSubcube tl b t)`.
          have hmem_unfolded :
              br ∈ coloredSubcubesAux (n := n) t [(i, false)] ∪
                    coloredSubcubesAux (n := n) (matchSubcube (n := n) tl b t) [(i, true)] := by
            simpa [matchSubcube, coloredSubcubes, coloredSubcubesAux] using hmem
          rcases Finset.mem_union.mp hmem_unfolded with h_branch | h_main
          · -- Path deviates into the fallback tree `t`.
            have h_path : br ∈ coloredSubcubesAux (n := n) t [(i, false)] := h_branch
            obtain ⟨brRec, hmemRec, hsub⟩ :=
              coloredSubcubesAux_cons_subset_nil (t := t) (i := i) (b := false)
                (br := br) (hmem := h_path)
            exact ⟨brRec, by simpa [coloredSubcubes] using hmemRec, hsub⟩
          · -- Path continues along the main branch (symmetric to the previous case).
            -- As above, removing the initial assignment should expose a coloured
            -- subcube for `matchSubcube tl b t` and lead to an inductive call
            -- once we rule out equality with `subcube_of_path tl`.
            -- TODO: carry out the symmetry argument and apply the inductive step.
            sorry
  -- Specialise the general statement to the list encoding of `R`.
  have hmem' : br ∈ coloredSubcubes (n := n) (matchSubcube (n := n) (R.toList) b t) := by
    simpa [branchOnSubcube] using hmem
  have hnodup_list : (R.toList.map Prod.fst).Nodup := toList_nodup_fst (n := n) R
  have hne' : br.2 ≠ subcube_of_path (n := n) (R.toList) := by
    simpa [subcube_of_path_eq_self (n := n) R] using hne
  exact h_gen (R.toList) hnodup_list hmem' hne'


/--
If a subcube `R` is monochromatic for every function in a family `F` and the
fallback tree `t` only produces monochromatic subcubes for all members of `F`,
then every coloured subcube of `branchOnSubcube R b t` is also monochromatic for
all functions in `F`.
-/
lemma coloredSubcubes_branchOnSubcube_monochromatic {R : Subcube n} {b : Bool}
    {t : DecisionTree n} {F : Family n}
    (hR : ∀ f ∈ F, Subcube.monochromaticFor R f)
    (hRec : ∀ f ∈ F, ∀ br ∈ coloredSubcubes (n := n) t,
        Subcube.monochromaticFor br.2 f) :
    ∀ f ∈ F, ∀ br ∈
        coloredSubcubes (n := n) (branchOnSubcube (n := n) R b t),
        Subcube.monochromaticFor br.2 f := by
  intro f hf br hbr
  classical
  -- Either `br` coincides with the main subcube `R` or it descends from `t`.
  by_cases hbrR : br.2 = R
  · -- If `br` is exactly `R`, the claim follows from the assumption `hR`.
    subst hbrR
    exact hR f hf
  · -- Otherwise `br` comes from the recursive tree.  Locate the ancestor
    -- subcube `brRec` in `t` and transfer monochromaticity along the inclusion.
    obtain ⟨brRec, hbrRec, hsub⟩ :=
      coloredSubcubes_branchOnSubcube_subset (n := n) (R := R) (b := b)
        (t := t) (br := br) hbr hbrR
    have hmonoRec := hRec f hf brRec hbrRec
    exact Subcube.monochromaticFor_subset (n := n) (f := f)
      (R := brRec.2) (S := br.2) hsub hmonoRec

end DecisionTree

/-! ### Path-based family restrictions -/

namespace Family

variable {n : ℕ}

/--
Restrict every function in a family according to a path of fixed coordinates.
Each pair `(i, b)` in the list records that coordinate `i` is set to `b`.
Later occurrences in the path override earlier ones, mirroring
`DecisionTree.subcube_of_path` behaviour. -/
noncomputable def restrictPath (F : Family n) : List (Fin n × Bool) → Family n
  | []        => F
  | (i, b) :: p => (restrictPath F p).restrict i b

@[simp] lemma restrictPath_nil (F : Family n) :
    restrictPath F [] = F := rfl

@[simp] lemma restrictPath_cons (F : Family n) (i : Fin n) (b : Bool)
    (p : List (Fin n × Bool)) :
    restrictPath F ((i, b) :: p) = (restrictPath F p).restrict i b := rfl

/-!  Concatenating paths corresponds to sequentially applying the
    restrictions.  This helper lemma unfolds the recursion and shows
    that processing `p ++ q` is the same as first restricting by `q`
    and then by `p`. -/
lemma restrictPath_append (F : Family n) (p q : List (Fin n × Bool)) :
    restrictPath F (p ++ q) = restrictPath (restrictPath F q) p := by
  induction p with
  | nil =>
      simp [restrictPath]
  | cons hd tl ih =>
      cases hd with
      | mk i b =>
          simp [List.cons_append, restrictPath, ih]

/-- Restricting along a path does not increase sensitivity.  This follows by
iterating `sensitivity_family_restrict_le`. -/
lemma sensitivity_restrictPath_le (F : Family n) (p : List (Fin n × Bool))
    {s : ℕ} [Fintype (Point n)] (Hs : ∀ f ∈ F, sensitivity f ≤ s) :
    ∀ g ∈ restrictPath F p, sensitivity g ≤ s := by
  induction p with
  | nil =>
      simpa using Hs
  | cons q p ih =>
      cases q with
      | mk i b =>
          intro g hg
          have hg' : g ∈ (restrictPath F p).restrict i b := by simpa using hg
          have htail := sensitivity_family_restrict_le
            (F := restrictPath F p) (i := i) (b := b) (s := s) (hF := ih)
          exact htail g hg'

end Family

/--
  Build a depth-zero decision tree for a Boolean function with empty support.
  Such a function is constant on the entire cube, so a single leaf suffices.
-/
lemma exists_decisionTree_of_support_card_zero (f : BFunc n)
    (hzero : (support f).card = 0) :
    ∃ t : DecisionTree n,
      (∀ x : Point n, DecisionTree.eval_tree (n := n) t x = f x) ∧
      DecisionTree.depth (n := n) t ≤ 0 := by
  classical
  -- The empty support implies the function is constant.
  have hsupport_empty : support f = (∅ : Finset (Fin n)) :=
    Finset.card_eq_zero.mp hzero
  have hxconst : ∀ x : Point n, f x = f (fun _ => false) := by
    intro x
    have hx : ∀ i ∈ support f, x i = (fun _ : Fin n => false) i := by
      intro i hi
      have : False := by simpa [hsupport_empty] using hi
      exact this.elim
    simpa using
      (eval_eq_of_agree_on_support (f := f) (x := x)
        (y := fun _ : Fin n => false) hx)
  -- The tree `ofSubcube` for the empty path queries no coordinates.
  refine ⟨DecisionTree.ofSubcube (n := n)
      (R := DecisionTree.subcube_of_path (n := n) ([] : List (Fin n × Bool)))
      (f (fun _ => false)), ?_, ?_⟩
  · intro x
    -- Every point belongs to the subcube described by the empty path.
    have hxmem : x ∈ₛ
        DecisionTree.subcube_of_path (n := n) ([] : List (Fin n × Bool)) := by
      simpa [Subcube.mem, DecisionTree.subcube_of_path]
    -- Evaluation reduces to the constant value.
    have hconst :=
      DecisionTree.eval_ofSubcube_of_mem (n := n)
        (R := DecisionTree.subcube_of_path (n := n) ([] : List (Fin n × Bool)))
        (x := x) (b := f (fun _ => false)) hxmem
    have hx := hxconst x
    simpa [hx.symm] using hconst
  ·
    -- The depth is bounded by the number of fixed coordinates, which is zero.
    have hdepth :=
      DecisionTree.depth_ofSubcube_le
        (n := n)
        (R := DecisionTree.subcube_of_path (n := n) ([] : List (Fin n × Bool)))
        (b := f (fun _ => false))
    simpa [DecisionTree.subcube_of_path] using hdepth

/--
Given any Boolean function `f`, we can build a decision tree that computes it
while querying at most one coordinate for each element of `support f`.  The
resulting tree has depth bounded by the size of the support.

This basic construction performs a case split on a coordinate from the support
and recursively handles the two restricted functions.  When the support is
empty, the function is constant and the tree collapses to a single leaf.
-/
lemma exists_decisionTree_depth_le_support_card (f : BFunc n) :
    ∃ t : DecisionTree n,
      (∀ x : Point n, DecisionTree.eval_tree (n := n) t x = f x) ∧
      DecisionTree.depth (n := n) t ≤ (support f).card := by
  classical
  -- We generalise the statement to any upper bound `k` on the support size and
  -- perform induction on `k`.
  have hgen :
      ∀ k f, (support f).card ≤ k →
        ∃ t : DecisionTree n,
          (∀ x, DecisionTree.eval_tree (n := n) t x = f x) ∧
          DecisionTree.depth (n := n) t ≤ k := by
    refine Nat.rec ?base ?step
    · -- Base case: the support is empty, so the function is constant.
      intro f hf
      -- Translate the bound `hf` into exact emptiness of the support and apply
      -- the constant-function construction.
      have hcard0 : (support f).card = 0 := Nat.le_zero.mp hf
      obtain ⟨t, ht, hdepth⟩ :=
        exists_decisionTree_of_support_card_zero (n := n) (f := f) hcard0
      exact ⟨t, ht, by simpa using hdepth⟩
    · -- Inductive step: split on a coordinate from the support.
      intro k ih f hf
      by_cases hzero : (support f).card = 0
      · -- With empty support the function again collapses to a constant tree.
        obtain ⟨t, ht, hdepth⟩ :=
          exists_decisionTree_of_support_card_zero (n := n) (f := f) hzero
        refine ⟨t, ht, ?_⟩
        -- The produced tree has depth `≤ 0`, which trivially bounds the desired
        -- depth `≤ Nat.succ k`.
        have hle : 0 ≤ Nat.succ k := Nat.zero_le _
        exact hdepth.trans hle
      ·
        -- Choose a coordinate `i` from the nonempty support.
        have hpos : 0 < (support f).card := Nat.pos_of_ne_zero hzero
        obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
        -- Build trees for both restrictions, using the induction hypothesis.
        have hlt0 := support_card_restrict_lt (f := f) (i := i)
            (b := false) (hi := hi)
        have hlt1 := support_card_restrict_lt (f := f) (i := i)
            (b := true) (hi := hi)
        have hle0 : (support (f.restrictCoord i false)).card ≤ k :=
          Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le hlt0 hf)
        have hle1 : (support (f.restrictCoord i true)).card ≤ k :=
          Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le hlt1 hf)
        obtain ⟨t0, ht0, hdepth0⟩ := ih (f.restrictCoord i false) hle0
        obtain ⟨t1, ht1, hdepth1⟩ := ih (f.restrictCoord i true) hle1
        refine ⟨DecisionTree.node i t0 t1, ?_, ?_⟩
        · intro x; cases hxi : x i with
          | false =>
              -- On the `false` branch, evaluate the restricted function.
              have := ht0 x
              have hx := restrictCoord_agrees (f := f) (j := i) (b := false)
                (x := x) (h := hxi)
              simpa [DecisionTree.eval_tree, hxi, hx] using this
          | true =>
              -- Symmetric case for the `true` branch.
              have := ht1 x
              have hx := restrictCoord_agrees (f := f) (j := i) (b := true)
                (x := x) (h := hxi)
              simpa [DecisionTree.eval_tree, hxi, hx] using this
        · -- The depth increases by at most one.
          have hmax :
              max (DecisionTree.depth (n := n) t0)
                  (DecisionTree.depth (n := n) t1) ≤ k :=
            max_le_iff.mpr ⟨hdepth0, hdepth1⟩
          have := Nat.succ_le_succ hmax
          simpa [DecisionTree.depth, Nat.succ_eq_add_one] using this
  -- Apply the general lemma with the exact support size bound.
  exact hgen (support f).card f (Nat.le_refl _)

end BoolFunc
