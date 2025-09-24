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

/--
Splitting a path at the first occurrence of a coordinate yields suffix
and prefix subpaths that both avoid any further mention of that
coordinate provided the list of indices is `Nodup`.  This strengthened
variant of `subcube_of_path_idx_split_first` records freshness of `j`
for both halves, which is convenient when reasoning about subsequent
permutations.
-/
lemma subcube_of_path_idx_split_first_unique
    {p : List (Fin n × Bool)} {j : Fin n}
    (hj : j ∈ (subcube_of_path (n := n) p).idx)
    (hnodup : (p.map Prod.fst).Nodup) :
    ∃ b p₁ p₂, p = p₁ ++ (j, b) :: p₂ ∧
      j ∉ (subcube_of_path (n := n) p₁).idx ∧
      j ∉ (subcube_of_path (n := n) p₂).idx := by
  classical
  obtain ⟨b, p₁, p₂, hsplit, hjp₁⟩ :=
    subcube_of_path_idx_split_first (n := n) (p := p) (j := j) hj
  -- The nodup condition ensures that `j` cannot appear in the suffix `p₂`.
  have hmap : p.map Prod.fst =
      p₁.map Prod.fst ++ j :: p₂.map Prod.fst := by
    simp [hsplit]
  have hnodup' : (p₁.map Prod.fst ++ j :: p₂.map Prod.fst).Nodup := by
    simpa [hmap] using hnodup
  have hjp₂_list : j ∉ p₂.map Prod.fst :=
    let h := (List.nodup_append.1 hnodup').2.1
    (List.nodup_cons).1 h |>.1
  have hjp₂ : j ∉ (subcube_of_path (n := n) p₂).idx := by
    intro hjmem
    have : j ∈ p₂.map Prod.fst :=
      mem_path_of_mem_subcube_idx (n := n) (i := j) (p := p₂) hjmem
    exact hjp₂_list this
  exact ⟨b, p₁, p₂, hsplit, hjp₁, hjp₂⟩

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
