import Pnp2.BoolFunc
import Pnp2.BoolFunc.Sensitivity
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
subcubes produced from them. The proof mirrors the legacy version and is
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

end Subcube

open Subcube

namespace DecisionTree

variable {n : ℕ}

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
      cases bi with
      | false =>
          simp [matchSubcube, leaf_count, ih, Nat.mul_succ, Nat.add_comm,
            Nat.add_left_comm]
      | true =>
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
      cases bi with
      | false =>
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
      | true =>
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
Every `true` evaluation of the decision tree is witnessed by a
subcube in `coloredSubcubes` labelled with `true` that contains the
input.  This lemma packages the membership information from
`eval_pair_mem_coloredSubcubes` together with the path membership
property.  It will be convenient when constructing covers from
decision trees.
-/
lemma coloredSubcubes_cover_true (t : DecisionTree n) :
    ∀ x : Point n, eval_tree t x = true →
      ∃ R : Subcube n, (true, R) ∈ coloredSubcubes (n := n) t ∧ x ∈ₛ R := by
  intro x hx
  classical
  -- Subcube obtained from the path taken by `x`.
  let R := subcube_of_path ((path_to_leaf t x).reverse)
  have hmem : (eval_tree t x, R) ∈ coloredSubcubes (n := n) t :=
    eval_pair_mem_coloredSubcubes (t := t) (x := x)
  have hxR : x ∈ₛ R :=
    mem_subcube_of_path_reverse_path_to_leaf (t := t) (x := x)
  refine ⟨R, ?_, ?_⟩
  · -- Rewrite the membership using the fact that `eval_tree t x = true`.
    simpa [R, hx] using hmem
  · simpa [R] using hxR

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

end BoolFunc
