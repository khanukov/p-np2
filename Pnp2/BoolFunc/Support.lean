import Mathlib.Data.Finset.Basic
import Pnp2.BoolFunc

open Finset

-- Silence linter warnings about `simp`/`simpa` usage in this file.
set_option linter.unnecessarySimpa false

namespace BoolFunc
variable {n : ℕ}

/-- If a coordinate is not in the `support` of `f`, updating that coordinate does
not change the value of `f`. -/
lemma eval_update_not_support {f : BFunc n} {i : Fin n}
    (hi : i ∉ support f) (x : Point n) (b : Bool) :
    f x = f (Point.update x i b) := by
  classical
  have hxall : ∀ z : Point n, f z = f (Point.update z i (!z i)) := by
    simp [mem_support_iff] at hi
    exact hi
  have hx := hxall x
  by_cases hb : b = x i
  · subst hb
    have hupdate : Point.update x i (x i) = x := by
      funext j; by_cases hj : j = i <;> simp [Point.update, hj]
    simp [hupdate]
  · have hb' : b = !x i := by
      cases hxi : x i <;> cases hbv : b <;> simp [hxi, hbv] at *
    simp [hb'.symm] at hx
    exact hx

/-- Every non-trivial function evaluates to `true` at some point. -/
lemma exists_true_on_support {f : BFunc n} (h : support f ≠ ∅) :
    ∃ x, f x = true := by
  classical
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 h
  obtain ⟨x, hx⟩ := mem_support_iff.mp hi
  by_cases hfx : f x = true
  · exact ⟨x, hfx⟩
  · have hxne : f (Point.update x i (!x i)) ≠ f x := by simpa using hx.symm
    cases hupdate : f (Point.update x i (!x i)) with
    | false =>
        have : False := by
          simp [hfx, hupdate] at hxne
        contradiction
    | true =>
        exact ⟨Point.update x i (!x i), by simp [hupdate]⟩

/-!
If two Boolean points agree on every coordinate belonging to the *essential*
`support` of a function, then that function evaluates to the same result on
both points.
The combinatorial proof—incrementally updating coordinates
outside the support—is now complete.
-/
lemma eval_eq_of_agree_on_support {f : BFunc n} {x y : Point n}
    (h : ∀ i ∈ support f, x i = y i) :
    f x = f y := by
  classical
  -- Consider the finite set of coordinates where `x` and `y` differ.
    let T : Finset (Fin n) :=
      Finset.univ.filter fun i => x i ≠ y i
    -- Membership in `T` corresponds exactly to coordinates where `x` and `y`
    -- disagree.  This characterisation will be useful throughout the proof.
    have hTmem : ∀ i : Fin n, i ∈ T ↔ x i ≠ y i := by
      intro i
      have : i ∈ (Finset.univ : Finset (Fin n)) := by simp
      simp [T, this]
    -- Any coordinate in `T` lies outside the support of `f` by hypothesis.
    have hT_not_support : ∀ i ∈ T, i ∉ support f := by
      intro i hi
      have hdiff : x i ≠ y i := (hTmem i).1 hi
      by_contra hmem
      have := h i hmem
      exact hdiff this
  -- Update `x` one coordinate at a time along `T`, using the previous lemma to
  -- keep the evaluation of `f` unchanged.  The technical induction over the
  -- list `T.attach.toList` is deferred to future work.
  have hfold :
      f x =
        f ((T.attach.toList).foldl (fun z i => Point.update z i.1 (y i.1)) x) := by
    -- We generalise the statement to an arbitrary starting point `z` and
    -- perform induction over the list of coordinates to be updated.  At each
    -- step we use `eval_update_not_support` to show that modifying a
    -- non-support coordinate leaves the value of `f` unchanged.
    have hfold_aux :
        ∀ (l : List {i // i ∈ T}) (z : Point n),
          f z =
            f (List.foldl (fun z i => Point.update z i.1 (y i.1)) z l) := by
      intro l z
      induction l generalizing z with
      | nil =>
          -- No coordinates to update: the fold is the identity.
          simp
      | cons i l ih =>
          -- `i.1` is a coordinate from `T`, hence outside the support of `f`.
          have hiT : i.1 ∈ T := by
            -- Membership in `T.attach` projects to membership in `T`.
            simpa using i.property
          have hnot : i.1 ∉ support f := hT_not_support _ hiT
          -- Updating a non-support coordinate preserves the evaluation.
          have hstep :=
            eval_update_not_support (f := f) (i := i.1) (hi := hnot) z (y i.1)
          -- Invoke the inductive hypothesis on the remaining coordinates.
          have htail := ih (Point.update z i.1 (y i.1))
          -- Combine the two equalities and rewrite the fold.
          have hcomb := hstep.trans htail
          simpa [List.foldl_cons] using hcomb
    -- Apply the auxiliary lemma with the specific list `T.attach.toList`.
    simpa using hfold_aux (T.attach.toList) x
  -- After all updates the point coincides with `y`.
  have hfold_eq :
      (T.attach.toList).foldl (fun z i => Point.update z i.1 (y i.1)) x = y := by
    classical
    -- Prove equality by showing both sides agree on every coordinate.
    funext j
    -- Compute the value of the folded point at coordinate `j`.
    have hcoord :
        ((T.attach.toList).foldl (fun z i => Point.update z i.1 (y i.1)) x) j =
          if j ∈ T then y j else x j := by
      -- General auxiliary lemma over arbitrary lists.
      have haux :
          ∀ (l : List {i // i ∈ T}) (z : Point n),
            (l.foldl (fun z i => Point.update z i.1 (y i.1)) z) j =
              if j ∈ l.map Subtype.val then y j else z j := by
        intro l z
        induction l generalizing z with
        | nil =>
            -- No coordinates updated.
            simp
        | cons i l ih =>
            -- Update coordinate `i.1` and recurse on the tail.
            have := ih (Point.update z i.1 (y i.1))
            by_cases hj : j = i.1
            · subst hj
              -- First update hits `j`; afterwards the value is fixed to `y j`.
              simp [List.foldl_cons, this]
            · -- `j` is different from `i.1`; the inductive hypothesis applies.
              simp [List.foldl_cons, hj, this]
      -- Apply the auxiliary lemma to the list of all differing coordinates.
      have hmem : (j ∈ (T.attach.toList.map Subtype.val)) ↔ j ∈ T := by
        constructor
        · intro hj
          rcases List.mem_map.1 hj with ⟨i, hi, hji⟩
          have : i.1 ∈ T := by simpa using i.2
          simpa [hji] using this
        · intro hj
          refine List.mem_map.2 ?_
          refine ⟨⟨j, hj⟩, ?_, rfl⟩
          simp
      have := haux (T.attach.toList) x
      simpa [hmem] using this
    -- With the explicit coordinate description, deduce equality with `y`.
    by_cases hj : j ∈ T
    · simp [hcoord, hj]
    ·
      -- Outside `T` the points already agree.
      have hx_eq : x j = y j := by
        have := (hTmem j).not.mp hj
        exact not_not.mp this
      simp [hcoord, hj, hx_eq]
  -- Combining both facts gives the desired evaluation equality.
  simpa [hfold_eq] using hfold

@[simp] lemma support_const_false (n : ℕ) :
    support (fun _ : Point n => false) = (∅ : Finset (Fin n)) := by
  classical
  ext i
  simp [support]

@[simp] lemma support_const_true (n : ℕ) :
    support (fun _ : Point n => true) = (∅ : Finset (Fin n)) := by
  classical
  ext i
  simp [support]


/-! ### Subcubes determined by the support -/

/--
`supportSubcube f x` freezes every coordinate from the `support` of `f` to
the value it takes in a base point `x`.  Since `f` ignores all other
coordinates, the function is constant on this subcube.
-/
noncomputable def supportSubcube (f : BFunc n) (x : Point n) : Subcube n where
  idx := support f
  val := fun i _ => x i

@[simp] lemma mem_supportSubcube {f : BFunc n} {x y : Point n} :
    (y ∈ₛ supportSubcube f x) ↔ ∀ i ∈ support f, y i = x i := by
  rfl

/-- On the subcube determined by its `support`, a Boolean function is
constant with value `f x`.
-/
lemma supportSubcube_monochromatic (f : BFunc n) (x : Point n) :
    ∀ y : Point n, (supportSubcube f x).mem y → f y = f x := by
  intro y
  intro hy
  have h : ∀ i ∈ support f, y i = x i :=
    (mem_supportSubcube (f := f) (x := x) (y := y)).1 hy
  simpa using
    (eval_eq_of_agree_on_support (f := f) (x := y) (y := x) h)

@[simp] lemma supportSubcube_dim (f : BFunc n) (x : Point n) :
    (supportSubcube f x).dimension = n - (support f).card := by
  rfl

end BoolFunc
