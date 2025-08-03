import Mathlib.Data.Finset.Basic
import Pnp2.BoolFunc

open Finset

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
both points.  The combinatorial proof—incrementally updating coordinates
outside the support—is still pending and will replace this placeholder.
-/
lemma eval_eq_of_agree_on_support {f : BFunc n} {x y : Point n}
    (h : ∀ i ∈ support f, x i = y i) :
    f x = f y := by
  classical
  -- Consider the finite set of coordinates where `x` and `y` differ.
  let T : Finset (Fin n) :=
    Finset.univ.filter fun i => x i ≠ y i
  -- Any coordinate in `T` lies outside the support of `f` by hypothesis.
  have hT_not_support : ∀ i ∈ T, i ∉ support f := by
    intro i hi
    rcases Finset.mem_filter.mp hi with ⟨-, hdiff⟩
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
    -- Prove equality by comparing coordinates one by one.
    ext j
    -- Auxiliary lemma describing the effect of sequential updates on a single
    -- coordinate `j`.
    have haux :
        ∀ (l : List {i // i ∈ T}) (z : Point n),
          (l.foldl (fun z i => Point.update z i.1 (y i.1)) z) j =
            if j ∈ l.map (fun i => i.1) then y j else z j := by
      intro l
      induction l with
      | nil =>
          intro z; simp
      | cons i l ih =>
          intro z
          by_cases hji : j = i.1
          · subst hji
            -- The current step updates coordinate `j` to `y j`.
            simp [List.map, ih, Point.update_eq]
          · have hji' : j ≠ i.1 := hji
            -- Coordinate `j` differs from `i.1`; recurse on the tail.
            simp [List.map, ih, Point.update_neq, hji']
    -- Relate membership in the mapped list to membership in the original
    -- finset `T`.
    have hmem_equiv :
        j ∈ (T.attach.toList.map fun i => i.1) ↔ j ∈ T := by
      constructor
      · intro hjmap
        rcases List.mem_map.1 hjmap with ⟨i, hi, hval⟩
        -- Recover membership in `T.attach` from membership in its list.
        have hiT : i ∈ T.attach := by
          exact Finset.mem_toList.mp hi
        -- Hence the underlying value lies in `T`.
        simpa [hval] using i.property
      · intro hjT
        have hiT : (⟨j, hjT⟩ : {i // i ∈ T}) ∈ T.attach := by
          simpa using (Finset.mem_attach hjT)
        have hiList : (⟨j, hjT⟩ : {i // i ∈ T}) ∈ T.attach.toList :=
          Finset.mem_toList.mpr hiT
        exact List.mem_map.2 ⟨_, hiList, rfl⟩
    -- Apply the auxiliary lemma to the full list of updates.
    specialize haux (T.attach.toList) x
    -- Distinguish whether `j` belongs to `T`.
    by_cases hjT : j ∈ T
    · have hjmap : j ∈ (T.attach.toList.map fun i => i.1) :=
        (hmem_equiv).2 hjT
      simpa [hjmap, hmem_equiv, hjT] using haux
    · have hjmap : j ∉ (T.attach.toList.map fun i => i.1) := by
        intro hjm; exact hjT ((hmem_equiv).1 hjm)
      -- If `j ∉ T`, the original points agree on `j`.
      have hx_eq_y : x j = y j := by
        by_contra hneq
        -- Then `j` would belong to `T` by construction.
        have : j ∈ T := by
          have hjuniv : j ∈ Finset.univ := by simpa
          have hjfilter :
              j ∈ Finset.univ.filter (fun i : Fin n => x i ≠ y i) :=
            Finset.mem_filter.mpr ⟨hjuniv, hneq⟩
          simpa [T] using hjfilter
        exact hjT this
      simpa [hjmap, hmem_equiv, hjT, hx_eq_y] using haux
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

end BoolFunc
