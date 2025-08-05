import Pnp2.Boolcube
import Pnp2.BoolFunc
import Pnp2.entropy
import Pnp2.Cover.Bounds
import Pnp2.Cover.SubcubeAdapters
import Pnp2.Cover.Uncovered
import Pnp2.cover2

-- Silence linter suggestions about using `simp` instead of `simpa` in this file.
set_option linter.unnecessarySimpa false

/-!
This module provides a **lightweight executable wrapper** around the
non‑computable cover construction in `cover2.lean`.

The main development constructs a finite set of monochromatic subcubes via the
function `Cover2.buildCover`.  That definition lives in a classical world and
returns a `Finset`.  For experimentation it is convenient to obtain an actual
`List` of rectangles, hence the function `buildCoverCompute` below simply
enumerates the set produced by `Cover2.buildCover`.

The current implementation does not attempt to be efficient—the heavy lifting
is delegated to `Cover2.buildCover` which itself is still a placeholder in this
repository.  Nevertheless, providing this wrapper keeps the interface stable
while the constructive algorithm is being developed.

`Cover.Bounds` exposes the auxiliary function `mBound` together with several
useful arithmetic lemmas.  We re-export the most common ones so that users of
this module can reason about bounds without importing the full development.
-/

open Cover2

namespace Cover

-- Re-export the numeric bounds from `Cover2` for convenience.
export Cover2 (mBound mBound_pos mBound_zero two_le_mBound mBound_mono_left)

-- Basic Boolean-cube objects and Boolean-function families.
open BoolFunc (Family BFunc)
open Boolcube (Point Subcube)
open Boolcube.Subcube

variable {n : ℕ}


/--
`buildCoverNaive` is a tiny executable baseline for the cover construction.
It scans all points of the Boolean cube and records those on which **every**
function in the family evaluates to `true`.  Each such point becomes a
zero‑dimensional subcube.  The procedure is exponentially slow in `n` but keeps
the code entirely constructive and provides a convenient playground while the
efficient algorithm is being developed.
-/
noncomputable def buildCoverNaive (F : Family n) : List (Subcube n) :=
  ((Finset.univ.filter (fun x : Point n => ∀ f ∈ F, f x = true)).image
      (fun x => Subcube.point (n := n) x)).toList

/--
Basic specification for `buildCoverNaive`.
The resulting list has no duplicates, every listed cube is monochromatic for
the family (with colour `true`) and the length never exceeds the number of
available subcubes.
-/
lemma buildCoverNaive_spec (F : Family n) :
    (buildCoverNaive (n := n) (F := F)).Nodup ∧
    (∀ R ∈ (buildCoverNaive (n := n) (F := F)).toFinset,
        Subcube.monochromaticForFamily R F) ∧
    (buildCoverNaive (n := n) (F := F)).length ≤
      Fintype.card (Subcube n) := by
  classical
  -- Abbreviate the underlying finite set of subcubes.
  set S :=
    (Finset.univ.filter (fun x : Point n => ∀ f ∈ F, f x = true)).image
      (fun x => Subcube.point (n := n) x) with hS
  have hlist : buildCoverNaive (n := n) (F := F) = S.toList := by
    simpa [buildCoverNaive, hS]
  have hnodup : (buildCoverNaive (n := n) (F := F)).Nodup := by
    simpa [hlist] using (Finset.nodup_toList S)
  refine And.intro hnodup ?_
  -- Establish monochromaticity and the cardinality bound.
  refine And.intro ?mono ?bound
  · -- Each element stems from a point where all functions evaluate to `true`.
    intro R hR
    have hR' : R ∈ S := by
      simpa [hlist] using hR
    rcases Finset.mem_image.mp hR' with ⟨x, hx, rfl⟩
    have hx' : ∀ f ∈ F, f x = true :=
      (Finset.mem_filter.mp hx).2
    refine ⟨true, ?_⟩
    intro f hf y hy
    have hy' : x = y :=
      (Subcube.mem_point_iff (x := x) (y := y)).1 hy
    simpa [hy'] using hx' f hf
  · -- The list enumerates a subset of all subcubes.
    have hcard : S.card ≤ Fintype.card (Subcube n) :=
      Finset.card_le_univ _
    have hlen : (buildCoverNaive (n := n) (F := F)).length = S.card := by
      simpa [hlist] using (Finset.length_toList S)
    simpa [hlen]

/--
`buildCoverSearch` provides a tiny constructive cover routine used for
experimentation.  Starting from the empty rectangle set the algorithm keeps
requesting an uncovered witness using `Cover2.firstUncovered`.  For every point
returned it inserts the corresponding zero‑dimensional subcube and continues the
search.  The process repeats for at most `F.card * 2^n` iterations, which is
sufficient to cover every `true` value individually.

This procedure is *exponentially* slow and should only be used as a reference
implementation.  Nevertheless it offers a simple executable model of the cover
construction that avoids the classical reasoning of `Cover2.buildCover`.
-/
noncomputable def buildCoverSearch (F : Family n) : List (Subcube n) := by
  classical
  let fuel := F.card * Fintype.card (Point n)
  -- recursive worker that keeps track of the already chosen rectangles
  let rec loop : Nat → Finset (Subcube n) → List (Subcube n)
    | 0, _ => []
    | Nat.succ fuel, Rset =>
        match Cover2.firstUncovered (n := n) F Rset with
        | none => []
        | some ⟨_, x⟩ =>
            let R := Subcube.point (n := n) x
            -- continue the search with the newly inserted rectangle
            R :: loop fuel (Insert.insert R Rset)
  exact loop fuel (∅ : Finset (Subcube n))


/-!
`buildCoverCompute` below implements a very small executable cover
construction.  It repeatedly queries `Cover2.firstUncovered` and inserts the
corresponding point subcube.  The routine stops after at most `2^n` iterations,
ensuring termination even though the search itself is naive.  The resulting
rectangles are all zero‑dimensional, but this suffices for experimentation.
-/
noncomputable def coverLoop (F : Family n) : Nat → Finset (Subcube n) → Finset (Subcube n)
  | 0, Rset => Rset
  | Nat.succ k, Rset =>
      match Cover2.firstUncovered (n := n) F Rset with
      | none => Rset
      | some ⟨_, x⟩ =>
          let R := Subcube.point (n := n) x
          coverLoop F k (Insert.insert R Rset)

noncomputable def buildCoverCompute (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) : List (Subcube n) :=
  let _ := h; let _ := hH
  let fuel := Fintype.card (Point n)
  (coverLoop (n := n) F fuel (∅ : Finset (Subcube n))).toList

/--
Specification for `buildCoverCompute`.  The returned list contains no
duplicates, every element is a point subcube and the total length is bounded by
`2^n`.
-/
lemma buildCoverCompute_spec (F : Family n) (h : ℕ)
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (buildCoverCompute (F := F) (h := h) hH).Nodup ∧
    (buildCoverCompute (F := F) (h := h) hH).length ≤
      Fintype.card (Point n) := by
  classical
  unfold buildCoverCompute
  set fuel := Fintype.card (Point n) with hfuel
  set loop := coverLoop (n := n) F with hloop
  -- Bound the cardinality of the intermediate set.
  have hcard_aux : ∀ k Rset, (loop k Rset).card ≤ Rset.card + k := by
    intro k; induction k with
    | zero => intro Rset; simp [hloop, coverLoop]
    | succ k ih =>
        intro Rset; cases hfu : Cover2.firstUncovered (n := n) F Rset with
        | none => simpa [coverLoop, hfu, hloop]
        | some p =>
            have ih' := ih (Insert.insert (Subcube.point (n := n) p.2) Rset)
            have hinsert :
                (Insert.insert (Subcube.point (n := n) p.2) Rset).card ≤ Rset.card + 1 :=
              Finset.card_insert_le (a := Subcube.point (n := n) p.2) (s := Rset)
            calc
              (loop (Nat.succ k) Rset).card
                  = (loop k (Insert.insert (Subcube.point (n := n) p.2) Rset)).card := by
                        simp [coverLoop, hfu, hloop]
              _ ≤ (Insert.insert (Subcube.point (n := n) p.2) Rset).card + k := ih'
              _ ≤ (Rset.card + 1) + k := Nat.add_le_add_right hinsert _
              _ = Rset.card + Nat.succ k := by
                simp [Nat.add_comm, Nat.add_left_comm]
  have hcard := hcard_aux fuel (∅ : Finset (Subcube n))
  have hnodup := Finset.nodup_toList (loop fuel (∅ : Finset (Subcube n)))
  have hlen := Finset.length_toList (loop fuel (∅ : Finset (Subcube n)))
  refine And.intro ?nodup ?length
  · simpa [hloop, hfuel] using hnodup
  · have : (loop fuel (∅ : Finset (Subcube n))).card ≤ fuel := by
        simpa [hloop, hfuel] using hcard
    simpa [hloop, hfuel, hlen] using this

end Cover

