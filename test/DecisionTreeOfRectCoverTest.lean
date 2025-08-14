import Pnp2.DecisionTree

open BoolFunc
open DecisionTree

-- Notation for subcube membership used in existing files
notation x " ∈ₛ " R => Subcube.mem R x

namespace DecisionTreeOfRectCoverTest

/-- A trivial subcube covering the full one-bit cube. -/
def fullSubcube : Subcube 1 :=
  { idx := ∅,
    val := by
      intro i hi
      exact False.elim (Finset.notMem_empty _ hi) }

/-- Single-element set of rectangles used in the examples below. -/
def Rset : Finset (Subcube 1) := {fullSubcube}

/-- Monochromaticity is vacuous for the empty family. -/
lemma hmono :
    ∀ R ∈ Rset, Subcube.monochromaticForFamily R (∅ : Family 1) := by
  intro R hR
  cases hR

/-- The leaf-count bound collapses to `1` for the singleton cover. -/
example :
    leaf_count (ofRectCover (n := 1) false (F := (∅ : Family 1)) Rset hmono) ≤ 1 := by
  -- Apply the general bound and evaluate the resulting fold.
  have h := leaf_count_ofRectCover_le
      (n := 1) (default := false)
      (F := (∅ : Family 1)) (Rset := Rset) (hmono := hmono)
  simpa [Rset, fullSubcube, Subcube.toList] using h

/-- The depth bound evaluates to `0` for the singleton cover. -/
example :
    depth (ofRectCover (n := 1) false (F := (∅ : Family 1)) Rset hmono) ≤ 0 := by
  have h := depth_ofRectCover_le
      (n := 1) (default := false)
      (F := (∅ : Family 1)) (Rset := Rset) (hmono := hmono)
  simpa [Rset, fullSubcube, Subcube.toList] using h

/-- The coloured-subcube count matches the single rectangle in the cover. -/
example :
    (coloredSubcubes
        (ofRectCover (n := 1) false (F := (∅ : Family 1)) Rset hmono)).card ≤ 1 := by
  have h :=
    coloredSubcubes_ofRectCover_card_le
      (n := 1) (default := false)
      (F := (∅ : Family 1)) (Rset := Rset) (hmono := hmono)
  simpa [Rset, fullSubcube, Subcube.toList] using h

/-- A tree where both branches are the same leaf. -/
def dupTree : DecisionTree 1 :=
  DecisionTree.node 0 (DecisionTree.leaf true) (DecisionTree.leaf true)

/-- Only one distinct subcube arises despite two leaves. -/
example :
    (leaves_as_subcubes dupTree).card = 1 := by
  simp [dupTree, leaves_as_subcubes]

/-- The raw leaf count still registers both leaves. -/
example :
    leaf_count dupTree = 2 := by
  simp [dupTree, leaf_count]

/-- The general cardinality bound specialises correctly. -/
example :
    (leaves_as_subcubes dupTree).card ≤ leaf_count dupTree := by
  have h := leaves_as_subcubes_card_le_leaf_count (t := dupTree)
  simpa [dupTree] using h

/-- Combining with the depth bound yields the expected power-of-two estimate. -/
example :
    (leaves_as_subcubes dupTree).card ≤ 2 ^ depth dupTree := by
  have h := leaves_as_subcubes_card_le_pow_depth (t := dupTree)
  simpa [dupTree] using h

/-- A simple branching tree producing both colours. -/
def splitTree : DecisionTree 1 :=
  DecisionTree.node 0 (DecisionTree.leaf false) (DecisionTree.leaf true)

/-- Points with bit `0` and `1` in the single coordinate. -/
def zero : Point 1 := fun _ => false
def one  : Point 1 := fun _ => true

/-- Inputs evaluating to `false` are covered by a `false`-labelled subcube. -/
example :
    ∃ R : Subcube 1, (false, R) ∈ coloredSubcubes (n := 1) splitTree ∧ zero ∈ₛ R := by
  have h :=
    coloredSubcubes_cover_false (t := splitTree)
      (x := zero) (by simpa [splitTree, zero])
  simpa [splitTree, zero] using h

/-- And similarly for the `true` branch. -/
example :
    ∃ R : Subcube 1, (true, R) ∈ coloredSubcubes (n := 1) splitTree ∧ one ∈ₛ R := by
  have h :=
    coloredSubcubes_cover_true (t := splitTree)
      (x := one) (by simpa [splitTree, one])
  simpa [splitTree, one] using h

end DecisionTreeOfRectCoverTest
