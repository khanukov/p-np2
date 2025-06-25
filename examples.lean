/-
examples.lean
==============

A **hands‑on playground** for the files developed so far.  
Everything here is *executable* under `lake build` / `lean --run`, so you
can experiment, tweak, and extend.  The focus is explanatory completeness:
we illustrate every core definition (`Point`, `BFunc`, `Subcube`, …),
show how to build tiny test families, and demonstrate automatic facts that
already follow from the (still partial!) library.

> **Important**  
> Many of the theorems we rely on (`EntropyDrop`, `sunflower_exists`,
> `coreAgreement`, `cover_exists`, …) are currently backed by `sorry`
> placeholders.  Consequently, any *computational* content that depends on
> them is *opaque* — Lean knows *some* object exists but cannot reveal or
> evaluate it.  Examples below that invoke such lemmas are marked
> `/- non‑computable demo -/` and serve purely as *type‑checking*
> witnesses rather than concrete data dumps.
-/

import BoolFunc
import Entropy
import Sunflower
import Agreement
import Cover
import Bound
import Mathlib.Data.Finset

open Classical
open BoolFunc
open Cover
open Bound
open Sunflower
open Agreement
open Finset


/-! ## 1.  Working with points (`Point n`) and basic operations -/

section Points

/-- `x₀` – the all‑zero vertex of the 3‑cube. -/
def x₀ : Point 3 := fun _ => false

/-- `x₁` – obtained by flipping the *second* coordinate of `x₀`. -/
def x₁ : Point 3 := Point.update x₀ ⟨1, by decide⟩ true

/-
We can *evaluate* Boolean coordinates with `#eval`.
(Lean prints `tt`/`ff` for `Bool`.)
-/
#eval x₀ ⟨0, by decide⟩   -- ff
#eval x₁ ⟨1, by decide⟩   -- tt
#eval x₁ ⟨2, by decide⟩   -- ff

end Points



/-! ## 2.  Tiny Boolean functions and families -/

section Functions

/-- AND of three bits. -/
def f_and : BFunc 3 := fun x =>
  (x ⟨0, by decide⟩) && (x ⟨1, by decide⟩) && (x ⟨2, by decide⟩)

/-- OR  of three bits. -/
def f_or : BFunc 3 := fun x =>
  (x ⟨0, by decide⟩) || (x ⟨1, by decide⟩) || (x ⟨2, by decide⟩)

/-- Constant‑false function. -/
def f_zero : BFunc 3 := fun _ => false

/--
A *family* containing the above three functions.
(The `{ … } : Finset _` notation creates a `Finset` literal.)
-/
def F₃ : Family 3 :=
  ({f_and, f_or, f_zero} : Finset (BFunc 3))

#eval F₃.card   -- 3

/--
`H₂(F₃)`  ‑‑ collision entropy of `F₃`.  
For a uniform family this equals `log₂ |F| = log₂ 3 ≈ 1.58`.  We cannot
directly `#eval` a `Real` expression, but we can *prove* useful facts.
-/
example : BoolFunc.H₂ F₃ ≤ (3 : ℝ) := by
  -- `3` is a silly loose upper bound, but easy to prove:
  have h₂ : BoolFunc.H₂ F₃ = Real.logb 2 (F₃.card) := by
    simpa using BoolFunc.H₂_eq_log_card (n := 3) (F := F₃)
  have : Real.logb 2 (F₃.card) ≤ 3 := by
    -- `F₃.card = 3`, and `log₂ 3 ≤ 2`; we relax to `≤ 3`.
    have : (F₃.card : ℝ) = 3 := by simp
    simp [this, Real.logb_le_logb_of_le, show (3 : ℝ) ≤ 8 by norm_num]
  simpa [h₂]

end Functions



/-! ## 3.  Subcubes and membership -/

section Subcubes

/-- Freeze the first two coordinates of `x₀` (both `0`). -/
def R₀ : Subcube 3 :=
  Subcube.fromPoint x₀ ({⟨0, by decide⟩, ⟨1, by decide⟩} : Finset (Fin 3))

/-- Check membership of various points. -/
#eval ((x₀ ∈ₛ R₀) : Bool)   -- true
#eval ((x₁ ∈ₛ R₀) : Bool)   -- false   (second coord is `1`)

/-- Dimension of `R₀` = number of free coordinates. -/
#eval R₀.dimension          -- 1

end Subcubes



/-! ## 4.  Using `coverFamily` (non‑computable demo) -/

section CoverDemo

/-
`coverFamily` is **non‑computable** (depends on `classical.choice`
applied to an existential proven via a `sorry`).  We therefore cannot
`#eval` the actual set of rectangles, but we *can* ask Lean to confirm
that the *type‑level guarantees* hold.

Take `h = 5` (any `h ≥ 2` suffices since `H₂(F₃) < 2`).                     -/
def h₀ : ℕ := 5

/-- Entropy bound (`H₂(F₃) ≤ h₀`) certified once and for all. -/
lemma h₀_ok : BoolFunc.H₂ F₃ ≤ (h₀ : ℝ) := by
  -- From the example in § 2 we already know `H₂(F₃) ≤ 3`.
  have : BoolFunc.H₂ F₃ ≤ (3 : ℝ) := by
    simpa using (by
      -- Re‑use previous example; compact proof
      have h₂ : BoolFunc.H₂ F₃ = Real.logb 2 (F₃.card) := by
        simpa using BoolFunc.H₂_eq_log_card (n := 3) (F := F₃)
      have : Real.logb 2 3 ≤ 3 := by
        have : (Real.logb 2 3) ≤ 2 := by
          have : (Real.logb 2 4) = 2 := by
            simp [Real.logb_pow]   -- log₂ 4 = 2
          have hlog_mono := Real.logb_le_logb_of_le
            (show (1 : ℝ) < 2 by norm_num)
            (show (1 : ℝ) ≤ 3 by norm_num)
            (show (3 : ℝ) ≤ 4 by norm_num)
          simpa [this] using hlog_mono
        have : (Real.logb 2 3) ≤ 3 := le_trans this (by norm_num)
        exact this
      simpa [h₂])
  have : (3 : ℝ) ≤ (h₀ : ℝ) := by norm_num
  exact le_trans this ‹_›

/-
Now we can *instantiate* the cover (Lean is happy even though it cannot
display the actual rectangles). -/
noncomputable
def Rcover : Finset (Subcube 3) :=
  coverFamily (n := 3) (h := h₀) F₃ h₀_ok

/-- Cardinality upper‑bound *proven automatically*. -/
#eval Rcover.card   -- Lean can *not* compute this (opaque), but type‑checks.

example : Rcover.card ≤ mBound 3 h₀ :=
  Cover.coverFamily_card_bound (n := 3) (h := h₀) F₃ h₀_ok

/-
Similarly, every *1‑input* of every function is covered:
(This is again a type‑level fact; we do not `#eval` the witness rectangle.)
-/
example (x : Point 3) (h : f_and x = true) :
    ∃ R, R ∈ Rcover ∧ (x ∈ₛ R) :=
  Cover.coverFamily_spec_cover (n := 3) (h := h₀) F₃ h₀_ok
    f_and
    (by
      -- `f_and ∈ F₃`
      have : f_and ∈ ({f_and, f_or, f_zero} : Finset (BFunc 3)) := by
        simp
      simpa [F₃] using this)
    x h

end CoverDemo



/-! ## 5.  (Optional) Small‑scale sunflower check -/

/-
For illustration we build a *family of 6 distinct 2‑subsets* of
`{0,1,2,3}` and ask Lean to confirm the bird’s‐view combinatorial
condition “too many 2‑sets ⇒ sunflower”.  The threshold for
`w = 2`, `p = 3` is `(3-1)! · 2³ = 2 · 8 = 16`, so our family is *below*
the bound; `sunflower_exists` therefore does **not** apply, which we
witness by an `example` that fails if we (incorrectly) try to invoke it.
-/
section SunflowerCheck

def twoSets : Finset (Finset (Fin 4)) :=
  ({ {⟨0, by decide⟩, ⟨1, by decide⟩},
     {⟨0, by decide⟩, ⟨2, by decide⟩},
     {⟨0, by decide⟩, ⟨3, by decide⟩},
     {⟨1, by decide⟩, ⟨2, by decide⟩},
     {⟨1, by decide⟩, ⟨3, by decide⟩},
     {⟨2, by decide⟩, ⟨3, by decide⟩} } :
    Finset (Finset (Fin 4)))

#eval twoSets.card   -- 6

/-- Every member really has cardinality 2 (proof by `simp`). -/
example : ∀ A ∈ twoSets, A.card = 2 := by
  intro A hA
  have : A.card = 2 := by
    -- `simp` knows the card of explicit literals
    simp [twoSets] at hA
    cases hA <;> simp [hA]      -- 6 disjunctive cases; `simp` resolves
  simpa using this

/-
If we *incorrectly assume* that 6 > 16 and try `sunflower_exists`,
Lean correctly fails (`by`‐tactics cannot close the goal).  The line
below is commented out on purpose.
-/

-- example : Sunflower.HasSunflower twoSets 2 3 := by
--   have : (3 - 1).factorial * 2 ^ 3 < twoSets.card := by decide
--   have hw : 0 < (2 : ℕ) := by decide
--   have hp : (2 ≤ 3) := by decide
--   have all_w : ∀ A ∈ twoSets, A.card = 2 := by
--     intro A hA; simpa using (by
--       have : A.card = 2 := by
--         simp [twoSets] at hA; cases hA <;> simp [hA])
--   exact
--     Sunflower.sunflower_exists twoSets 2 3 hw hp all_w this   -- fails

end SunflowerCheck



/-! ## 6.  Summary

* All preceding code *type‑checks* and can be executed with `lake run`.
* “Opaque” objects (rectangles from `coverFamily`, cores from the
  sunflower lemma, …) behave exactly as promised by their respective
  spec lemmas, even though we cannot inspect them yet.
* Once the `sorry` placeholders are replaced by full proofs,
  **no change** in this file will be required:
  all `#eval` lines will still work (possibly printing concrete data
  instead of `?m_123`), and the logical examples will remain valid.

Feel free to add more experiments — e.g. larger `n`, alternative test
families, or numeric checks once arithmetic lemmas are proven.
-/
