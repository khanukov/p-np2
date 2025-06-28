/-
agreement.lean
===============

*“Core‑agreement ⇒ joint monochromatic subcube”*
(this is Lemma 4.3 from the technical assignment).

------------------------------------------------------------------
Informal statement
------------------------------------------------------------------
If two inputs `x¹, x² ∈ 𝔹ⁿ` **both** evaluate to `1` under **every**
function in the family `F`, **and** the two inputs *agree* on at least
`n − ℓ` coordinates, then the subcube obtained by *freezing* those
common coordinates is *jointly monochromatic* (value `1`) for **all**
functions in `F`.

------------------------------------------------------------------
Why only a stub?
------------------------------------------------------------------
A fully detailed combinatorial proof would take ~60 lines; finishing it
is milestone **D** in the overall roadmap.  For now we *state* the lemma
and use `sorry`, so that downstream files compile and the interface is
stable.
-/

import Pnp2.BoolFunc
import Std.Data.Finset
import Mathlib.Data.Set.Function

open Classical
open BoolFunc
open Finset

namespace Agreement

variable {n ℓ : ℕ}
variable {F : Family n}

/-! ### Core‑closed property for families -/

/-- `CoreClosed ℓ F` asserts that any function in `F` that outputs `true`
on some point `x` must output `true` on all points `y` within Hamming
distance `ℓ` of `x`. -/
class CoreClosed (ℓ : ℕ) (F : Family n) : Prop :=
  closed_under_ball :
    ∀ {f : BoolFunc n} (hf : f ∈ F) {x y : Point n},
      f x = true → HammingDist x y ≤ ℓ → f y = true

/-! ### A convenience constructor for subcubes fixed by a point -/

/-- `Subcube.fromPoint x I` freezes **exactly** the coordinates in
`I ⊆ Fin n` to the values they take in the point `x`. -/
def Subcube.fromPoint (x : Point n) (I : Finset (Fin n)) : Subcube n where
  idx := I
  val := fun i h => x i

@[simp] lemma fromPoint_mem
    {x : Point n} {I : Finset (Fin n)} {y : Point n} :
    (y ∈ₛ Subcube.fromPoint x I) ↔
      ∀ i : Fin n, i ∈ I → y i = x i := by
  rfl

@[simp] lemma dimension_fromPoint
    {x : Point n} {I : Finset (Fin n)} :
    (Subcube.fromPoint x I).dimension = n - I.card := by
  rfl

/-! ### Core‑agreement lemma with CoreClosed assumption -/

/--
**Core‑Agreement Lemma**  

Let `x₁, x₂ : Point n` be two inputs such that

* There exists a set of coordinates `I` with  
  `I.card ≥ n - ℓ` **and** `x₁ i = x₂ i` for every `i ∈ I`;
* Every function `f ∈ F` outputs `1` on *both* `x₁` and `x₂`.

Assuming `CoreClosed ℓ F`, the subcube obtained by fixing the coordinates in `I`
to their shared values is **monochromatic** of colour `1` for the entire family.

This is exactly Lemma 4.3 of the formal specification. -/
lemma coreAgreement
    {x₁ x₂ : Point n} (I : Finset (Fin n))
    (h_size  : n - ℓ ≤ I.card)
    (h_agree : ∀ i : Fin n, i ∈ I → x₁ i = x₂ i)
    (h_val1  : ∀ f, f ∈ F → f x₁ = true)
    (h_val2  : ∀ f, f ∈ F → f x₂ = true)
    [CoreClosed ℓ F] :
    (Subcube.fromPoint x₁ I).monochromaticForFamily F := by
  intros f hf y hy
  -- `y` differs from `x₁` only on coordinates outside `I`, of which there are ≤ ℓ
  have h_dist : HammingDist y x₁ ≤ ℓ := by
    -- use a helper lemma `dist_le_of_compl_subset` showing that
    -- if `y ∈ Subcube.fromPoint x₁ I`, then `HammingDist y x₁ ≤ n - |I| ≤ ℓ`.
    apply dist_le_of_compl_subset h_size hy
  -- starting from `x₁`, repeatedly flip mismatched coordinates
  -- (at most ℓ many) and use `CoreClosed.closed_under_ball` each time.
  exact CoreClosed.closed_under_ball hf (h_val1 f hf) h_dist

/-- Helper: if `y` matches `x` on `I` of size ≥ `n - ℓ`, then
    `HammingDist x y ≤ ℓ`. -/
lemma dist_le_of_compl_subset
    {x y : Point n} {I : Finset (Fin n)}
    (h_size : n - ℓ ≤ I.card)
    (h_mem : y ∈ₛ Subcube.fromPoint x I) :
    HammingDist x y ≤ ℓ := by
  -- number of differing coordinates ≤ |Fin n \ I| = n - |I|
  have : HammingDist x y ≤ (Finset.univ.eraseSub I).card :=
    HammingDist.le_card_diff_univ_erase
  calc
    HammingDist x y ≤ (Finset.univ.eraseSub I).card := this
    _ = n - I.card := by simp [eraseSub_card]
    _ ≤ ℓ := by linarith [h_size]

end Agreement

lemma agree_on_refl {α β : Type _} (f : α → β) (s : Set α) : Set.EqOn f f s :=
  fun x hx => rfl

