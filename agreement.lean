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

import BoolFunc
import Std.Data.Finset

open Classical
open BoolFunc
open Finset

namespace Agreement

variable {n ℓ : ℕ}
variable {F : Family n}

/-! ### A convenience constructor for subcubes fixed by a point -/

/-- `Subcube.fromPoint x I` freezes **exactly** the coordinates in
`I ⊆ Fin n` to the values they take in the point `x`.                     -/
def Subcube.fromPoint (x : Point n) (I : Finset (Fin n)) : Subcube n where
  idx := I
  val := fun i h => x i

@[simp] lemma fromPoint_mem
    {x : Point n} {I : Finset (Fin n)} {y : Point n} :
    (y ∈ₛ Subcube.fromPoint x I) ↔
      ∀ i : Fin n, i ∈ I → y i = x i := by
  rfl

/-! ### Core‑agreement lemma (statement only) -/

/--
**Core‑Agreement Lemma**  

Let `x₁, x₂ : Point n` be two inputs such that

* There exists a set of coordinates `I` with  
  `I.card ≥ n - ℓ` **and** `x₁ i = x₂ i` for every `i ∈ I`;
* Every function `f ∈ F` outputs `1` on *both* `x₁` and `x₂`.

Then the subcube obtained by fixing the coordinates in `I`
to their shared values is **monochromatic** of colour `1`
for the entire family.

This is exactly Lemma 4.3 of the formal specification.               -/
lemma coreAgreement
    {x₁ x₂ : Point n} (I : Finset (Fin n))
    (h_size : n - ℓ ≤ I.card)
    (h_agree : ∀ i : Fin n, i ∈ I → x₁ i = x₂ i)
    (h_val1 : ∀ f, f ∈ F → f x₁ = true)
    (h_val2 : ∀ f, f ∈ F → f x₂ = true) :
    (Subcube.fromPoint x₁ I).monochromaticForFamily F := by
  -- TODO: combinatorial proof (using, e.g., flipping the ℓ free
  --       coordinates one‑by‑one and inducting on Hamming distance).
  --       Marked as `sorry` for now so all imports compile.
  sorry

end Agreement
