/-
cover.lean
===========

Top‑level **cover construction** for the Family Collision‑Entropy Lemma.

Interface
---------

* `mBound n h`         — the *numeric* bound
      `n·(h+2)·2^(10 h)` appearing in the spec;
* `cover_exists F h hH` — existential statement:
      a finite set `𝓡` of subcubes satisfying

  1.  every `R ∈ 𝓡` is **jointly monochromatic** for the whole family `F`;
  2.  for every function `f ∈ F`, every `1`‑input of `f`
      lies in (at least) one rectangle of `𝓡`;
  3.  `|𝓡| ≤ mBound n h`.

* `coverFamily F h hH` — a *choice* of such a cover (`noncomputable`).

Both the construction and the proof are currently marked `sorry`; they
depend on yet‑to‑be‑proved lemmas (`EntropyDrop`, `sunflower_exists`,
`coreAgreement`).  Still, the **API is frozen** and downstream files can
import and use `coverFamily` immediately.

Road‑map notes: filling the two `sorry` blocks below is milestone **E**
and **F** of the project plan.
-/

import BoolFunc
import Entropy
import Sunflower
import Agreement
import Mathlib.Data.Nat.Pow
import Mathlib.Tactic

open Classical
open BoolFunc
open Finset

namespace Cover

/-! ## Numeric bound taken from the specification -/

/-- `mBound n h = n·(h+2)·2^(10 h)` — the explicit rectangle bound.  All
cardinalities in the spec are natural numbers, so we keep everything in
`ℕ`. -/
def mBound (n h : ℕ) : ℕ :=
  n * (h + 2) * Nat.pow 2 (10 * h)

/-! ## Existence of a good cover (statement only) -/

variable {n h : ℕ} (F : Family n)

/--
**Existence lemma** — the heart of the FCE‑lemma’s constructive part.

Assume `H₂(F) ≤ h`.  Then there exists a finite set `𝓡` of subcubes
satisfying:  

* **(mono)** each `R ∈ 𝓡` is monochromatic for the entire family `F`;
* **(cover)** for every `f ∈ F` and every `x` with `f x = true`
  there is an `R ∈ 𝓡` such that `x ∈ R`;
* **(bound)** `|𝓡| ≤ mBound n h`.
-/
lemma cover_exists
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∃ (𝓡 : Finset (Subcube n)),
      (∀ R, R ∈ 𝓡 → (Subcube.monochromaticForFamily R F)) ∧
      (∀ f, f ∈ F → ∀ x, f x = true → ∃ R, R ∈ 𝓡 ∧ (x ∈ₛ R)) ∧
      𝓡.card ≤ mBound n h := by
  /- ------------------------------------------------------------------
     **Sketch of the intended constructive proof** (to be formalised):

     1.  *Initialisation*  
         Set `Rset := ∅`, `Fam := F`.

     2.  *Main loop (while there exists `f ∈ Fam` with a 1‑point uncovered)*  
         *Try Sunflower*  
         – Collect, for every `f`, the set of its **currently uncovered
           1‑points**.  Put all those points (over all `f`) into one large
           family `𝒮` of *sets of coordinates* (their support bits).  
         – If `|𝒮|` exceeds the classical Erdős–Rado bound
           `(p − 1)!·wᵖ` (with suitably chosen `w, p`),
           invoke `sunflower_exists` to obtain a common core `I`
           of size `≥ n − ℓ`.  
         – Use `Agreement.coreAgreement` with **two petals** to obtain a
           subcube `R` that is monochromatic `1` for *all* functions
           (colour `1` because the petals were 1‑inputs for every `f`).  
           Add `R` to `Rset`, mark all its points as covered, and repeat.

         *Entropy drop fallback*  
         – If Sunflower fails, use `EntropyDrop` to pick a coordinate
           `(i,b)` that lowers `H₂` by ≥ 1.  *Restrict* all functions
           to `x_i = b`.  Recurse on that smaller instance.  Since
           `H₂` starts ≤ `h`, at most `h` such restrictions happen.

     3.  *Termination & bound*  
         *Each* entropy‑drop adds **two** rectangles (one for `b=0`, one
         for `b=1`) whose union is the full cube, giving ≤ `2h` rectangles.  
         Each sunflower extraction removes ≥ `2^{n-ℓ}` points; with
         `ℓ = ⌈log₂ n⌉` there can be at most `n/ℓ` such extractions.  
         Hence  
            `|Rset| ≤ 2h + n/⌈log₂ n⌉ ≤ n·(h+2)·2^{10h}`.

     All operations preserve joint monochromaticity by construction.
     The full formalisation will follow this plan verbatim.
     ------------------------------------------------------------------ -/
  -- The detailed Lean proof is yet to be written.
  -- We provide `sorry` so that downstream files type‑check.
  sorry

/-! ## A *choice* function (noncomputable) returning one specific cover -/

/-- A concrete (noncomputable) cover obtained via `classical.choice`. -/
noncomputable
def coverFamily
    (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    Finset (Subcube n) :=
  Classical.choice (cover_exists F h hH)

@[simp] lemma coverFamily_spec_mono
    {F : Family n} {h : ℕ} (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∀ R ∈ coverFamily (n := _) (h := h) F hH,
      Subcube.monochromaticForFamily R F := by
  classical
  -- Extract the witness and ignore the other properties.
  obtain ⟨hmono, -, -⟩ :=
    Classical.choose_spec (cover_exists (F := F) (h := h) hH)
  exact hmono

@[simp] lemma coverFamily_spec_cover
    {F : Family n} {h : ℕ} (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    ∀ f, f ∈ F → ∀ x, f x = true →
      ∃ R, R ∈ coverFamily (n := _) (h := h) F hH ∧ (x ∈ₛ R) := by
  classical
  -- The covering property is the second component of `cover_exists`.
  obtain ⟨-, hcover, -⟩ :=
    Classical.choose_spec (cover_exists (F := F) (h := h) hH)
  exact hcover

@[simp] lemma coverFamily_card_bound
    {F : Family n} {h : ℕ} (hH : BoolFunc.H₂ F ≤ (h : ℝ)) :
    (coverFamily (n := _) (h := h) F hH).card ≤ mBound n h := by
  classical
  -- The cardinality bound is the third component of `cover_exists`.
  obtain ⟨-, -, hbound⟩ :=
    Classical.choose_spec (cover_exists (F := F) (h := h) hH)
  exact hbound

end Cover
