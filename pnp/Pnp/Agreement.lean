import Pnp.BoolFunc
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Function
import Mathlib.InformationTheory.Hamming

open Classical
open BoolFunc
open Finset
open BigOperators

namespace Agreement

variable {n ℓ : ℕ}
variable {F : Family n}

/-! ### Core-closed property for families -/

/-- `CoreClosed ℓ F` asserts that any function in `F` that outputs `true`
    on some point `x` must output `true` on all points `y` within Hamming
    distance `ℓ` of `x`. -/
class CoreClosed (ℓ : ℕ) (F : Family n) : Prop where
  closed_under_ball :
    ∀ {f : BFunc n} (hf : f ∈ F) {x y : Point n},
      f x = true → hammingDist x y ≤ ℓ → f y = true

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

/-- Helper: if `y` matches `x` on `I` of size ≥ `n - ℓ`, then
    `hammingDist x y ≤ ℓ`. -/
lemma dist_le_of_compl_subset
    {x y : Point n} {I : Finset (Fin n)}
    (h_size : n - ℓ ≤ I.card)
    (h_mem : y ∈ₛ Subcube.fromPoint x I) :
    hammingDist x y ≤ ℓ := by
  classical
  have h_subset : (Finset.univ.filter fun i => x i ≠ y i) ⊆ Iᶜ := by
    intro i hi
    have hxne : x i ≠ y i := (Finset.mem_filter.mp hi).2
    by_cases hiI : i ∈ I
    · have := h_mem i hiI
      have : x i = y i := by simpa [Subcube.fromPoint] using this.symm
      exact False.elim (hxne this)
    · simpa [Finset.mem_compl] using hiI
  have h_card := Finset.card_le_card h_subset
  have h_bound : (Finset.univ.filter fun i => x i ≠ y i).card ≤ n - I.card := by
    simpa [Finset.card_compl] using h_card
  have h_le_sub : n - I.card ≤ ℓ := by
    have := (Nat.sub_le_iff_le_add.mp h_size)
    have : n ≤ ℓ + I.card := by simpa [Nat.add_comm] using this
    exact Nat.sub_le_iff_le_add.mpr this
  have h_le : (Finset.univ.filter fun i => x i ≠ y i).card ≤ ℓ :=
    h_bound.trans h_le_sub
  simpa [hammingDist] using h_le

/-- **Core-Agreement Lemma**

Let `x₁, x₂ : Point n` be two inputs such that

* There exists a set of coordinates `I` with
  `I.card ≥ n - ℓ` **and** `x₁ i = x₂ i` for every `i ∈ I`;
* Every function `f ∈ F` outputs `1` on *both* `x₁` and `x₂`.

Assuming `CoreClosed ℓ F`, the subcube obtained by fixing the coordinates in `I`
to their shared values is **monochromatic** of colour `1` for the entire family. -/
lemma coreAgreement
    {x₁ x₂ : Point n} (I : Finset (Fin n))
    (h_size  : n - ℓ ≤ I.card)
    (h_agree : ∀ i : Fin n, i ∈ I → x₁ i = x₂ i)
    (h_val1  : ∀ f, f ∈ F → f x₁ = true)
    (h_val2  : ∀ f, f ∈ F → f x₂ = true)
    [CoreClosed ℓ F] :
    (Subcube.fromPoint x₁ I).monochromaticForFamily F := by
  classical
  refine ⟨true, ?_⟩
  intro f hf y hy
  have hx₁ : f x₁ = true := h_val1 f hf
  have hdist : hammingDist x₁ y ≤ ℓ :=
    dist_le_of_compl_subset (n := n) (ℓ := ℓ) (x := x₁) (y := y)
      (I := I) h_size hy
  exact CoreClosed.closed_under_ball (f := f) (hf := hf) hx₁ hdist

open Finset

/--
If `x` and `y` agree on every coordinate in `K`, then both belong to the
subcube `fromPoint x K`. -/
lemma mem_fromPoint_of_agree {n : ℕ} {K : Finset (Fin n)}
    {x y : Point n}
    (h : ∀ i, i ∈ K → x i = y i) :
    y ∈ₛ Subcube.fromPoint x K := by
  intro i hi
  simpa [Subcube.fromPoint] using (h i hi).symm

/-- If two points agree on all coordinates in `K`, then the subcubes
obtained by freezing `K` according to these points coincide. -/
lemma Subcube.point_eq_core {n : ℕ} {K : Finset (Fin n)} {x₀ x : Point n}
    (h : ∀ i, i ∈ K → x i = x₀ i) :
    Subcube.fromPoint x K = Subcube.fromPoint x₀ K := by
  have hval : (fun i (hi : i ∈ K) => x i) = (fun i (hi : i ∈ K) => x₀ i) := by
    funext i hi; simpa [h i hi]
  simp [Subcube.fromPoint, hval]

end Agreement

lemma agree_on_refl {α β : Type _} (f : α → β) (s : Set α) : Set.EqOn f f s :=
  fun x hx => rfl
