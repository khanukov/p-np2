import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanFourierEnergy

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Coordinate Laplacians for uFBDD accepting suffixes

This module identifies the Fourier filter containing a fixed coordinate with
the corresponding coordinate Laplacian.  It then specializes that exact
finite identity to the accepting-suffix indicator of a finite uFBDD and proves
the pointwise bounds needed by the masked-product argument.

The compatible-prefix homogeneous slice is also shown to depend only on the
syntactic prefix variables.  This file does not regroup the full high-degree
Fourier tail over vertices, sum vertex contributions, or prove a program-level
one-round fooling theorem.
-/

namespace FiniteBooleanSuffixLaplacian

open scoped BigOperators
open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteBooleanFourierEnergy

/-! ## Generic coordinate Laplacian -/

/-- The finite Boolean coordinate Laplacian, using the Walsh convention
`false ↦ +1` and `true ↦ -1`. -/
noncomputable def coordinateLaplacian {n : Nat}
    (f : (Fin n → Bool) → ℚ) (coordinate : Fin n)
    (input : Fin n → Bool) : ℚ :=
  (f input - f (flipCoordinate input coordinate)) / 2

/-- The full Fourier filter consisting of supports that contain a fixed
coordinate. -/
noncomputable def coordinateFourierFilter {n : Nat}
    (f : (Fin n → Bool) → ℚ) (coordinate : Fin n)
    (input : Fin n → Bool) : ℚ :=
  ∑ alpha : Finset (Fin n),
    if coordinate ∈ alpha then
      coefficient f alpha * character alpha input
    else 0

/-- A coordinate Laplacian is exactly the sum of the Fourier terms whose
supports contain that coordinate. -/
theorem coordinateLaplacian_eq_fourierFilter {n : Nat}
    (f : (Fin n → Bool) → ℚ) (coordinate : Fin n)
    (input : Fin n → Bool) :
    coordinateLaplacian f coordinate input =
      coordinateFourierFilter f coordinate input := by
  classical
  unfold coordinateLaplacian coordinateFourierFilter
  calc
    (f input - f (flipCoordinate input coordinate)) / 2 =
        ((∑ alpha : Finset (Fin n),
            coefficient f alpha * character alpha input) -
          (∑ alpha : Finset (Fin n),
            coefficient f alpha *
              character alpha (flipCoordinate input coordinate))) / 2 := by
          rw [fourier_inversion, fourier_inversion]
    _ = ∑ alpha : Finset (Fin n),
          (coefficient f alpha * character alpha input -
            coefficient f alpha *
              character alpha (flipCoordinate input coordinate)) / 2 := by
          rw [← Finset.sum_sub_distrib, Finset.sum_div]
    _ = ∑ alpha : Finset (Fin n),
          if coordinate ∈ alpha then
            coefficient f alpha * character alpha input
          else 0 := by
          apply Finset.sum_congr rfl
          intro alpha _
          rw [character_flipCoordinate]
          by_cases hcoordinate : coordinate ∈ alpha <;>
            simp [hcoordinate]

/-- If `f` depends only on `support`, the coordinate Fourier filter may be
restricted exactly to subsets of `support`. -/
theorem coordinateFourierFilter_eq_sum_powerset {n : Nat}
    {support : Finset (Fin n)} {f : (Fin n → Bool) → ℚ}
    (hf : DependsOnlyOn support f) (coordinate : Fin n)
    (input : Fin n → Bool) :
    coordinateFourierFilter f coordinate input =
      ∑ alpha ∈ support.powerset,
        if coordinate ∈ alpha then
          coefficient f alpha * character alpha input
        else 0 := by
  classical
  unfold coordinateFourierFilter
  symm
  apply Finset.sum_subset
  · simp
  · intro alpha _ hnot
    have hnsubset : ¬ alpha ⊆ support := by
      simpa using hnot
    rw [coefficient_eq_zero_of_not_subset_of_dependsOnlyOn hf hnsubset]
    simp

/-- Support-restricted form of the coordinate-Laplacian Fourier identity. -/
theorem coordinateLaplacian_eq_fourierFilter_on_support {n : Nat}
    {support : Finset (Fin n)} {f : (Fin n → Bool) → ℚ}
    (hf : DependsOnlyOn support f) (coordinate : Fin n)
    (input : Fin n → Bool) :
    coordinateLaplacian f coordinate input =
      ∑ alpha ∈ support.powerset,
        if coordinate ∈ alpha then
          coefficient f alpha * character alpha input
        else 0 := by
  rw [coordinateLaplacian_eq_fourierFilter,
    coordinateFourierFilter_eq_sum_powerset hf]

/-- Taking a coordinate Laplacian preserves every advertised dependency
set. -/
theorem coordinateLaplacian_dependsOnlyOn {n : Nat}
    {support : Finset (Fin n)} {f : (Fin n → Bool) → ℚ}
    (hf : DependsOnlyOn support f) (coordinate : Fin n) :
    DependsOnlyOn support (coordinateLaplacian f coordinate) := by
  intro input input' hagrees
  unfold coordinateLaplacian
  rw [hf hagrees]
  congr 2
  apply hf
  intro queryIndex hqueryIndex
  by_cases heq : queryIndex = coordinate
  · subst queryIndex
    simp [hagrees coordinate hqueryIndex]
  · simp [flipCoordinate_apply_of_ne _ heq,
      hagrees queryIndex hqueryIndex]

/-- A pointwise unit-bounded function has coordinate Laplacian bounded by
one. -/
theorem abs_coordinateLaplacian_le_one {n : Nat}
    (f : (Fin n → Bool) → ℚ)
    (hbounded : ∀ input, |f input| ≤ 1)
    (coordinate : Fin n) (input : Fin n → Bool) :
    |coordinateLaplacian f coordinate input| ≤ 1 := by
  have hdiff :
      |f input - f (flipCoordinate input coordinate)| ≤ (2 : ℚ) := by
    calc
      |f input - f (flipCoordinate input coordinate)| ≤
          |f input| + |f (flipCoordinate input coordinate)| :=
        abs_sub _ _
      _ ≤ 2 := by
        linarith [hbounded input,
          hbounded (flipCoordinate input coordinate)]
  unfold coordinateLaplacian
  rw [abs_div]
  norm_num at *
  linarith

/-- For a function valued in `[0,1]`, the sharper coordinate-Laplacian bound
is one half. -/
theorem abs_coordinateLaplacian_le_half {n : Nat}
    (f : (Fin n → Bool) → ℚ)
    (hbounded : ∀ input, 0 ≤ f input ∧ f input ≤ 1)
    (coordinate : Fin n) (input : Fin n → Bool) :
    |coordinateLaplacian f coordinate input| ≤ (1 : ℚ) / 2 := by
  have hleft := hbounded input
  have hright := hbounded (flipCoordinate input coordinate)
  have hdiff :
      |f input - f (flipCoordinate input coordinate)| ≤ (1 : ℚ) := by
    rw [abs_le]
    constructor <;> linarith
  unfold coordinateLaplacian
  rw [abs_div]
  norm_num at *
  linarith

/-! ## Locality of homogeneous Fourier slices -/

/-- If `f` depends only on `support`, then every homogeneous Fourier slice of
`f` depends only on `support` as well. -/
theorem homogeneousPolynomial_coefficient_dependsOnlyOn
    {n k : Nat} {support : Finset (Fin n)}
    {f : (Fin n → Bool) → ℚ} (hf : DependsOnlyOn support f) :
    DependsOnlyOn support
      (homogeneousPolynomial k (coefficient f)) := by
  intro input input' hagrees
  unfold homogeneousPolynomial
  apply Finset.sum_congr rfl
  intro alpha _
  by_cases hsubset : alpha ⊆ support
  · congr 1
    unfold character
    apply Finset.prod_congr rfl
    intro queryIndex hqueryIndex
    rw [hagrees queryIndex (hsubset hqueryIndex)]
  · rw [coefficient_eq_zero_of_not_subset_of_dependsOnlyOn hf hsubset]
    simp

end FiniteBooleanSuffixLaplacian

namespace FiniteUnambiguousFBDD

open scoped BigOperators
open FiniteBooleanFourier
open FiniteBooleanRestrictionMoment
open FiniteBooleanSuffixLaplacian

/-! ## Prefix and suffix specializations -/

/-- The degree-`k` homogeneous Fourier slice of the compatible-prefix
indicator at a vertex. -/
noncomputable def ratCompatiblePrefixHomogeneousSlice {n : Nat}
    (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex) (k : Nat)
    (input : Fin n → Bool) : ℚ :=
  homogeneousPolynomial k
    (coefficient (fun source =>
      B.ratCompatiblePrefixIndicator source vertex)) input

/-- The compatible-prefix homogeneous slice is local to the syntactic prefix
variables. -/
theorem ratCompatiblePrefixHomogeneousSlice_dependsOnlyOn_preVars
    {n k : Nat} (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex) :
    DependsOnlyOn (B.preVars vertex)
      (B.ratCompatiblePrefixHomogeneousSlice vertex k) := by
  exact homogeneousPolynomial_coefficient_dependsOnlyOn
    (B.ratCompatiblePrefixIndicator_dependsOnlyOn_preVars vertex)

/-- The accepting-suffix Fourier filter selected by the query coordinate at a
vertex.  Silent choice vertices and sinks contribute zero. -/
noncomputable def suffixFourierFilter {n : Nat}
    (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex)
    (input : Fin n → Bool) : ℚ :=
  match B.node vertex with
  | .query coordinate _ _ =>
      ∑ alpha ∈ (B.postVars vertex).powerset,
        if coordinate ∈ alpha then
          coefficient
              (fun source =>
                B.ratCompatibleAcceptingSuffixIndicator source vertex)
              alpha *
            character alpha input
        else 0
  | .choice _ => 0
  | .sink => 0

/-- The coordinate Laplacian of the accepting-suffix indicator selected by
the query coordinate at a vertex.  Silent choice vertices and sinks
contribute zero. -/
noncomputable def suffixLaplacian {n : Nat}
    (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex)
    (input : Fin n → Bool) : ℚ :=
  match B.node vertex with
  | .query coordinate _ _ =>
      coordinateLaplacian
        (fun source =>
          B.ratCompatibleAcceptingSuffixIndicator source vertex)
        coordinate input
  | .choice _ => 0
  | .sink => 0

/-- At a query vertex, the suffix Laplacian is the coordinate Laplacian at
that vertex's query. -/
theorem suffixLaplacian_eq_coordinateLaplacian_of_node_eq_query
    {n : Nat} (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex)
    (coordinate : Fin n) (ifFalse ifTrue : B.Vertex)
    (hnode : B.node vertex = .query coordinate ifFalse ifTrue)
    (input : Fin n → Bool) :
    B.suffixLaplacian vertex input =
      coordinateLaplacian
        (fun source =>
          B.ratCompatibleAcceptingSuffixIndicator source vertex)
        coordinate input := by
  simp [suffixLaplacian, hnode]

/-- Query-vertex form of the exact suffix Fourier-filter identity. -/
theorem suffixLaplacian_eq_fourierFilter_of_node_eq_query
    {n : Nat} (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex)
    (coordinate : Fin n) (ifFalse ifTrue : B.Vertex)
    (hnode : B.node vertex = .query coordinate ifFalse ifTrue)
    (input : Fin n → Bool) :
    B.suffixLaplacian vertex input =
      ∑ alpha ∈ (B.postVars vertex).powerset,
        if coordinate ∈ alpha then
          coefficient
              (fun source =>
                B.ratCompatibleAcceptingSuffixIndicator source vertex)
              alpha *
            character alpha input
        else 0 := by
  rw [B.suffixLaplacian_eq_coordinateLaplacian_of_node_eq_query
    vertex coordinate ifFalse ifTrue hnode]
  exact coordinateLaplacian_eq_fourierFilter_on_support
    (B.ratCompatibleAcceptingSuffixIndicator_dependsOnlyOn_postVars vertex)
    coordinate input

/-- The canonical suffix Fourier filter is exactly the canonical suffix
coordinate Laplacian at every vertex. -/
theorem suffixLaplacian_eq_fourierFilter {n : Nat}
    (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex)
    (input : Fin n → Bool) :
    B.suffixLaplacian vertex input =
      B.suffixFourierFilter vertex input := by
  cases hnode : B.node vertex with
  | query coordinate ifFalse ifTrue =>
      simpa [suffixFourierFilter, hnode] using
        B.suffixLaplacian_eq_fourierFilter_of_node_eq_query
          vertex coordinate ifFalse ifTrue hnode input
  | choice children => simp [suffixLaplacian, suffixFourierFilter, hnode]
  | sink => simp [suffixLaplacian, suffixFourierFilter, hnode]

/-- The canonical suffix Laplacian depends only on the syntactic suffix
variables. -/
theorem suffixLaplacian_dependsOnlyOn_postVars {n : Nat}
    (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex) :
    DependsOnlyOn (B.postVars vertex) (B.suffixLaplacian vertex) := by
  intro input input' hagrees
  cases hnode : B.node vertex with
  | query coordinate ifFalse ifTrue =>
      have hlocal :=
        coordinateLaplacian_dependsOnlyOn
          (B.ratCompatibleAcceptingSuffixIndicator_dependsOnlyOn_postVars
            vertex)
          coordinate
      simpa [suffixLaplacian, hnode] using hlocal hagrees
  | choice children =>
      simp [suffixLaplacian, hnode]
  | sink =>
      simp [suffixLaplacian, hnode]

/-- The rational accepting-suffix indicator is valued in `[0,1]`. -/
theorem ratCompatibleAcceptingSuffixIndicator_unitInterval {n : Nat}
    (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex)
    (input : Fin n → Bool) :
    0 ≤ B.ratCompatibleAcceptingSuffixIndicator input vertex ∧
      B.ratCompatibleAcceptingSuffixIndicator input vertex ≤ 1 := by
  classical
  by_cases hsuffix : B.HasCompatibleAcceptingSuffix input vertex <;>
    simp [ratCompatibleAcceptingSuffixIndicator,
      compatibleAcceptingSuffixIndicator, hsuffix]

/-- Because the suffix indicator is `{0,1}`-valued, its coordinate Laplacian
has the sharper pointwise bound `1/2`. -/
theorem abs_suffixLaplacian_le_half {n : Nat}
    (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex)
    (input : Fin n → Bool) :
    |B.suffixLaplacian vertex input| ≤ (1 : ℚ) / 2 := by
  cases hnode : B.node vertex with
  | query coordinate ifFalse ifTrue =>
      rw [B.suffixLaplacian_eq_coordinateLaplacian_of_node_eq_query
        vertex coordinate ifFalse ifTrue hnode]
      exact abs_coordinateLaplacian_le_half _
        (B.ratCompatibleAcceptingSuffixIndicator_unitInterval vertex)
        coordinate input
  | choice children => simp [suffixLaplacian, hnode]
  | sink => simp [suffixLaplacian, hnode]

/-- Paper-strength corollary of the sharper `1/2` suffix-Laplacian bound. -/
theorem abs_suffixLaplacian_le_one {n : Nat}
    (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex)
    (input : Fin n → Bool) :
    |B.suffixLaplacian vertex input| ≤ (1 : ℚ) := by
  exact (B.abs_suffixLaplacian_le_half vertex input).trans (by norm_num)

/-- The canonical suffix Fourier filter inherits the sharper pointwise
`1/2` bound from the coordinate Laplacian. -/
theorem abs_suffixFourierFilter_le_half {n : Nat}
    (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex)
    (input : Fin n → Bool) :
    |B.suffixFourierFilter vertex input| ≤ (1 : ℚ) / 2 := by
  rw [← B.suffixLaplacian_eq_fourierFilter vertex input]
  exact B.abs_suffixLaplacian_le_half vertex input

end FiniteUnambiguousFBDD
end OneTapeMagnification
end Frontier
end Pnp4
