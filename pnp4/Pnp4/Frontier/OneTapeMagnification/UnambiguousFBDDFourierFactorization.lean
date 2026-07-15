import Pnp4.Frontier.OneTapeMagnification.FiniteBooleanFourier
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDIndicatorLocality
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorCompleteness

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Exact Fourier decomposition of the filtered uFBDD cut

This file records the exact algebraic part of the corrected CLTW Claim 15
bridge.  The support filter remains part of every contributing cut vertex.
There is no approximation, error estimate, size bound, or lower-bound claim
in this module.
-/

namespace FiniteUnambiguousFBDD

/-- The exact rational indicator of acceptance. -/
noncomputable def ratAcceptanceIndicator {n : Nat}
    (B : FiniteUnambiguousFBDD n) (input : Fin n -> Bool) : Rat := by
  classical
  exact if B.Accepts input then 1 else 0

/-- The exact rational indicator of a semantic filtered cut vertex. -/
noncomputable def ratFilteredAlphaCutIndicator {n : Nat}
    (B : FiniteUnambiguousFBDD n) (input : Fin n -> Bool)
    (alpha : Finset (Fin n)) (k : Nat) (vertex : B.Vertex) : Rat :=
  B.filteredAlphaCutIndicator input alpha k vertex

/-- The exact rational prefix-reachability indicator. -/
noncomputable def ratCompatiblePrefixIndicator {n : Nat}
    (B : FiniteUnambiguousFBDD n) (input : Fin n -> Bool)
    (vertex : B.Vertex) : Rat :=
  B.compatiblePrefixIndicator input vertex

/-- The exact rational accepting-suffix indicator. -/
noncomputable def ratCompatibleAcceptingSuffixIndicator {n : Nat}
    (B : FiniteUnambiguousFBDD n) (input : Fin n -> Bool)
    (vertex : B.Vertex) : Rat :=
  B.compatibleAcceptingSuffixIndicator input vertex

/-- The exact rational, input-independent support-filter indicator. -/
noncomputable def ratFilteredAlphaCutStaticIndicator {n : Nat}
    (B : FiniteUnambiguousFBDD n) (alpha : Finset (Fin n))
    (k : Nat) (vertex : B.Vertex) : Rat :=
  B.filteredAlphaCutStaticIndicator alpha k vertex

/-- A semantic filtered-cut witness always concatenates to an accepting
compatible walk.  This implication does not use unambiguity. -/
theorem accepts_of_hasFilteredAlphaCut {n : Nat}
    {B : FiniteUnambiguousFBDD n} {input : Fin n -> Bool}
    {alpha : Finset (Fin n)} {k : Nat} {vertex : B.Vertex}
    (hcut : B.HasFilteredAlphaCut input alpha k vertex) :
  B.Accepts input := by
  rcases hcut with
    ⟨⟨leftWalk, hleft⟩, ⟨rightWalk, hright⟩, _hstatic⟩
  exact ⟨⟨leftWalk.append rightWalk,
    (Walk.compatible_append input leftWalk rightWalk).mpr
      ⟨hleft, hright⟩⟩⟩

/-- The corrected pointwise Claim-15 identity, including rejected inputs.

On accepted inputs the unique filtered cut contributes one.  On rejected
inputs no compatible prefix/suffix pair can exist, so every summand is zero.
-/
theorem ratAcceptanceIndicator_eq_sum_ratFilteredAlphaCutIndicator
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hunambiguous : B.IsUnambiguous)
    (alpha : Finset (Fin n)) (k : Nat)
    (hreads : forall input (path : B.AcceptingPath input),
      alpha ⊆ path.walk.queryVars)
    (hk : k < alpha.card) (input : Fin n -> Bool) :
    B.ratAcceptanceIndicator input =
      ∑ vertex : B.Vertex,
        B.ratFilteredAlphaCutIndicator input alpha k vertex := by
  classical
  by_cases haccepts : B.Accepts input
  · have haccepts' : B.Accepts input := haccepts
    rcases haccepts with ⟨path⟩
    have hsum := path.sum_filteredAlphaCutIndicator_eq_one
      hreadOnce hunambiguous alpha k (hreads input path) hk
    rw [ratAcceptanceIndicator, if_pos haccepts']
    simp only [ratFilteredAlphaCutIndicator]
    exact_mod_cast hsum.symm
  · have hnone (vertex : B.Vertex) :
        ¬ B.HasFilteredAlphaCut input alpha k vertex := by
      intro hcut
      exact haccepts (accepts_of_hasFilteredAlphaCut hcut)
    simp [ratAcceptanceIndicator, haccepts, ratFilteredAlphaCutIndicator,
      filteredAlphaCutIndicator, hnone]

/-- Rational form of the exact prefix/suffix/static pointwise product. -/
theorem ratFilteredAlphaCutIndicator_eq_prefix_mul_suffix_mul_static
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (input : Fin n -> Bool) (alpha : Finset (Fin n))
    (k : Nat) (vertex : B.Vertex) :
    B.ratFilteredAlphaCutIndicator input alpha k vertex =
      B.ratCompatiblePrefixIndicator input vertex *
      B.ratCompatibleAcceptingSuffixIndicator input vertex *
          B.ratFilteredAlphaCutStaticIndicator alpha k vertex := by
  have hnat :=
    B.filteredAlphaCutIndicator_eq_prefix_mul_suffix_mul_static
      input alpha k vertex
  simpa only [ratFilteredAlphaCutIndicator,
    ratCompatiblePrefixIndicator,
    ratCompatibleAcceptingSuffixIndicator,
    ratFilteredAlphaCutStaticIndicator, Nat.cast_mul] using
      congrArg (fun value : Nat => (value : Rat)) hnat

/-- The rational prefix indicator depends only on the syntactic prefix
variables. -/
theorem ratCompatiblePrefixIndicator_dependsOnlyOn_preVars
    {n : Nat} (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex) :
    FiniteBooleanFourier.DependsOnlyOn (B.preVars vertex)
      (fun input => B.ratCompatiblePrefixIndicator input vertex) := by
  intro input input' hagrees
  have hnat := B.compatiblePrefixIndicator_eq_of_eq_on_preVars
    vertex hagrees
  simpa only [ratCompatiblePrefixIndicator] using
    congrArg (fun value : Nat => (value : Rat)) hnat

/-- The rational suffix indicator depends only on the syntactic suffix
variables. -/
theorem ratCompatibleAcceptingSuffixIndicator_dependsOnlyOn_postVars
    {n : Nat} (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex) :
    FiniteBooleanFourier.DependsOnlyOn (B.postVars vertex)
      (fun input => B.ratCompatibleAcceptingSuffixIndicator input vertex) := by
  intro input input' hagrees
  have hnat := B.compatibleAcceptingSuffixIndicator_eq_of_eq_on_postVars
    vertex hagrees
  simpa only [ratCompatibleAcceptingSuffixIndicator] using
    congrArg (fun value : Nat => (value : Rat)) hnat

/-- Fourier transform commutes with a finite vertex sum. -/
theorem coefficient_fintype_sum {n : Nat} {Vertex : Type}
    [Fintype Vertex] (f : Vertex -> (Fin n -> Bool) -> Rat)
    (alpha : Finset (Fin n)) :
    FiniteBooleanFourier.coefficient (fun input => ∑ vertex, f vertex input)
        alpha =
      ∑ vertex, FiniteBooleanFourier.coefficient (f vertex) alpha := by
  classical
  simp only [FiniteBooleanFourier.coefficient]
  rw [← Finset.sum_div]
  congr 1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Exact Fourier coefficient decomposition over filtered cut vertices. -/
theorem coefficient_ratAcceptanceIndicator_eq_sum_filteredCut
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hunambiguous : B.IsUnambiguous)
    (alpha : Finset (Fin n)) (k : Nat)
    (hreads : forall input (path : B.AcceptingPath input),
      alpha ⊆ path.walk.queryVars)
    (hk : k < alpha.card) :
    FiniteBooleanFourier.coefficient B.ratAcceptanceIndicator alpha =
      ∑ vertex : B.Vertex,
        FiniteBooleanFourier.coefficient
          (fun input => B.ratFilteredAlphaCutIndicator input alpha k vertex)
          alpha := by
  have hfunction : B.ratAcceptanceIndicator =
      fun input => ∑ vertex : B.Vertex,
        B.ratFilteredAlphaCutIndicator input alpha k vertex := by
    funext input
    exact B.ratAcceptanceIndicator_eq_sum_ratFilteredAlphaCutIndicator
      hreadOnce hunambiguous alpha k hreads hk input
  rw [hfunction]
  exact coefficient_fintype_sum
    (fun vertex input => B.ratFilteredAlphaCutIndicator input alpha k vertex)
    alpha

/-- Each filtered vertex coefficient factors into its input-independent
support-filter indicator and the two Fourier coefficients supported on the
prefix and suffix variables.  The support filter is what supplies the
hypothesis `alpha ⊆ preVars vertex ∪ postVars vertex`; it is not discarded.
-/
theorem coefficient_ratFilteredAlphaCutIndicator_eq_static_mul_prefix_mul_suffix
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (alpha : Finset (Fin n)) (k : Nat) (vertex : B.Vertex) :
    FiniteBooleanFourier.coefficient
        (fun input => B.ratFilteredAlphaCutIndicator input alpha k vertex)
        alpha =
      B.ratFilteredAlphaCutStaticIndicator alpha k vertex *
        (FiniteBooleanFourier.coefficient
            (fun input => B.ratCompatiblePrefixIndicator input vertex)
            (alpha ∩ B.preVars vertex) *
          FiniteBooleanFourier.coefficient
            (fun input =>
              B.ratCompatibleAcceptingSuffixIndicator input vertex)
            (alpha ∩ B.postVars vertex)) := by
  classical
  have hfunction :
      (fun input => B.ratFilteredAlphaCutIndicator input alpha k vertex) =
        (fun input =>
          B.ratCompatiblePrefixIndicator input vertex *
            B.ratCompatibleAcceptingSuffixIndicator input vertex *
              B.ratFilteredAlphaCutStaticIndicator alpha k vertex) := by
    funext input
    exact B.ratFilteredAlphaCutIndicator_eq_prefix_mul_suffix_mul_static
      input alpha k vertex
  rw [hfunction]
  by_cases hstatic : B.IsFilteredAlphaCutVertex alpha k vertex
  · have hstaticIndicator :
        B.ratFilteredAlphaCutStaticIndicator alpha k vertex = 1 := by
      simp [ratFilteredAlphaCutStaticIndicator,
        filteredAlphaCutStaticIndicator, hstatic]
    rw [hstaticIndicator]
    simp only [mul_one, one_mul]
    exact FiniteBooleanFourier.coefficient_mul_eq_mul_coefficient_of_disjoint
      (B.ratCompatiblePrefixIndicator_dependsOnlyOn_preVars vertex)
      (B.ratCompatibleAcceptingSuffixIndicator_dependsOnlyOn_postVars vertex)
      (B.indicatorDependencySets_disjoint_of_syntacticallyReadOnce
        hreadOnce vertex)
      hstatic.2.2
  · have hstaticIndicator :
        B.ratFilteredAlphaCutStaticIndicator alpha k vertex = 0 := by
      simp [ratFilteredAlphaCutStaticIndicator,
        filteredAlphaCutStaticIndicator, hstatic]
    rw [hstaticIndicator]
    simp [FiniteBooleanFourier.coefficient]

/-- Fully factored corrected Claim-15 coefficient identity.  This is still an
exact equality; no claim about the magnitude of any factor is made here. -/
theorem coefficient_ratAcceptanceIndicator_eq_sum_static_mul_prefix_mul_suffix
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hunambiguous : B.IsUnambiguous)
    (alpha : Finset (Fin n)) (k : Nat)
    (hreads : forall input (path : B.AcceptingPath input),
      alpha ⊆ path.walk.queryVars)
    (hk : k < alpha.card) :
    FiniteBooleanFourier.coefficient B.ratAcceptanceIndicator alpha =
      ∑ vertex : B.Vertex,
        B.ratFilteredAlphaCutStaticIndicator alpha k vertex *
          (FiniteBooleanFourier.coefficient
              (fun input => B.ratCompatiblePrefixIndicator input vertex)
              (alpha ∩ B.preVars vertex) *
            FiniteBooleanFourier.coefficient
              (fun input =>
                B.ratCompatibleAcceptingSuffixIndicator input vertex)
              (alpha ∩ B.postVars vertex)) := by
  rw [B.coefficient_ratAcceptanceIndicator_eq_sum_filteredCut
    hreadOnce hunambiguous alpha k hreads hk]
  apply Finset.sum_congr rfl
  intro vertex _hvertex
  exact B.coefficient_ratFilteredAlphaCutIndicator_eq_static_mul_prefix_mul_suffix
    hreadOnce alpha k vertex

end FiniteUnambiguousFBDD

/-! ## Mandatory canonical specialization -/

/-- The corrected pointwise cut identity for the mandatory canonical uFBDD.
Positivity of `b` is used only for graph unambiguity; completeness of the
query trace itself is unconditional. -/
theorem mandatoryCanonicalUFBDD_ratAcceptanceIndicator_eq_sum_filteredCut
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b) (alpha : Finset (Fin n)) (k : Nat)
    (hk : k < alpha.card) (input : Fin n -> Bool) :
    (mandatoryCanonicalUFBDD machine n T b).ratAcceptanceIndicator input =
      ∑ vertex : (mandatoryCanonicalUFBDD machine n T b).Vertex,
        (mandatoryCanonicalUFBDD machine n T b).ratFilteredAlphaCutIndicator
          input alpha k vertex := by
  apply FiniteUnambiguousFBDD.ratAcceptanceIndicator_eq_sum_ratFilteredAlphaCutIndicator
  · exact mandatoryCanonicalUFBDD_isSyntacticallyReadOnce machine n T b
  · exact mandatoryCanonicalUFBDD_isUnambiguous machine n T b hb
  · intro currentInput path
    exact mandatoryCanonicalUFBDD_alpha_subset_acceptingPath_queryVars
      machine n T b currentInput alpha path
  · exact hk

/-- Exact Fourier coefficient sum for the mandatory canonical uFBDD. -/
theorem mandatoryCanonicalUFBDD_coefficient_ratAcceptanceIndicator_eq_sum_filteredCut
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b) (alpha : Finset (Fin n)) (k : Nat)
    (hk : k < alpha.card) :
    FiniteBooleanFourier.coefficient
        (mandatoryCanonicalUFBDD machine n T b).ratAcceptanceIndicator alpha =
      ∑ vertex : (mandatoryCanonicalUFBDD machine n T b).Vertex,
        FiniteBooleanFourier.coefficient
          (fun input =>
            FiniteUnambiguousFBDD.ratFilteredAlphaCutIndicator
              (mandatoryCanonicalUFBDD machine n T b) input alpha k vertex)
          alpha := by
  apply FiniteUnambiguousFBDD.coefficient_ratAcceptanceIndicator_eq_sum_filteredCut
  · exact mandatoryCanonicalUFBDD_isSyntacticallyReadOnce machine n T b
  · exact mandatoryCanonicalUFBDD_isUnambiguous machine n T b hb
  · intro input path
    exact mandatoryCanonicalUFBDD_alpha_subset_acceptingPath_queryVars
      machine n T b input alpha path
  · exact hk

/-- Fully factored exact coefficient identity for the mandatory canonical
uFBDD.  Query-trace completeness discharges the path-support hypothesis, and
`b > 0` is needed only for unambiguity. -/
theorem mandatoryCanonicalUFBDD_coefficient_ratAcceptanceIndicator_eq_sum_factored
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (hb : 0 < b) (alpha : Finset (Fin n)) (k : Nat)
    (hk : k < alpha.card) :
    FiniteBooleanFourier.coefficient
        (mandatoryCanonicalUFBDD machine n T b).ratAcceptanceIndicator alpha =
      ∑ vertex : (mandatoryCanonicalUFBDD machine n T b).Vertex,
        FiniteUnambiguousFBDD.ratFilteredAlphaCutStaticIndicator
            (mandatoryCanonicalUFBDD machine n T b) alpha k vertex *
          (FiniteBooleanFourier.coefficient
              (fun input =>
                FiniteUnambiguousFBDD.ratCompatiblePrefixIndicator
                  (mandatoryCanonicalUFBDD machine n T b) input vertex)
              (alpha ∩
                (mandatoryCanonicalUFBDD machine n T b).preVars vertex) *
            FiniteBooleanFourier.coefficient
              (fun input =>
                FiniteUnambiguousFBDD.ratCompatibleAcceptingSuffixIndicator
                  (mandatoryCanonicalUFBDD machine n T b) input vertex)
              (alpha ∩
                (mandatoryCanonicalUFBDD machine n T b).postVars vertex)) := by
  apply FiniteUnambiguousFBDD.coefficient_ratAcceptanceIndicator_eq_sum_static_mul_prefix_mul_suffix
  · exact mandatoryCanonicalUFBDD_isSyntacticallyReadOnce machine n T b
  · exact mandatoryCanonicalUFBDD_isUnambiguous machine n T b hb
  · intro input path
    exact mandatoryCanonicalUFBDD_alpha_subset_acceptingPath_queryVars
      machine n T b input alpha path
  · exact hk

end OneTapeMagnification
end Frontier
end Pnp4
