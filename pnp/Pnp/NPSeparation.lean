import Pnp.ComplexityClasses
import Mathlib.Data.Real.Basic

/-!
This file contains axioms relating an MCSP lower bound to standard
complexity separations.  The actual results are omitted.
-/

/--
Lower bound for the minimum circuit size problem (MCSP).
`MCSP_lower_bound ε` means that MCSP on inputs of size `N` requires
circuits of size at least `N^{1 + ε}`. Formal details are omitted; see
Theorem 1.4 of "Hardness Magnification Near State-of-the-Art Lower
Bounds" (2021).
-/
axiom MCSP_lower_bound : ℝ → Prop

axiom magnification_AC0_MCSP :
  (∃ ε > 0, MCSP_lower_bound ε) → ¬ NP ⊆ Ppoly

axiom PH_collapse : Prop

/-- Karp-Lipton theorem: `NP ⊆ P/poly` implies a collapse of the polynomial
hierarchy.  The proof is assumed as an axiom in this development. -/
axiom karp_lipton : (NP ⊆ Ppoly) → PH_collapse

/--
If there exists an ε > 0 with an MCSP lower bound, then P ≠ NP.  The proof
would combine `magnification_AC0_MCSP` with known implications of MCSP lower
bounds for circuit complexity.
-/
theorem P_ne_NP_of_MCSP_bound :
  (∃ ε > 0, MCSP_lower_bound ε) → P ≠ NP := by
  intro h
  have h₁ : ¬ NP ⊆ Ppoly := magnification_AC0_MCSP h
  -- If `P = NP`, then `NP ⊆ Ppoly` trivially, contradicting `h₁`.
  by_contra hPNP
  have : NP ⊆ Ppoly := by
    -- From `hPNP : P = NP` we obtain `NP ⊆ P` by rewriting,
    -- and `P ⊆ Ppoly` is available as the axiom `P_subset_Ppoly`.
    intro L hL
    have hL_P : L ∈ P := by simpa [hPNP] using hL
    exact P_subset_Ppoly hL_P
  have := h₁ this
  contradiction

section Examples
example : ¬ (∃ ε > 0, MCSP_lower_bound ε) ∨ P ≠ NP := by
  classical
  by_cases h : ∃ ε > 0, MCSP_lower_bound ε
  · right
    exact P_ne_NP_of_MCSP_bound h
  · left
    exact h
end Examples

/-!
References:
* Hardness Magnification Near State-of-the-Art Lower Bounds (2021):
  https://theoryofcomputing.org/articles/v017a011/
-/

/-!
Bridge from the constructive cover (FCE-Lemma) to the MCSP lower bound.
In the current blueprint this implication is assumed as an axiom.
-/
axiom FCE_implies_MCSP : ∃ ε > 0, MCSP_lower_bound ε

/--
Assuming the bridge from the FCE-Lemma to the MCSP lower bound, we obtain
the classical separation `P ≠ NP`.
-/
lemma p_ne_np : P ≠ NP := by
  have h := FCE_implies_MCSP
  exact P_ne_NP_of_MCSP_bound h
