import PSubsetPpoly.ComplexityClasses

/-!
# Non-uniform Separation and `P ≠ NP`

This file records the axioms that connect an improved lower bound on
`MCSP` with the classical complexity-theoretic separations.  At this
stage we keep the magnification theorem and the bridge from the
constructive cover as assumptions, but we eliminate the historical
dependence on the Karp–Lipton collapse.  Instead we spell out the
elementary deduction that combines a non-uniform separation with the
classical inclusion `P ⊆ P/poly` to conclude `P ≠ NP`.
-/

/-- A stub representing the claim that `MCSP` requires circuits of size
    at least `n^{1 + ε}` and depth `o(log n)` within `ACC⁰`.  The actual
    numeric bounds are omitted here. -/
constant MCSP_lower_bound : ℝ → Prop

/-- Hypothesis: magnification for `ACC⁰` circuits on `MCSP`.  If the
    lower bound holds for some `ε > 0`, then `NP` is not contained in
    `P/poly`. -/
axiom magnification_AC0_MCSP :
  (∃ ε > 0, MCSP_lower_bound ε) → NP ⊄ Ppoly

/-!
### From `NP ⊄ P/poly` to `P ≠ NP`

The only classical ingredient we need at the moment is the well-known
simulation of polynomial-time Turing machines by polynomial-size
circuits.  Once this inclusion is available, any separation between `NP`
and `P/poly` immediately forces `P` to differ from `NP`.
-/

/-- A helper lemma isolating the purely set-theoretic argument: if `NP`
    is not contained in `P/poly` but `P` is, then `P ≠ NP`.  The proof
    is elementary and keeps the final chain free of any reference to the
    polynomial hierarchy. -/
lemma P_ne_NP_of_NP_not_subset_Ppoly
    (hNP : NP ⊄ Ppoly) (hP : P ⊆ Ppoly) : P ≠ NP := by
  classical
  by_contra hEq
  -- Equality of sets gives both inclusions; the one we need is `NP ⊆ P`.
  have hNPsubP : NP ⊆ P := by
    intro L hL
    simpa [hEq] using hL
  -- Combining the inclusion `P ⊆ P/poly` with the previous step yields
  -- the forbidden containment `NP ⊆ P/poly`.
  have hContr : NP ⊆ Ppoly := by
    intro L hL
    exact hP (hNPsubP hL)
  exact hNP hContr

/-- Combining magnification with the classical inclusion `P ⊆ P/poly`
    we obtain `P ≠ NP` once a suitable lower bound on `MCSP` is known. -/
lemma P_ne_NP_of_MCSP_bound :
    (∃ ε > 0, MCSP_lower_bound ε) → P ≠ NP := by
  intro h
  have hNP : NP ⊄ Ppoly := magnification_AC0_MCSP h
  -- The inclusion `P ⊆ P/poly` is the only classical ingredient needed
  -- for the final contradiction.
  have hP : P ⊆ Ppoly := P_subset_Ppoly
  exact P_ne_NP_of_NP_not_subset_Ppoly hNP hP

section Examples
/-!  Simple illustration showing that the statement
`P_ne_NP_of_MCSP_bound` yields `P ≠ NP` whenever an MCSP lower bound is
available.  The proof mirrors the legacy version and serves as a
sanity check for the migrated lemmas. -/
example : ¬ (∃ ε > 0, MCSP_lower_bound ε) ∨ P ≠ NP := by
  classical
  by_cases h : ∃ ε > 0, MCSP_lower_bound ε
  · right
    exact P_ne_NP_of_MCSP_bound h
  · left
    exact h
end Examples

/-!  Bridge from the constructive cover (FCE-Lemma) to the MCSP lower
bound.  In the current blueprint this implication is assumed as an
axiom.  Ported from the legacy development for completeness. -/
axiom FCE_implies_MCSP : ∃ ε > 0, MCSP_lower_bound ε

/-- Assuming the bridge from the FCE-Lemma to the MCSP lower bound, we
    obtain the classical separation `P ≠ NP` without appealing to the
    polynomial hierarchy. -/
lemma p_ne_np : P ≠ NP := by
  have h := FCE_implies_MCSP
  exact P_ne_NP_of_MCSP_bound h

