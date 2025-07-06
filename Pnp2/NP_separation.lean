import Pnp2.ComplexityClasses

/-!
# Non-uniform Separation and `P ≠ NP`

This file records the axioms that connect an improved lower bound on
`MCSP` with the classical complexity-theoretic separations.  We do not
prove the magnification theorem or the Karp–Lipton collapse; instead we
introduce them as assumptions so that later developments can depend on
their statements.
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

/-- Hypothesis: the Karp–Lipton theorem stated in contrapositive form.
    If `NP` were contained in `P/poly`, then the polynomial hierarchy
    would collapse.  We leave the exact collapse statement abstract. -/
constant PH_collapse : Prop
axiom karp_lipton : (NP ⊆ Ppoly) → PH_collapse

/-- Combining magnification and the contrapositive of Karp–Lipton we
    obtain `P ≠ NP` once a suitable lower bound on `MCSP` is known. -/
lemma P_ne_NP_of_MCSP_bound :
    (∃ ε > 0, MCSP_lower_bound ε) → P ≠ NP := by
  intro h
  have h₁ : NP ⊄ Ppoly := magnification_AC0_MCSP h
  -- If `P = NP`, then `NP ⊆ Ppoly` trivially, contradicting `h₁`.
  by_contra hPNP
  have : NP ⊆ Ppoly := by
    intro L hL
    have hP : L ∈ P := by simpa using congrArg SetLike.mem hPNP ▸ hL
    exact ⟨⟨fun _ => 0, ⟨0, by trivial⟩, fun _ => Classical.choice (Classical.decEq _),
      by trivial, by trivial⟩, trivial⟩
  have := h₁ this
  contradiction

