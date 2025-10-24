> **Status (2025-09-24)**: Updated after removing the `P_subset_Ppoly` axiom; only the magnification bridge remains axiomatic in `Pnp2/NP_separation.lean`.
>
# NP \nsubseteq P/poly via magnification

This short note records the assumptions and final logical steps used in the repository to obtain the non-uniform separation `NP \nsubseteq P/poly` and the consequence `P ≠ NP`.

1. **Lower bound premise.** Suppose there exists some ε > 0 such that `MCSP` requires circuits of size at least `n^{1+ε}` and depth `o(log n)` in `ACC⁰`.
   This is the quantitative improvement suggested by the FCE‑Lemma.
2. **Magnification theorem.** Following Oliveira–Pich (2019) one assumes a magnification property for `MCSP` against `ACC⁰` circuits.  Formally we state it as an axiom in Lean:
   ```lean
   axiom magnification_AC0_MCSP :
     (∃ ε > 0, MCSP_lower_bound ε) → NP ⊄ Ppoly
   ```
   Here `MCSP_lower_bound ε` abbreviates the depth and size restriction from step 1 and `Ppoly` denotes `P/poly`.
3. **Applying the axiom.** Once the FCE‑Lemma yields the existence of such an `ε`, the axiom implies `NP ⊄ P/poly`.
4. **From non‑uniform to uniform.** Combining the separation from step 3 with the constructive inclusion `P ⊆ P/poly` yields `P ≠ NP`.  The Lean code now contains a direct lemma
   ```lean
   lemma P_ne_NP_of_NP_not_subset_Ppoly
       (hNP : NP ⊄ Ppoly) (hP : P ⊆ Ppoly) : P ≠ NP
   ```
   so the only missing ingredients are the magnification theorem and the bridge `FCE_implies_MCSP`.  The files `TM/Encoding.lean`, `Circuit/Family.lean`, and `PsubsetPpoly.lean` now supply the constructive proof of `P ⊆ P/poly` used here.

In summary, the combination of the FCE‑Lemma, the magnification axiom and the classical inclusion `P ⊆ P/poly` yields the concluding statement `P ≠ NP` inside this blueprint, without appealing to any collapse of the polynomial hierarchy.
