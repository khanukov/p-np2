> **Status (2025-08-06)**: This document is part of an unfinished repository. Results and plans may rely on unproven axioms or placeholders.
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
4. **From non‑uniform to uniform.** The classical Karp–Lipton theorem states that if `NP ⊆ P/poly` then the polynomial hierarchy collapses to `Σ₂`.  Taking the contrapositive, the separation from step 3 implies `P ≠ NP` unless one accepts such a collapse.  In the Lean files we leave the Karp–Lipton step as another axiom:
   ```lean
   axiom karp_lipton : (NP ⊆ Ppoly) → PH_collapse
   ```

In summary, the combination of the FCE‑Lemma, the magnification axiom and the (contrapositive of) Karp–Lipton yields the concluding statement `P ≠ NP` inside this blueprint.
