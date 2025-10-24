import Complexity.ComplexityClasses

/-!
# Non-uniform Separation and P ≠ NP

This file contains the **purely logical** argument that derives P ≠ NP from
a non-uniform separation NP ⊄ P/poly combined with the classical inclusion P ⊆ P/poly.

## Key Theorem

```lean
theorem P_ne_NP_of_nonuniform_separation :
  NP ⊄ Ppoly → P ⊆ Ppoly → P ≠ NP
```

This is **pure logic** (14 lines), no complexity theory needed!

## Proof Idea

By contradiction:
1. Assume P = NP
2. Then NP ⊆ P (from equality)
3. We have P ⊆ P/poly (given)
4. So NP ⊆ P/poly (transitivity)
5. But this contradicts NP ⊄ P/poly (given)
6. Therefore P ≠ NP

This elementary argument eliminates any need for the polynomial hierarchy
or Karp-Lipton collapse theorems.

## References

- This proof is taken from Pnp2/NP_separation.lean:39-52
- Original source: classical complexity theory folklore
- Formalized independently from Håstad, Williams, OPS, CJW results
-/


namespace Pnp3
namespace Complexity

open Classical

/-! ## Main Theorem

This is the **key logical step** in the P≠NP proof strategy.

Given:
- NP ⊄ P/poly (from GapMCSP hardness + magnification)
- P ⊆ P/poly (classical inclusion)

Conclude: P ≠ NP

**This theorem has NO axioms** - it's pure logic!
-/

/-- **Main Theorem**: Non-uniform separation implies uniform separation.

    If NP is not contained in P/poly, but P is, then P ≠ NP.

    This is an elementary set-theoretic argument that requires no
    deep complexity theory.

    **Proof**: By contradiction. If P = NP, then:
    - NP ⊆ P (from equality)
    - P ⊆ P/poly (given)
    - So NP ⊆ P/poly (transitivity)
    - Contradiction with NP ⊄ P/poly (given)

    **Previously an axiom in Interfaces.lean**, now proven!
-/
theorem P_ne_NP_of_nonuniform_separation
    (hNP : NP ⊄ Ppoly) (hP : P ⊆ Ppoly) : P ≠ NP := by
  -- Proof by contradiction
  by_contra hEq
  -- If P = NP, then NP ⊆ P
  have hNPsubP : NP ⊆ P := by
    intro L hL
    -- L ∈ NP, P = NP, so L ∈ P
    simpa [hEq] using hL
  -- Combining P ⊆ P/poly with NP ⊆ P gives NP ⊆ P/poly
  have hContr : NP ⊆ Ppoly := by
    intro L hL
    -- L ∈ NP ⟹ L ∈ P ⟹ L ∈ P/poly
    exact hP (hNPsubP hL)
  -- But this contradicts NP ⊄ P/poly
  exact hNP hContr

/-! ## Sanity Checks

These examples verify that our logic is sound.
-/

/-- Example: Either we don't have NP ⊄ P/poly, or we have P ≠ NP.

    This tautology confirms the theorem structure is correct. -/
example (hP : P ⊆ Ppoly) : ¬(NP ⊄ Ppoly) ∨ P ≠ NP := by
  by_cases h : NP ⊄ Ppoly
  · right
    exact P_ne_NP_of_nonuniform_separation h hP
  · left
    exact h

/-- The theorem is contrapositive to: P = NP ∧ P ⊆ P/poly → NP ⊆ P/poly -/
example (hP : P ⊆ Ppoly) : P = NP → NP ⊆ Ppoly := by
  intro hEq
  -- If the separation holds, we get P ≠ NP
  by_contra hNP
  -- So P = NP is false
  have := P_ne_NP_of_nonuniform_separation hNP hP
  exact this hEq

/-! ## Integration with the Full Proof

The full P≠NP proof (when all axioms are eliminated) will have this structure:

```lean
theorem P_ne_NP : P ≠ NP := by
  -- Step 1: GapMCSP is hard for AC⁰ (Part C: Anti-Checker)
  have gap_hard : AC0_cannot_solve_GapMCSP := ...

  -- Step 2: Magnification (Part D)
  have np_sep : NP ⊄ Ppoly := magnification gap_hard

  -- Step 3: Classical inclusion (currently axiom, can be proven)
  have p_in : P ⊆ Ppoly := P_subset_Ppoly

  -- Step 4: Logical conclusion (THIS THEOREM - NO AXIOM!)
  exact P_ne_NP_of_nonuniform_separation np_sep p_in
```

Currently Steps 1-3 have axioms, but Step 4 is **axiom-free**!
-/

end Complexity
end Pnp3
