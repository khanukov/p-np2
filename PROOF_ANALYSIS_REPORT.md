# Analysis of Proof Chain "Shrinkage from Good"

This document summarizes the findings from the review of the "Shrinkage from Good" proof chain in `pnp3/AC0/MultiSwitching/ShrinkageFromGood.lean` and `pnp3/AC0/MultiSwitching/Main.lean`.

## Logical Disconnect in Stage 4 (Shrinkage)

The chain of proof consists of several steps:
1.  **Stage 1 (Encoding/Injection)**: Proves that "bad" restrictions (which leave long canonical traces) can be encoded injectively into a smaller set.
2.  **Stage 2 (Counting)**: Uses counting arguments to show that the set of "bad" restrictions is small relative to the set of all restrictions.
3.  **Stage 3 (Existence)**: Concludes that a "Good" restriction $\rho$ exists (one for which `not BadEvent` holds).
4.  **Stage 4 (Shrinkage)**: Claims to construct a `Shrinkage` witness from this "Good" restriction.

The review reveals a critical **logical disconnect** at Stage 4.

### The False Fact: Vacuous Shrinkage Witness

The theorem `shrinkage_from_good_restriction` in `pnp3/AC0/MultiSwitching/ShrinkageFromGood.lean` (and subsequently `stage1_4_complete` in `Main.lean`) claims to provide a shrinkage witness:

```lean
theorem shrinkage_from_good_restriction
    {n k t : Nat} (F : FormulaFamily n k)
    (ρ : Restriction n) (hgood : GoodFamilyCNF (F := F) t ρ) :
    ∃ (S : Shrinkage n),
      S.F = evalFamily F ∧ S.t = (allPointSubcubes n).length ∧
        S.ε = (1 : Q) / (n + 2)
```

However, the implementation ignores the `hgood` hypothesis entirely:

```lean
  -- В этой версии `hgood` не используется: точечные selectors корректны всегда.
  have _ := hgood
  simpa using (shrinkage_from_restriction (F := F) (ρ := ρ))
```

Instead of constructing a decision tree with small depth (implied by the `Good` property via `TraceBridge`), it constructs a trivial decision tree using `allPointSubcubes`. This tree simply lists every satisfying assignment of the function.

**Consequence:**
The depth bound `S.t` is set to `(allPointSubcubes n).length`, which can be up to $2^n$ (exponential in $n$).

For the intended application (proving circuit lower bounds for AC0), the shrinkage step must reduce the complexity of the function significantly (typically to depth polynomial in $\log s$ or $n^\epsilon$). An exponential bound makes the result **vacuous** for proving $P \ne NP$.

### Broken Chain

While the codebase contains correct components for proving the existence of a good restriction (`Counting.lean`) and relating restrictions to decision tree depth (`TraceBridge.lean`), these components are **not used** to construct the final shrinkage witness. The proof chain is effectively broken:

*   `TraceBridge` proves: `not BadCNF -> depth(canonicalDT) < t`.
*   `Counting` proves: `exists rho, not BadCNF`.
*   `ShrinkageFromGood` ignores both and returns a tree of depth $\approx 2^n$.

### Counter-Example

Any boolean function requiring a non-trivial lower bound (e.g., Parity) serves as a counter-example to the *utility* of this proof. The current proof technically holds (an exponential-size decision tree always exists), but it fails to demonstrate the required shrinkage property. Specifically, if one attempts to use `stage1_4_complete` to prove that Parity requires super-polynomial size depth-3 circuits, the resulting bound from this shrinkage step will be useless (exponential), failing to separate complexity classes.
