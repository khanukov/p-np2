# Research Blocker: `FormulaHalfSizeBoundPartial`

Date: 2026-02-21
Status: Open research blocker (not engineering-complete)
Owner area: MCP-4 (`Magnification/LocalityProvider_Partial.lean`)

## 1. Exact target to prove

In code:

`FormulaHalfSizeBoundPartial : Prop`

```
∀ {p : GapPartialMCSPParams}
  (hFormula : PpolyFormula (gapPartialMCSP_Language p)),
  FormulaCircuit.size ((Classical.choose hFormula).family (partialInputLen p))
    ≤ Partial.tableLen p.n / 2
```

Interpretation:
- for every parameter pack `p`,
- for every strict non-uniform formula witness solving `gapPartialMCSP_Language p`,
- the extracted formula at length `N = partialInputLen p` must have size at most `2^n / 2`.

## 2. Why this matters in the pipeline

This bound is the current key input for building a `stable` restriction witness:

- `stableWitness_of_formula_halfSize`
- `formulaToGeneralLocalityData_of_halfSize`
- `hasDefaultStructuredLocalityProviderPartial_of_halfSize`

Then this feeds final wrappers in `Magnification/FinalResult.lean`:

- `NP_not_subset_PpolyFormula_final_of_halfSize`
- `P_ne_NP_final_of_halfSize`

Without this bound (or a stronger internal replacement), the MCP-4 chain remains conditional.

## 3. Why current internal lemmas are insufficient

Current `PpolyFormula` witness gives only:
- polynomial-size bound `size ≤ polyBound n`,
- with `polyBound n ≤ n^c + c` for some witness-specific `c`.

At target length `n = partialInputLen p = 2^(p.n+1)`, this yields:
- `size ≤ (2^(p.n+1))^c + c`,
- which does **not** imply `size ≤ 2^(p.n) = tableLen/2` in general.

So the desired half-table bound is not derivable by pure arithmetic from the current interface.

## 4. What would count as a valid closure

Any one of:

1. Prove the exact theorem above internally from stronger structural facts about formula realizers for `gapPartialMCSP_Language`.
2. Replace it by a stronger theorem that implies the same `stable` witness path (for example a direct constructive `stable` theorem for extracted solvers).
3. Refactor locality-lift requirements so half-table cardinality is replaced by a different internally provable criterion.

## 5. Minimal expected output of closure

After closure, the following should be constructible with no extra external hypothesis:

- `hasDefaultStructuredLocalityProviderPartial`

from internal lemmas only, and then final MCP-4 exports can avoid all half-size assumptions.

## 6. Risk classification

This is likely breakthrough-strength depending on the exact closure route.
Treat as research, not routine refactor.

Do not report MCP-4 as fully closed until this blocker is removed or replaced by an internally proved equivalent.

## 7. Candidate research routes (A/B/C)

### Route A: Direct half-size theorem for extracted formula witnesses

Goal shape:
- prove `FormulaHalfSizeBoundPartial` exactly as stated.

Expected theorem artifact:
- `theorem formula_half_size_bound_partial_internal :
    FormulaHalfSizeBoundPartial`

Why it closes MCP-4:
- instantly discharges `stableWitness_of_formula_halfSize`,
- yields `hasDefaultStructuredLocalityProviderPartial` via existing plumbing.

Primary risk:
- may be equivalent in strength to proving the required separation itself.

### Route B: Replace half-size premise with direct stable witness theorem

Goal shape:
- avoid cardinality-from-size;
- prove stability of `generalSolverOfFormula hFormula` directly by semantic/syntactic argument.

Expected theorem artifact:
- `theorem stableWitness_of_formula_internal
    {p} (hFormula : PpolyFormula (gapPartialMCSP_Language p)) :
    ∃ r, r.alive.card ≤ tableLen/2 ∧ stable(...)`

Integration action:
- replace uses of `stableWitness_of_formula_halfSize` and remove `FormulaHalfSizeBoundPartial` from active route.

Primary risk:
- still requires proving a strong locality statement for arbitrary extracted witnesses.

### Route C: Locality-lift criterion refactor (remove `tableLen/2` dependency)

Goal shape:
- redesign the locality-lift interface to consume an alternative invariant that is provable internally.

Expected theorem artifacts:
1. New lift theorem with alternate premise:
   `locality_lift_partial_alt : ...`
2. Internal theorem supplying that premise from extracted formula witness.

Integration action:
- migrate `ConstructiveLocalityEnginePartial.stable` contract to new premise.

Primary risk:
- broad refactor footprint; must preserve compatibility with downstream LB/magnification lemmas.

## 8. Route selection criteria

Pick Route A if:
- there is a concrete counting/shrinkage argument already known to imply exact half-size bound.

Pick Route B if:
- a direct restriction-stability proof is available without full numeric half-size theorem.

Pick Route C if:
- team can prove a different structural invariant, but not half-size cardinality.

## 9. Immediate theorem-level deliverables for scientists

Minimum useful milestone set:

1. One internal theorem candidate with precise statement (A or B or C).
2. One compatibility lemma showing how it plugs into
   `structuredLocalityProviderPartial_of_engine`.
3. One end-to-end compile witness:
   build `hasDefaultStructuredLocalityProviderPartial` without any half-size assumption parameter.
