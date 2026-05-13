# V2-A rewrite attack landed (gpt55)

## Result

ATTACK_LANDED.

The semantic-rewrite attack lands against V2-A/gpt55 for the Nat.log2
prefix-AND hardwiring witness.

Exact Lean reference:

- `pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_A_gpt55/AdversarialRobustness/RewriteAttack.lean::Pnp3.Magnification.AuditRoutes.ProvenanceFilterV2.V2_A_gpt55.AdversarialRobustness.v2A_rewrite_attack_prefixAnd`

## What was constructed

The file defines `rewritePrefixAndFamily`, which leaves the zero-length case
unchanged and, for positive input lengths, replaces the excluded family
`adversaryFamily_v_natlog2 n` by

```lean
FormulaCircuit.and (adversaryFamily_v_natlog2 n) (seedGate n h)
```

where `seedGate n h` is the tautology `(x₀ ∨ ¬x₀)` already used by the V2-A
non-vacuity surface.

The packaged witness is
`rewritePrefixAndWitness : InPpolyFormula rewritePrefixAndLanguage`, with
`rewritePrefixAndLanguage` definitionally equal to `adversaryLanguage_v_natlog2`.

## Why this breaks V2-A

The seed is semantically redundant, so the rewritten family computes exactly the
same language as the excluded prefix-AND adversary.  However, syntactically it
adds one OR gate and one NOT gate, plus constant-size overhead.  The support
remains at least the original log-width support, the Boolean-gate count stays
linear in that support, and the depth stays within the V2-A linear depth cap.

Kernel-checked theorem:

```lean
theorem v2A_rewrite_attack_prefixAnd :
    ∃ (L : Language) (w_rewritten : InPpolyFormula L),
      L = adversaryLanguage_v_natlog2 ∧
      ProvenanceFilter_v2_V2_A_gpt55_Filter w_rewritten
```

## Scope notes

Per the seed-pack instructions, this report does not edit `known_guards`, does
not mark V2-A dead in spec, and does not add any accepted promotion, FP-4,
`SourceTheorem`, `gap_from`, final endpoint, or candidate package.

The secondary arbitrary-payload target was not needed to establish this major
attack result; the landed primary theorem is already a hardwiring-shaped witness
that computes the same language as an excluded witness while satisfying V2-A.
