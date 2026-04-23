# Simulation Fine-Grained Status

Updated: 2026-04-23.

This file records the complexity-leakage audit boundary for
`pnp3/Complexity/Simulation`.

## Current Claim

The active simulation endpoint is:

```text
proved_P_subset_PpolyDAG_internal : P_subset_PpolyDAG
```

It is a coarse non-uniform inclusion theorem.  It proves that every `P`
language has some polynomial-size DAG family.

The size contract in `Circuit_Compiler.lean` is:

```text
CompiledRuntimeCircuitSizeBoundLinear :
  ... -> exists k, forall n, size <= n^k + k
```

`Linear` names the linear-step builder route.  It is not an `O(n)` or
fine-grained compiler bound.

## Why This Is Enough For The Current Final Route

The public final route is:

```text
ResearchGapWitness -> P_ne_NP_final
```

`ResearchGapWitness` contains `NP_not_subset_PpolyDAG`, which separates against
every polynomial-size DAG family.  The inclusion side only needs the coarse
`P_subset_PpolyDAG` theorem.

Therefore loose simulation overhead does not consume counting slack in the
current honest final path.

## What Is Not Claimed

This module does not prove a fine-grained Cook-Levin or hardness-magnification
adequacy theorem.  It does not establish bounds such as `O(T log T)`,
`O(T polylog T)`, or any small explicit exponent suitable for magnification
inequalities.

## Future Requirement

Any future route whose source theorem depends on exact MCSP thresholds, Shannon
slack, or hardness-magnification constants must include a separate
fine-grained simulation adequacy proof.  That proof must expose the concrete
compiler overhead and show it fits the route's numeric inequalities before it
is wired to `ResearchGapWitness`.
