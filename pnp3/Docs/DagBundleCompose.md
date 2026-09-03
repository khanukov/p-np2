# Fixed-width DAG-bundle composition (P1b-0)

**Classification: Infrastructure.**  The modules
`Complexity.DagBundleCompose` and `Complexity.DagGadgets` provide generic
Boolean DAG plumbing for later compilation work.  They do not reduce a pnp4
source obligation and are not P-vs-NP mainline progress.

## Contract

For `S : DagBundle mid out` and `B : DagBundle m mid`, `substBundle S B`
stores `B`'s predecessor graph once and then `S`'s graph once.  Its gate count
is exactly

```text
B.gates + S.gates
```

and its output domain remains `Fin out`; old intermediate outputs are not
appended.  Output `o` is exactly `substInputsWithBundle (S.asCircuit o) B`, so
evaluation is `S` output `o` applied to the vector of `B` outputs.

The zero-gate `identityBundle W` starts fixed-width iteration.  With `S`
placed over the preceding iterate, `iterateBundle S t` agrees with
`(S.evalFun^[t])` and has exactly `t * S.gates` gates.  Thus the staging rule is:
each stage owns its new upper graph once, while every output shares the single
predecessor graph already present in the bundle.

`Complexity.DagGadgets` supplies projection and constant bundles plus direct
NOT, AND, OR, and four-gate MUX circuits and singleton bundles.  The MUX has an
explicit eight-row truth table; two NOT-bundle iterations have a proved
double-negation regression.  P1b-2 adds `bigOrCircuit`, a direct linear
false-seeded disjunction of a list of circuits.  Its evaluation is exactly
`List.any`, and its gate count (including the empty list) is
`1 + sum (C.gates + 1)`.  Each listed circuit occurs once, each row adds one OR
gate, and the empty list retains the one false seed gate.  Map and
`List.finRange` evaluation forms support compile-time enumerations.

## Boundary and handoff

This generic DAG layer provides no `UniformTM` step bundle, polynomial-size
theorem, `PpolyDAG` bridge, or rebind of repository complexity classes.  The
P1b-2 semantic kernel consumes its iteration laws conditionally; P1b-3 must
still construct a concrete shared one-step bundle and prove its gate bound.
