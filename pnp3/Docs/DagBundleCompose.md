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
double-negation regression.  No finite/list big OR is included because P1b-0
does not yet require a stable downstream statement for it.

## Boundary and handoff

This slice provides no `UniformTM` configuration, step, or run construction;
no polynomial-size theorem; no `PpolyDAG` bridge; and no rebind of repository
complexity classes.  P1b-1 can consume `substBundle`, `identityBundle`, and the
gadgets to compile one fixed-width transition layer.  It must preserve the
same sharing rule and separately prove any width and polynomial bounds its
application needs.
