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

`reindexOutputs B f` selects, permutes, or duplicates output wires while
preserving exactly the same gate function and gate count. P1b-3 uses it to
hide internal scan/row rails without copying their graph.

`Complexity.DagGadgets` supplies projection and constant bundles plus direct
NOT, AND, OR, and four-gate MUX circuits and singleton bundles.  The MUX has an
explicit eight-row truth table; two NOT-bundle iterations have a proved
double-negation regression.  P1b-2 adds `bigOrCircuit`, a direct linear
false-seeded disjunction of a list of circuits.  Its evaluation is exactly
`List.any`, its gate count is `1 + sum (C.gates + 1)`, and its exact
`DagCircuit.size` is `2 + sum C.size`.  Thus the empty list has one false seed
gate and size two, including its output; each listed circuit occurs once and
each row adds one OR gate.  Map and `List.finRange` evaluation forms support
compile-time enumerations.

## Boundary and handoff

This generic DAG layer alone provides no polynomial-size run-family theorem,
`PpolyDAG` bridge, or rebind of repository complexity classes. P1b-3 separately
uses it to construct a concrete shared one-step bundle and gate bound.
