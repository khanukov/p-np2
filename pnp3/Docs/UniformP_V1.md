# Uniform P V1 foundation (P1a)

**Status:** P1a infrastructure landed on 2026-09-03.

The versioned namespace is:

```text
Pnp3.Complexity.Uniform.V1
```

Its source modules are `Complexity/Uniform/V1/Machine.lean`,
`PolynomialTime.lean`, and `Examples.lean`.  They use local definitionally
equal aliases

```lean
Bitstring n := Fin n → Bool
Language := ∀ n, Bitstring n → Bool
```

and do not import the frozen `Complexity/TMVerifier` tree or the legacy
`PsubsetPpolyInternal/TuringEncoding`, `Complexity/Interfaces`, or
`Complexity/Simulation` layers.

## Finite machine ABI

`UniformTM` contains exactly finite control and a raw transition table:

```lean
stateCount : Nat
start accept reject : Fin stateCount
accept_ne_reject : accept ≠ reject
rawStep : Fin stateCount → Bool → Fin stateCount × Bool × Move
```

It has no input-length function, clock, advice, runtime, or correctness field.
The public executable `UniformTM.step` overrides both terminal rows: accept and
reject preserve the scanned bit and stay put.  Thus raw terminal rows are not
observable.

For an `n`-bit input and budget `budget`, `Config k n budget` uses the finite
tape length `n + budget + 1`.  A run changes only elapsed steps; its input and
budget indices remain fixed.  Left and right moves clamp at the tape
boundaries.  P1a deliberately provides no cross-budget transport theorem.

## Verdict semantics

`AcceptsAt` and `RejectsAt` are exact-time predicates on the same
budget-indexed tape.  `AcceptsWithin` and `RejectsWithin` existentially choose
an elapsed time no greater than that budget.  Full-configuration terminal
absorption plus `UniformTM.run_add` proves:

```text
AcceptsAt M budget budget x ↔ AcceptsWithin M budget x
RejectsAt M budget budget x ↔ RejectsWithin M budget x
```

Acceptance and rejection cannot both hold, even when their within-budget
witness times differ.

`DecidesAt` and `DecidesWithin` branch on the requested Boolean answer.  True
requires acceptance; false requires literal rejection.  A nonterminal state at
the deadline is neither a false decision nor rejection.  Exact-deadline and
within-budget decision semantics are equivalent.

The clock is pinned to `polyClock c n = n ^ c + c`, including its exponent-zero,
zero-input, exponent-one, and positivity behavior.  The class predicate is:

```lean
UniformP L := ∃ M c, ∀ n x, DecidesWithin M (polyClock c n) x (L n x)
```

The same single `M` and `c` serve every input length.  The theorem
`uniformP_iff_exists_decidesAt` is the exact-deadline P1b handoff.  A finite
accept/reject label swap also proves `uniformP_complement`; the false branch is
not weakened to nonacceptance.

## Executable sanity surface

Closed literal machines prove the expected exact and within-budget behavior
for constant true, constant false, and the first bit (with empty input false).
All three languages are in this versioned `UniformP`.  The surface also checks
input padding and concrete true/false verdicts.  A separate literal remains in
a nonterminal state forever; its acceptance equality test is false, but it
neither rejects nor decides false.  This is the regression pin separating
timeout from rejection.

`Tests/UniformV1SurfaceTests.lean` pins the constructor shape, all definitions
and instances, every authored public theorem's full proposition, and direct
`#print axioms` output.

## Honest boundary and P1b work

This landing is infrastructure.  It does not change the repository's canonical
`P` or `NP` definitions and is not P-vs-NP mainline progress.  In particular,
P1a proves none of the following:

- countability or an encoding of `UniformTM`;
- a bridge to any legacy machine or language interface;
- `UniformP ⊆ PpolyDAG`;
- a canonical `P` rebind;
- `UniformNP` or any circuit lower bound.

Accordingly, the old runtime-advice languages are not yet proved excluded from
the canonical classes.  P1b can consume the exact-deadline equivalence while
adding separately audited encoding/simulation bridges; it must not infer those
bridges from P1a.
