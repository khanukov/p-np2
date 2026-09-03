# Uniform P V1 foundation (P1a)

**Status:** P1a infrastructure model, repaired on 2026-09-03. This status does
not assert completion of any later milestone.

The versioned namespace is:

```text
Pnp3.Complexity.Uniform.V1
```

The P1a model modules are `Complexity/Uniform/V1/Machine.lean`,
`PolynomialTime.lean`, and `Examples.lean`. They use local definitionally equal
aliases

```lean
Bitstring n := Fin n → Bool
Language := ∀ n, Bitstring n → Bool
```

and do not import the frozen `Complexity/TMVerifier` tree or the legacy
`PsubsetPpolyInternal/TuringEncoding`, `Complexity/Interfaces`, or
`Complexity/Simulation` layers. The later P1b `CircuitEncoding.lean` module
intentionally reaches the canonical `ComplexityInterfaces.DagCircuit` API
through `DagGadgets` and `DagBundleCompose`; it still imports neither the
legacy Turing-machine/simulator layers nor the frozen tree.

## Finite machine ABI

`UniformTM` contains exactly finite control and a raw transition table:

```lean
stateCount : Nat
start accept reject : Fin stateCount
accept_ne_reject : accept ≠ reject
rawStep : Fin stateCount → Option Bool →
  Fin stateCount × Option Bool × Move
```

It has no input-length function, clock, advice, runtime, or correctness field.
The tape alphabet distinguishes `some false`, `some true`, and the blank
`none`. The public executable `UniformTM.step` overrides both terminal rows:
accept and reject preserve the exact scanned symbol and stay put. Thus raw
terminal rows are not observable.

For an `n`-bit input and budget `budget`, `Config k n budget` uses the finite
tape length `n + budget + 1`.  A run changes only elapsed steps; its input and
budget indices remain fixed.  Left and right moves clamp at the tape
boundaries. `initialConfig` stores `some (x i)` exactly below `n` and `none`
from `n` onward, so a machine can observe the input boundary. P1a deliberately
provides no cross-budget transport theorem: such a result would require honest
dependent `Fin` transport between different tape types.

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
the deadline is neither acceptance nor rejection and decides neither true nor
false. Exact-deadline and within-budget decision semantics are equivalent at
the same budget.

Exact-time execution remains a total operation when `steps > budget`; the head
simply obeys the same finite-tape boundary clamps. This total clamped behavior
is not used to witness `UniformP`, whose semantics requires a verdict within
the clock budget.

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
A fixed four-state scanner also decides `lengthParityLanguage`: it toggles a
finite parity state across each `some` input symbol and branches on the first
`none` after exactly `n + 1 = polyClock 1 n` steps. Its arbitrary-length proof,
plus executable empty/one-/two-bit pins, is the regression that length is
observable and false input bits are not padding. These four languages are in
this versioned `UniformP`.

A separate literal remains in a nonterminal state forever; its acceptance
equality test is false, but it neither accepts nor rejects and decides neither
Boolean answer. This is the regression pin separating timeout from rejection.

`Tests/UniformV1SurfaceTests.lean` pins the constructor shape, definitions,
instances, and every authored public theorem's full proposition. All theorem
`#print axioms` roots live in the central `Tests/AxiomsAudit.lean`; private proof
helpers are excluded from both public surfaces.

## Honest boundary and P1b work

P1b-1 adds direct fixed-width encoding infrastructure in the nested namespace
`Pnp3.Complexity.Uniform.V1.Circuit`.  For tape length `T = n + budget + 1`,
its width is `M.stateCount + 3*T`, ordered as state, head, tape-presence, then
tape-value.  The two tape rails canonically encode blank as `(false,false)`,
`some false` as `(true,false)`, and `some true` as `(true,true)`; the exact
bundle specification therefore excludes malformed `(false,true)` outputs.

`initialBundle M n budget` is a direct shared `DagBundle` depending only on
those three parameters.  It uses exactly two shared constant gates, routes
input values by zero-gate projections, and has exact single-output circuit size
three.  Its specification is the exact encoding of `initialConfig`; the
length-one regression distinguishes a present false bit in cell zero from the
blank padding cell one.  `Tests/UniformV1CircuitEncodingSurfaceTests.lean` pins
this API, with direct theorem and wrapper roots in the central axiom audit.

This P1b-1 slice is infrastructure, not P-vs-NP mainline progress.  It provides
no transition/step compiler, run compiler, polynomial-size simulation theorem,
`UniformP`/`PpolyDAG` bridge, canonical class rebind, or lower bound.  P1b-2
must separately compile one transition over this fixed layout and prove its
exact semantics and size accounting before any repeated-run construction.

This P1a repair is infrastructure. It does not change the repository's canonical
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
