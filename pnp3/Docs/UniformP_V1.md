# Uniform P V1 foundation and circuit simulation

**Status:** P1a uniform model, P1b `UniformP ⊆ PpolyDAG` simulation, and P1c
countability/direct no-length-advice diagonal completed on 2026-09-03.
Canonical `P` remains legacy and unchanged.

The versioned namespace is:

```text
Pnp3.Complexity.Uniform.V1
```

The P1a model modules are `Complexity/Uniform/V1/Machine.lean`,
`PolynomialTime.lean`, and `Examples.lean`; P1c is the separate narrow module
`Countability.lean`. They use local definitionally equal aliases

```lean
Bitstring n := Fin n → Bool
Language := ∀ n, Bitstring n → Bool
```

and do not import the frozen `Complexity/TMVerifier` tree or the legacy
`PsubsetPpolyInternal/TuringEncoding`, `Complexity/Interfaces`, or
`Complexity/Simulation` layers. The later P1b `CircuitEncoding.lean` module
reaches the canonical `Complexity/Interfaces` module through `DagGadgets` and
the DAG composition layers.  That canonical interface has a transitive import
path to the legacy `PsubsetPpolyInternal/TuringEncoding`, so the inherited P1b
import cone does contain the legacy TM interface.  The P1b-1 construction and
proofs do not use that legacy TM, its `runTime`, the legacy simulator/compiler,
or the frozen `TMVerifier` semantics.

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
`#print axioms` roots live in the central `Tests/AxiomsAudit.lean`; private
proof helpers are excluded from both public surfaces.

## P1c countability and direct no-length-advice diagonal

`Countability.lean` injects `Move` into `Nat` and injects every `UniformTM`
into the explicit proof-erasing dependent code

```text
Σ k : Nat, Fin k × Fin k × Fin k ×
  (Fin k → Option Bool → Fin k × Option Bool × Move)
```

in the pinned order start, accept, reject, transition table.  The injection
reconstructs the dependent record fields and uses proof irrelevance only for
the erased `accept_ne_reject` field; it does not use retroactive deriving.
Finite-domain function and sigma countability then give `Countable UniformTM`
and `Countable (UniformTM × Nat)`.

`machineLanguage M c` is the total exact-deadline acceptance flag, mapping a
timeout to false.  No timeout is used as a false decision: for every genuine
`DecidesAt` witness, `machineLanguage_eq_of_decidesAt` proves the arbitrary
Boolean answer, with the false case using literal `RejectsAt` and terminal
state disjointness.  Exact-deadline equivalence and function extensionality
therefore put every versioned `UniformP` language in the range of
`(UniformTM × Nat) → Language`, proving `uniformP_languages_countable`.

Finally, `lengthOnly A n x = A n` is injective by evaluating at the canonical
all-false input, including `Fin 0`.  Given a countable set covered by
`f : Nat → Language`, the direct witness

```text
A i = !(f i i (fun _ => false))
```

differs from its covering entry at index `i`.  This proves
`exists_lengthOnly_not_uniformP` without a cardinal or uncountability
abstraction. `Tests/UniformV1CountabilitySurfaceTests.lean` pins every public
definition, theorem, and countability instance, with direct and wrapper axiom
roots in the central audit.

## Honest boundary and P1b work

P1b-1 adds direct fixed-width encoding infrastructure in the nested namespace
`Pnp3.Complexity.Uniform.V1.Circuit`.  For tape length `T = n + budget + 1`,
its width is `M.stateCount + 3*T`, ordered as state, head, tape-presence, then
tape-value.  The layout theorems prove within-block injectivity, pairwise
disjointness, and exhaustive coverage of every configuration index by those
four blocks.  The two tape rails canonically encode blank as `(false,false)`,
`some false` as `(true,false)`, and `some true` as `(true,true)`; the exact
bundle specification therefore excludes malformed `(false,true)` outputs.

`initialBundle M n budget` is a direct shared `DagBundle` depending only on
those three parameters.  It uses exactly two shared constant gates, routes
input values by zero-gate projections, and has exact single-output circuit size
three.  Its specification is the exact encoding of `initialConfig`; the
length-one regression distinguishes a present false bit in cell zero from the
blank padding cell one.  `Tests/UniformV1CircuitEncodingSurfaceTests.lean` pins
this API, with direct theorem and wrapper roots in the central axiom audit.

P1b-2 adds `Complexity.Uniform.V1.StepKernel`.  Its `encodedStep` is a pure
Boolean function, exact only on canonical `encodeConfig` inputs.  It scans the
one-hot old head, matches the canonical blank/false/true rails, selects one
public `M.step` row, and derives next state and clamped next head, plus write
rails and the old-head tape update from that same action. Its headline
theorem is

```text
encodedStep M n budget (encodeConfig M c) = encodeConfig M (M.stepConfig c)
```

and `Nat.iterate` agrees with `M.run`.  The general head theorem uses the real
`moveHead`, so it covers both boundary clamps.  A theorem-derived
blank-write/left-clamp capstone additionally exercises a symbol-changing write
and the left clamp together.

The module also defines `StepSpec S`. P1b-3 now supplies the direct witness
`stepBundle M n budget`, built from one shared scan/action predecessor and a
single update substitution. Its exact gate count is `19*T + 10*Q + 12` plus
the numbers of public transition rows that write present/value, and hence is
at most `19*T + 16*Q + 13`. The standalone `actionBundle` has exact all-vector
semantics (including malformed inputs) and is bounded by `4*T + 16*Q + 12`.
The state/symbol action filters inspect only the fixed public `M.step` table;
no runtime, clock, language, or proof data enters either construction.
The corresponding single-output `DagCircuit.size` is the shared bundle gate
count plus one; that output-wire accounting is not folded into these formulas.
The supporting false-seeded `bigOrCircuit` has exact size
`2 + sum C.size`, including size two for the empty list.
The first-bit, length-parity, and blank-write/left-clamp capstones are derived
from the general semantic theorem rather than independent computation.
The direct-bundle regressions additionally cover blank-versus-false dispatch,
both accept and reject fixed points despite malicious raw terminal rows, and a
moving write that changes only the old-head cell.

Final P1b adds `Complexity.Uniform.V1.PpolyDAG`.  For fixed `M`, `c`, and `n`,
it iterates the direct `stepBundle` exactly `polyClock c n` times over the
two-gate initial bundle and selects the literal accept-state rail.  The circuit
has exact size

```text
3 + polyClock c n * (stepBundle M n (polyClock c n)).gates
```

and is bounded at every input length by `n^d + d`, with the explicit exponent
`d = 3 + (c+1)*(19*c + 16*M.stateCount + 70)`.  The proof handles `n=0` and
`n=1` separately (including the `c=0`, `0^0=1` clock corner) before the
`n>=2` power argument.  Exact correctness uses `DecidesAt`: false output is
derived from literal `RejectsAt` plus distinct accept/reject states, never from
timeout or nonacceptance.

The completed endpoint is precisely the versioned inclusion

```text
uniformP_subset_PpolyDAG :
  forall L, UniformP L -> Pnp3.ComplexityInterfaces.PpolyDAG L
```

This is infrastructure, not P-vs-NP mainline progress.  It does not rebind the
repository's canonical `P`, establish a canonical-`P` equivalence with
versioned `UniformP`, introduce `UniformNP`, or prove a circuit lower bound.

The P1a model repair, final P1b circuit simulation, and P1c countability
diagonal are infrastructure. They do not change the repository's canonical
`P` or `NP` definitions and are not P-vs-NP mainline progress. In particular,
they prove none of the following:

- a bridge to the legacy machine model or canonical `P`;
- a canonical `P` rebind or equivalence with versioned `UniformP`;
- `UniformNP`, a lower bound, or any pnp4 mainline source obligation.

Accordingly, arbitrary length-advice languages are excluded only from this
versioned `UniformP`, not from the unchanged legacy canonical `P`.  Final P1b
and P1c infer no canonical-class bridge.  Any optional comparison corollary
involving pnp4 is deferred to a separate reviewed slice.
