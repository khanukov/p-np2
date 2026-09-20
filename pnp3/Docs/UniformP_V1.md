# Uniform P V1 foundation and circuit simulation

**Status:** P1a uniform model, P1b `UniformP ⊆ PpolyDAG` simulation, P1c
countability/direct no-length-advice diagonal, P2-1 pair-codec infrastructure,
P2-2 advice-free relation semantics/versioned `UniformNP`, P2-3a fixed
pair-parser executable core, and P2-3b universal exact parser correctness
plus P2-3cA ambient-budget parser transport through 2026-09-04. Canonical `P`
and `NP` remain legacy and unchanged. P2-3cB1 additionally provides generic
bounded budget transport for a fixed `UniformTM`; P2-3cB2 adds the routed
combined-machine constructor and exact parser handoff; P2-3cB3 proves total
combined relation verification.

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

## P2-1 uniquely-decodable pair codec

`PairEncoding.lean` imports only the V1 machine foundation and narrow
`Mathlib.Data.List.OfFn` support.  For input `x` and witness `w`, its exact
grammar is

```text
encodePair(x,w) = false,x0,false,x1,...,false,x(n-1),true,w0,...,w(m-1)
pairLength n m = 2*n + 1 + m
```

`decodePairList` is structural and executable: empty input and a dangling
false tag fail; an initial true ends the input and leaves the entire remainder
as witness; and an initial false consumes exactly one following data bit before
recursing.  The exact-image theorem is

```text
decodePairList l = some (xs,ws) ↔ l = encodePairList xs ws
```

so malformed words are exactly those outside the image, and both the list
encoder and the packed dependent indexed encoder are injective.  The indexed
decoder returns `(Sigma n, Bitstring n) × (Sigma m, Bitstring m)` and its
roundtrip preserves both lengths and functions exactly. Its indexed `some`
and `none` theorems characterize the complete packed encoder image, rather
than only canonical forward calls. Layout theorems pin every tag, data,
separator, witness, and initial-tape padding cell. Empty and
two-input/one-witness capstones are derived from the general roundtrip.

This is unique decoding of complete finite words, not global prefix-freeness.
The theorem `encodePairList_witness_extension_prefix` states the exact
factorization when a witness is extended, formally exhibiting one valid
encoding as a prefix of another. P2-1
introduces no witness relation, relation verifier, parser machine, `UniformNP`,
`P ⊆ NP`, canonical migration/rebind, or pnp4 theorem.  It is infrastructure,
not P-vs-NP mainline progress.  `Tests/UniformV1PairEncodingSurfaceTests.lean`
pins every public definition and theorem; direct and wrapper axiom roots remain
centralized in `Tests/AxiomsAudit.lean`.

## P2-2 advice-free relations and versioned `UniformNP`

P2-2 adds
`WitnessRelation := ∀ n m, Bitstring n → Bitstring m → Bool` and lifts each
relation to a **total raw-word language** through the P2-1 codec. For every
`y : Bitstring N`, `encodedRelationLanguage R N y` matches `decodePair y`; a
malformed word (`none`) has answer `false`, while a decoded pair is passed to
the one fixed `R` at its dependent input and witness lengths.

`VerifiesRelation M verifierExponent R` requires, for every raw length `N` and
raw word `y`,

```lean
DecidesWithin M (polyClock verifierExponent N) y
  (encodedRelationLanguage R N y)
```

Thus a false relation answer and a malformed encoding require literal
rejection within the actual raw-length clock. Timeout or mere nonacceptance is
not rejection. Correctness on `encodePair x w` is derived from total semantics
using `decodePair_roundtrip`; no parser machine is introduced.

`UniformNP L` fixes one relation `R`, one finite verifier `M`, one verifier
exponent `verifierExponent`, and an independent witness exponent
`witnessExponent` before inputs. Its certificate clause is exactly

```lean
∀ n (x : Bitstring n),
  L n x = true ↔
    ∃ m, ∃ w : Bitstring m,
      m ≤ polyClock witnessExponent n ∧
      R n m x w = true
```

The two exponents are not combined with `max`, and no budget-monotonicity
theorem is assumed. Executable controls distinguish literal acceptance,
literal rejection, and timeout/nondecision; in particular, the all-accepting
machine fails total verification because it accepts the malformed empty raw
word instead of rejecting it. Canonical round-trip plus literal two-sided
decision yields `verifiesRelation_unique`: for fixed `M` and
`verifierExponent`, at most one `WitnessRelation` is verified, formally closing
the mathematical-relation advice loophole. This slice proves no parser machine,
`UniformP ⊆ UniformNP`, canonical `P`/`NP` rebind, pnp4 theorem, or lower bound.
`Tests/UniformV1RelationSurfaceTests.lean` pins all ten public definitions and
all seventeen source theorems with full named wrappers; paired roots remain in
the central axiom audit.

## P2-3a fixed pair-parser executable core

`Complexity.Uniform.V1.FixedPairParserCore` supplies one fixed ten-state
`UniformTM` for the complete-word grammar
`(false,dataBit)* ++ true :: witnessBits`. The module pins its full raw table,
the table installed in the machine, public absorbing verdict rows, the actual
30-element state/symbol table domain, exact clock `2*N+1`, and exact-clock
allocation `3*N+2`.

Its semantic evidence is intentionally finite: closed decoder and literal
exact-run regressions cover malformed `[]`, `[false]`, and `[false,true]`, as
well as zero-input `[true]`, true-as-data `[false,true,true]`, and a false
witness bit `[true,false]`. Closed valid and malformed configurations pin the
literal verdict state, head zero, and equality of the entire allocated tape to
the corresponding exact-budget initial tape. The paired surface module gives
all seven source theorems exact named wrappers; their direct and wrapper roots
live in the central `Tests/AxiomsAudit.lean` file.

This is executable P2-3a infrastructure only. It proves no all-length parser
correctness, universal acceptance/decoder equivalence, first-terminal-time
theorem, arbitrary ambient-budget result, parser/verifier composition,
relation verification, `UniformP` inclusion, state minimality, or circuit-gate
bound.

## P2-3b universal exact fixed-pair-parser correctness

`Complexity.Uniform.V1.FixedPairParserLanguage` independently specifies the
complete-word grammar `(false,dataBit)* ++ true :: witnessBits` twice: as a
three-phase DFA and as an inductive list grammar. Both are proved equivalent to
successful `decodePair` on every raw indexed word; neither definition uses the
parser machine.

`Complexity.Uniform.V1.FixedPairParserCorrectness` keeps the tape budget fixed
definitionally at `clock N = 2*N+1`. A separate `N=0` root handles the single
blank transition. For positive inputs, `ForwardAt` covers times `1..N` with cell
zero erased and `BackAt` covers times `N+1..2*N`; both state equality of the
entire exact-budget tape against the erased-zero model. The deadline transition
restores cell zero and is the first transition into either public terminal.

Consequently, for every `y : Bitstring N`, the exact deadline configuration is
the exact-budget initial configuration with only its state replaced by the
decoder-classified verdict. The head is zero and every allocated tape cell,
including padding, is restored. Exact `AcceptsAt`, `RejectsAt`, and `DecidesAt`
are primary; `DecidesWithin` is derived from the same-budget exact-to-within
theorem.

`Tests.UniformV1FixedPairParserCorrectnessSurfaceTests` pins every public
definition and theorem, and the central axiom audit contains paired direct and
wrapper roots. This slice does not compose a parser and verifier, verify a
relation, prove a complexity-class inclusion or migration, add a pnp4 theorem,
or prove circuit resource bounds.

## P2-3cA ambient-budget fixed-parser transport

`Complexity.Uniform.V1.FixedPairParserAmbient` compares exact-clock execution
with execution of the same fixed parser at an ambient budget `B`, under the
explicit premise `clock N ≤ B`. It does not cast dependent configurations.
Instead, `tapeEmbed` preserves numeric addresses, `tapeProject` is a partial
inverse, and `ConfigExtension` records equal control, embedded head and tape
cells, plus literal blankness at every newly allocated address.

Movement commutes only under a proved strict right-room premise. Generic
one-step and bounded-run extension lemmas retain that premise, while the
parser-specific trace proves the head stays within the input segment through
the exact deadline. The resulting ambient theorem preserves the complete raw
word, keeps every cell from `N` onward blank, restores head zero and the full
ambient tape, excludes both terminals at every earlier step, and classifies
literal acceptance/rejection by dependent `decodePair` success/failure.
`DecidesWithin` uses `clock N` and the budget inequality as an explicit witness.

The typed surface is
`Tests.UniformV1FixedPairParserAmbientSurfaceTests`; every public theorem has a
`Pnp3.Tests...check_*` wrapper and paired direct/wrapper roots. This slice does
not prove budget transport for an arbitrary verifier, build a combined
parser/verifier machine, verify a relation, prove class inclusion or migration,
add a pnp4 theorem, or establish circuit bounds.

## P2-3cB1 generic bounded `UniformTM` budget transport

`Complexity.Uniform.V1.BudgetTransport` proves machine-independent transport
between budgets `C ≤ B` for exactly `s ≤ C` transitions from `initialConfig`.
The condition is uniformly sufficient and tight at `N=0`: a run of `s`
transitions uses pre-step configurations at `r < s`; unit head speed gives
`head(r) ≤ r`, hence strict room before every simulated right move in the
smaller `N+C+1` tape. For a fixed positive `N` the same speed estimate has
additional slack; no stronger public theorem is needed by composition. The
final configuration may reach the last cell when `N=0` and `s=C`, but no
further transition is requested.

The resulting runs satisfy the full blank-extension relation and therefore
have equal finite control. `AcceptsAt`, `RejectsAt`, and `DecidesAt` are
equivalent at the same elapsed time. `AcceptsWithin`, `RejectsWithin`, and
`DecidesWithin` transport only from the smaller budget to the larger one using
the original witness; no reverse implication is claimed.

`Tests.UniformV1BudgetTransportSurfaceTests` supplies a full-proposition
`check_*` wrapper for each public theorem, with paired central axiom roots.
This slice adds no combined parser/verifier machine, runtime advice, relation
verification, class inclusion or migration, pnp4 theorem, or circuit bound.

## P2-3cB2 routed combined machine and parser handoff

`Complexity.Uniform.V1.CombinedMachine` constructs one fixed `UniformTM` from
a fixed verifier `V`. Its state space has exactly `8 + V.stateCount` controls:
the eight nonterminal controls of the fixed parser and a disjoint offset copy
of every verifier control. Combined accept and reject are the injected verifier
terminals. The transition table depends only on `V`, never on input length,
budget, decoder output, relation value, or witness.

For parser work controls, the table computes the corresponding fixed-parser
action. A target in the parser work range remains there; a parser-accept target
is redirected directly to injected `V.start`; every other nonwork target is
literal combined reject. Thus the successful rewind row restores cell zero and
hands off in the same transition. The verifier branch maps `V.step`, including
its public terminal absorption.

The module proves same-budget verifier step/run embedding, parser work-state
translation, and prefix agreement only through `steps ≤ clock N`. At the
parser deadline, successful decoding yields full configuration equality with
the embedded `initialConfig V budget y`; decoder failure yields the restored
combined initial configuration with literal reject. This is one machine run;
the standalone parser configuration is only a proof object.

`Tests.UniformV1CombinedMachineSurfaceTests` pins the executable and theorem
surface, while `Tests/AxiomsAudit.lean` contains the paired source/wrapper
roots directly. This slice does not yet
prove the verifier suffix, total clock, `VerifiesRelation`, class inclusion or
migration, a pnp4 theorem, or a gate bound.

## P2-3cB3 total combined correctness

`Complexity.Uniform.V1.CombinedCorrectness` defines the sharp total deadline

```text
totalClock c N = (2*N+1) + (N^c+c)
```

for the single routed machine run. `run_add` is used only to decompose that
run in the proof. On successful pair syntax, the parser endpoint is the full
embedded verifier initial configuration; generic bounded budget transport and
same-budget `run_embed` then execute the verifier suffix. On malformed or empty
raw words, the parser endpoint is literal combined reject and terminal
absorption preserves it through the suffix.

The module proves exact `DecidesAt` and `DecidesWithin` at the sharp total
budget for every raw word. It then proves
`totalClock c N ≤ polyClock (c+3) N`, with explicit zero-, one-, and larger-
length cases; `c+2` fails at `N=1`. After transporting the exact combined
result to the standard budget, it packages

```lean
VerifiesRelation (combinedMachine V) (c + 3) R
```

from `VerifiesRelation V c R`. The surface is
`Tests.UniformV1CombinedCorrectnessSurfaceTests`, with three typed definition
pins, 22 full-proposition `check_*` wrappers, and paired roots inline in the
central axiom audit.

This slice does not construct a concrete verifier for the tree-circuit content
relation, adapt headerless pnp4 concatenation to tagged pair encoding, compile
V1 `UniformTM` into the legacy pnp4 TM model, prove class inclusion/migration,
or establish a pnp4 lower bound.

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

The P1a model repair, final P1b circuit simulation, P1c countability diagonal,
P2-1 pair codec, and P2-2 versioned `UniformNP` layer are infrastructure. They
do not change the repository's canonical `P` or `NP` definitions and are not
P-vs-NP mainline progress. In particular, they prove none of the following:

- a bridge to the legacy machine model or canonical `P`;
- a canonical `P` rebind or equivalence with versioned `UniformP`;
- a canonical `NP` rebind or equivalence with versioned `UniformNP`;
- `UniformP ⊆ UniformNP`, a lower bound, or any pnp4 mainline source obligation.

Accordingly, not every length-only language belongs to this versioned
`UniformP`; the direct theorem makes no corresponding exclusion claim about
the unchanged legacy canonical `P`. Final P1b and P1c infer no canonical-class
bridge. Any optional comparison corollary involving pnp4 is deferred to a
separate reviewed slice.

The Part A G1 `FixedContentGammaTerminator` phase is a three-state read-only
successor to `FixedContentTagGate`. Under the predecessor's successful tag
premise it scans from cell eight, stops on the first physical gamma terminator,
or rejects at the content blank. Its common deadline is `n + m - 7`; acceptance
occurs exactly after `zeros + 1` steps: tape unchanged; execution
budget-independent. This phase locates only the unary terminator and does not
decode the payload or implement capped arithmetic.

The Part A G2a `FixedContentGammaAnchor` successor has six states. It retags
the merged G1 final configuration, shuttles from the physical terminator to
the fixed tag tail, recognizes cells 6=true and 7=false, erases only cell 7,
and returns to the same terminator in exactly `2 * zeros + 5` steps. The common
deadline is `2 * (n + m)`; G1-none rejects honestly. Cell 7 is a recoverable
marker, not payload storage: G2b must avoid `none` in its counter zone and
restore cell 7 before a phase expecting literal `contentTape`. This phase does
not read/decode payload bits, compute caps, or establish semantic acceptance.
The dependency-closed Part A G2b `FixedGammaPayloadCursorCore` successor has
14 states and contains only the zero-width run and first rolling-hole round.
Its start configuration is a pure retag of G2a's final configuration. The
physical-false branch exposes a canonical next configuration carrying one
`false` symbol in finite control. The physical-true and first-virtual branches
have exact actual-run theorems at `3 * zeros + 6`: both restore literal
`contentTape` and stop at head 6, in `qOne` and `qVirtual` respectively.
`qOne` and `qVirtual` are absorbing internal outcome tags.
The equation `machine.accept = qOne` is an ABI choice local to this tracer;
`qVirtual` is not a machine terminal. No arbitrary-round, general
payload-decoding, or semantic-acceptance theorem is part of this surface.

The Part A G2c `FixedGammaPayloadRoundStep` successor has 11 states and 33
publicly pinned transition entries.  It retags the core's absorbing false
handoff without modifying that ABI.  Its exact `roundTape` boundary has holes
at cell 7, counter cells `8 .. 7+k`, and the current payload cursor
`8+zeros+k`.  For `1 ≤ k < zeros`, a physical-false step restores the old
cursor, consumes exactly one new counter cell, opens the next cursor, and
returns to this same machine's start state in `2*zeros+4` steps.  The exported
`k=1→2` theorem is derived from the core's actual `first_physical_false_exact`
run.  The true, virtual, and exhausted tags have no cleanup or semantic theorem
here; `machine.accept = qOnePending` is only this successor's local ABI choice.
There is no whole-payload verdict; G2d adds boundary induction only.

The proof-only Part A G2d `FixedGammaPayloadRoundDriver` reaches every boundary
`1 ≤ k ≤ zeros` under the uniform absolute-cell physical-false prefix
`9 + zeros ≤ j < 9 + zeros + k`. Boundary one is the real successor
`startConfig` at local clock zero, and boundary `k` is reached at the
transparent successor-local clock `(k - 1) * (2 * zeros + 4)`. This clock is
not combined with the predecessor machine's run. The module adds no exhausted,
true, or virtual outcome, no whole-payload verdict, and no semantic claim or
bridge.

The proof-only Part A G2e `FixedGammaPayloadExhausted` executes the last
boundary for exactly `zeros + 3` more successor-local steps. At the strict
first visit to the absorbing internal tag `qExhausted`, the head is
`8 + zeros` and the tape remains the last-boundary `roundTape`; there is no
restoration or cleanup. The composed clock
`boundaryClock zeros zeros + (zeros + 3)` is not a cross-machine total clock.
The theorem requires `0 < zeros` and the full physically present false prefix.
The tag asserts neither semantic acceptance nor an all-zero payload verdict,
and this module adds no complexity bridge.

The proof-only Part A G2h `FixedGammaPayloadPendingOutcomes` handles exactly
the nonfinal boundaries `1 ≤ k < zeros`.  From a G2d-reachable boundary, one
round costs `2 * zeros + 4` and stops on cell `9 + zeros + k`, with the common
uncleaned `pendingTape`: a physical `true` reaches absorbing `qOnePending`,
and the exact physical-boundary equality `9 + zeros + k = a + m` reaches
absorbing `qVirtualPending`.  Strict first arrival is proved both locally and
from the successor start.  The transparent `pendingClock` is successor-local;
the module excludes `k = 0`, `k = zeros`, cleanup, whole-payload and semantic
verdicts, and cross-machine timing.

The Part A G2f successor `FixedGammaPayloadZeroCleanup` retags that exact
absorbing endpoint into a separate five-state machine, preserving G2e's
`qExhausted` row. Starting on the terminator, it scans right over the complete
physical-false payload, replaces the cursor hole by literal `false`, scans left
over payload and terminator, and fills every contiguous counter/anchor hole
down through cell 7. It stops for the first time at local clock
`3 * zeros + 3` (`0 < zeros`) in absorbing internal `qDone`, with head 6 and
literal `FixedPairContentMarkerErase.contentTape`. The fixed 15-row table is
per-step budget independent, and the API pins the handoff, initial footprint,
and exact arithmetic bounds used to type the phase configurations. It does not
state run-level no-clamp safety. Neither the tag nor the trace is a semantic
all-zero/acceptance theorem, and no cross-machine total clock is stated.

The Part A G2i successor `FixedGammaPayloadPendingCleanup` retags either exact
G2h pending endpoint with one branch-independent start configuration. The
pending cell carries the branch data: `some true` is preserved into the
one-back scan, `none` into the virtual-back scan, and `some false` rejects.
Both branches restore holes `8+k` through cell 7 with physical false and read
fixed tag cell 6 unchanged. At strict first successor-local clock
`zeros + k + 4`, the tape is literal `contentTape`, the head is 6, and the
distinct result is absorbing `qOne` or `qVirtual`; the wrong tag is excluded
throughout. The fixed 24-row table has no right move and is budget independent.
Generic trace theorems prove head nonincrease and that cells strictly above the
initial head stay fixed. No semantic verdict, dispatcher claim, acceptance
meaning, cross-machine clock, or complexity bridge is stated.

The Part A G2k `FixedGammaPayloadDispatcher` is a fixed 28-state, 84-row routed
block sum of the payload cursor, round, exhausted cleanup, and pending cleanup
tables. Its input retags the actual G2a deadline run; the control and table
contain no input, `zeros`, `k`, or proof data. Its absorbing endpoints are
distinct `qAllZero`, internal `qHasOne`, and shared `qReject`. Exact executable
theorems in this slice activate malformed, zero-width, and `k = 0` physical-true
and virtual paths. Zero width retains head 7; cleaned paths retain head 6 and
literal `contentTape`. Positive-round, pending, and exhausted rows are routed
but do not yet have unified run theorems, so no whole-dispatcher semantics are
claimed. This is infrastructure only and changes no pnp4 semantics.

The proof-only Part A G2l `FixedGammaPayloadDispatcherRounds` activates the
remaining positive-round dispatcher paths from the actual dispatcher
`startConfig`. Its transparent clocks compose the core, round-driver, and
cleanup clocks with zero handoff offsets. For `1 ≤ k < zeros`, an all-false
prefix followed by a physical true bit reaches strict first `qHasOne`, while a
first virtual cell reaches strict first `qAllZero`; a fully false payload with
`0 < zeros` reaches strict first `qAllZero` through exhaustion. All cleaned
endpoints have head 6 and literal `contentTape`, with the sound wrong endpoint
and reject tags excluded throughout. The positive formulas deliberately omit
`k = 0`, and pending outcomes deliberately require `k < zeros`. This remains
execution infrastructure: it states no payload semantics, parser/decode fact,
whole-dispatcher iff, length-only cap, or pnp4 consequence.

The proof-only Part A G2m `FixedGammaPayloadDispatcherDeadline` closes the
dependency-contained dispatcher timing/classifier slice.  Its transparent
length-only deadline is `2*N*N`.  A bounded induction over the decoded gamma
payload constructs the first physical-true, first-virtual, or exhausted index;
the proof uses neither `Nat.find` nor choice and defines no proof-derived
runtime search.  Every existing malformed, zero-width, first-read, positive
pending, and exhausted exact clock is bounded by that deadline and lifted by
the three absorbing endpoint rows.  Under a matching tag the resulting total
classification pins literal `contentTape` and the branch-specific head
(`a+m`, `7`, or `6`), and proves physical iff statements for `qHasOne`,
`qAllZero`, and `qReject`.  It does not identify a uniform head, interpret a
pnp4 reader, assert parser acceptance, or change any canonical complexity
class; it is infrastructure only.

The Part A G2p-a `FixedGammaTerminatorScratchBootstrap` is the first fixed
phase that writes outside the content cells.  Its start configuration only
retags the actual G2m dispatcher configuration at the dispatcher deadline.  On
a matching tag with physical terminator at `8+zeros` (`N = a+m`), two fixed
steps through the `qStart` and `qNormalize` rows normalize dispatcher heads
`6` and `7` to cell `8`.  The machine then
scans the gamma zeros and blanks the terminator as a return marker, the unique
blank cell below `N`.  It scans to the blank boundary `N`, writes `true` at
scratch cell `N+1` (allocated for every budget, since the tape has
`2a+m+B+2` cells), steps back over `N`, scans left to the marker, and restores
it.  The public `traceState`/`traceHead`/`traceTape` schedule is exact at
every time.  The first terminal time is `2*N-11-zeros`, the length-only
deadline is `2*N`, and the endpoint is `qTerm` at head `8+zeros` with
`contentTape` changed only at `N+1`.  A failed gamma scan rejects after one
step at head `N`.  All 27 rows are pinned literally.  On successful runs the
module proves strict first arrival and the head window `[6, N+1]`, with only
the marker and scratch cells ever differing from `contentTape`; clamp freedom
and budget independence hold on every tagged input.  `qTerm` is an internal
endpoint rather than language acceptance, and the module states no pnp4 reader
or parser fact; it is infrastructure only.

The Part A G2p-b `FixedGammaTargetFirstPayload` copies the first gamma payload
bit into the target register, which is filled most significant bit first from
scratch cell `N+1`; this module adds only its second digit, at `N+2`.  Its start
configuration only retags the actual G2p-a bootstrap configuration at the
bootstrap deadline.  On a matching tag the 18-state machine blanks the terminator
`8+zeros` as a marker, walks left over the gamma zeros to tag cell `6`, and
blanks cell `7` as an anchor.  If the marker directly follows the anchor (width
zero), it restores both and halts; it reads no cell beyond `8`.
Otherwise it walks to the marker and reads the payload cell `9+zeros`.  A
physical `some b` is carried in control as `b` to the blank boundary `N`.  A
blank payload cell (then `9+zeros = N`) is the virtual zero, carried as `false`
without reading the scratch `true` at `N+1` as source.  The bit is written at the
target cell `N+2`, and the machine returns to restore the terminator and cell
`7`.  At the length-only deadline `3*N`, the endpoint is `qDone` at head `7`.
Width zero ends on the bootstrap scratch tape with no room premise.  Positive
width ends on `firstPayloadTape` with the physical bit or `false`, assuming
exactly `a+m+2 < tapeLength (pairLength a m) B`.  Malformed gamma ends in
`qReject` at head `N` on `contentTape`.  All 54 rows are pinned.
At every time the module proves clamp freedom on every tagged input and budget
independence across any two budgets, assuming room (`a+m+2 < tapeLength
(pairLength a m) B`, for both budgets in the latter) whenever the gamma width is
positive; malformed and width-zero inputs need no premise.  On decoded widths it
also proves the head window `[6,8]` (width zero) or `[6,N+2]` (positive width)
and the footprint `{7, 8+zeros, N+1, N+2}`, again assuming room for positive
widths; room fails at `a = B = 0`.  No theorem covers a positive width without
room, so nothing here says that `qReject` at this deadline implies malformed
gamma.  `qDone` is an internal endpoint; only the first payload bit is copied,
and the module states no pnp4 reader or parser fact.  Unlike G2p-a it exports no
exact first-arrival clock or strictness, only the length-only deadline.  It is
infrastructure only.

The Part A G2p-c `FixedGammaTargetSecondPayload` copies the **second** gamma
payload digit into the target register.  It landed in two slices against one
fixed 14-state, 42-row table: G2p-c1 fixed the table, the input ABI, exact room,
the phase-local clocks, and the two decoded widths at which the machine makes no
net payload or register write, and G2p-c2 added the positive-width
(`2 ≤ zeros`) execution that actually performs the copy.  The start
configuration is a *phase-local handoff*: it definitionally retags the actual
G2p-b `FixedGammaTargetFirstPayload` configuration at the G2p-b deadline,
replacing only the control field, and `handoff_exact` pins head and tape to that
endpoint.  It is a real provider, but it is not one fixed machine running from
the raw pair input, so the length-only deadline `2*N` and the exact clocks below
are this phase's cost alone and omit every step inside the start configuration;
clock composition remains out of scope.  No width, digit index, bit, target
address, proof term, or clock enters the control.

Positive width.  Under a matching tag, `gammaZeros? (Fin.append x w) = some
zeros` with `2 ≤ zeros`, and the exact room `a+m+3 < tapeLength (pairLength a m)
B` (equivalently `2 ≤ a+B`), `second_payload_exact` gives for every
`s ≥ exactClock N zeros = 2*N-7` the endpoint `qDone` at head `7` with the whole
tape equal to `secondPayloadTape B x w b0 c`: content restored, blank boundary
at `N`, register `true` at `N+1`, G2p-b digit `b0` at `N+2`, second digit `c` at
`N+3`, blanks after (`secondPayloadTape_layout`).  `second_payload_strict`
excludes both terminal states for every `s < 2*N-7`, so that value is the
*first* terminal time — derived row by row, not assumed, and the same in all
three shapes of the route (both payload cells physical; the source cell exactly
at the boundary; the first payload cell already at the boundary).  The copied
value `c` is the *content* symbol at the logical source address `10+zeros`, the
second payload cell of the block `[9+zeros, 9+2*zeros)` — `second_source_cell`
pins `10+zeros = 9+zeros+1` and places it inside the block under `2 ≤ zeros`,
that direction only and with no converse — so `c` is
`(physicalSymbol (Fin.append x w) (10+zeros)).getD false`.  That endpoint is
extensional, and the three shapes realize it by three different schedules.  With
`10+zeros < N` the source is physical and the control really does read it: the
run steps *over* the first payload cell `9+zeros` in `qStepOne` and reads
`10+zeros` in `qRead`, and that bit is copied verbatim
(`second_physical_exact`).  With `10+zeros = N` the source address *is* the
blank boundary, so `qRead` is entered and scans that blank, taking the virtual
zero.  With `9+zeros = N` the *first* payload cell is already the blank
boundary, so `qStepOne` reads *that* blank and hands straight to the register:
`qRead` is never entered, and the address `10+zeros` is then `N+1`, the register
cell — the head passes it, but in `qReg0` and over a tape holding the register
`true`, which is crossed rather than read as a source.  Both virtual shapes copy
`false` (`second_virtual_exact`, premise `a+m ≤ 10+zeros`), which is what
`Option.getD` records for a `none` content symbol.  Neither the register `true`
at `N+1` nor the G2p-b digit at `N+2` is taken as the source; both are crossed
in the register state that the selection already fixed.
`positive_width_head_range` bounds the head by `[7, N+3]` at every time and
`positive_width_no_boundary_clamp` shows that no transition of this branch
clamps at either tape end (the head *enters* the last allocated cell of the run,
`N+3`, on the preceding right move out of `N+2`, and the transition taken *at*
`N+3` is the write, which moves left, so no right move is attempted from the
last cell).  Both are head facts, not a footprint: they say nothing about which
cells may differ from the incoming tape.

Widths zero and one.  The machine blanks tag cell `7` as its single anchor and
steps onto cell `8`.  A terminator at `8` is width zero and a terminator at `9`
is width one; in both cases it turns around, restores the anchor, halts in
`qDone` at head `7`, and hands back the tape it was handed unchanged, so it
leaves behind no net payload or register write (the anchor *is* blanked in
flight and restored, so what is proved is the absence of a net tape change).
Every *allocated* cell after `N+2` stays blank, the target cell `N+3` included
whenever it is allocated (the width-one premise allocates only `N+2`, so that
claim is vacuous exactly when `N+3` does not exist).  For these two widths the
private traces keep the head in `[7,9]`, so no cell past `9` is read, but that
read bound is internal: the exported endpoints are tape equalities, which pin
the net effect of the run and not the cells it visited.  The two sweeps have
different delimiters: only the leftward `qScanLeft` sweep is delimited by a cell
the run itself maintains, the blanked anchor at `7` (the unique blank below `N`
while the run is in flight); the rightward sweep is delimited in phases by cells
the run maintains none of — the input terminator at `8+zeros` ends the
`qSeekTerm` scan at every width, and on a positive width the layout blank at `N`
then ends the walk across the content and the first blank after the register,
the target cell `N+3`, ends the register walk, that last delimiter being
consumed by the write rather than maintained.

Clocks and room.  `exactClock` is `3`, `5`, `2*N-7` by *decoded* width, and all
three values are now proved exact first arrivals — the endpoint holds from that
time on, and neither terminal state is reached before it.  A malformed gamma has
no decoded width and is clocked separately by `malformedExactClock = 1`, which
`malformed_exact` and `malformed_strict` together prove to be its first terminal
time: the `qReject` endpoint holds from step `1` on, and at step `0`, the
handed-over configuration itself, neither terminal state is reached.  Truncated
`Nat` subtraction makes `2*N-7` degenerate for `N ≤ 3`, which the positive-width
premises exclude: there `N ≥ 9+zeros ≥ 11`.  `exactClock_le_deadline` carries
the premise `3 ≤ N`; it is sharp, since width one costs `5` steps, and free in
scope.  Room is exact per width and never inferred from a decoded header:
`room_iff` reads `a+m+3 < tapeLength (pairLength a m) B` as `2 ≤ a+B`, which
fails at `a = B = 0` and at `a+B = 1`; width zero carries no room premise, width
one carries only the G2p-b premise `a+m+2 < tapeLength (pairLength a m) B`, and
the positive width carries `a+m+3 < tapeLength (pairLength a m) B`.  No theorem
covers a width without its premise, so nothing here says that `qReject` at this
deadline implies a malformed gamma, and no converse is stated — in particular
nothing says that `qDone`, or a written digit at `N+3`, implies `2 ≤ zeros`.

Probes.  Independent literal reduction probes identify the actual start
configuration for five concrete inputs, using only the landed G2p-b endpoint
theorems, and then reduce this machine's own run by kernel computation without
invoking any endpoint theorem of this module.  Of the three foundation probes,
the width-zero and width-one probes pin the width dispatch at cells `8`/`9` and
the anchor blank and its restoration, the width-one probe alone also pins the
target cell `N+3` — which every one of these five inputs allocates — still blank
at the endpoint, and the malformed probe pins instead that the handed-over
configuration is in neither terminal state and that one step rejects in place at
the boundary head.  Two positive-width probes walk the whole route in its two
extreme shapes.  The physical probe (`zeros = 2` at `N = 13`) pins
`qStepOne` over the first payload cell, `qRead` at the source cell `12`, and the
`qCarry1` that records the source bit.  The tight probe (`zeros = 2` at
`N = 11`, both payload digits virtual) pins the opposite schedule: `qStepOne`
reads the blank first payload cell and the next step is already `qReg0` at
`12 = N+1`, so `qRead` is never entered and the register `true` that its
endpoint pins at that address is crossed rather than read.  Both then pin the
head on the still-blank target cell at step `N-4`, the digit written by the
transition taken there and visible at step `N-3`, a non-terminal control at step
`2*N-8` — which, both terminal states being absorbing, also excludes any earlier
terminal arrival — and the halt at step `2*N-7`.

`qDone` is an internal endpoint rather than language acceptance; the module
states no pnp4 reader or parser fact.  Deferred: the remaining `zeros-2` digits,
the decrement to `n`, the all-times footprint/budget package (no `footprint` and
no `budget_independence` theorem is exported for any branch), the pnp4 semantic
bridge, every parser and `contentHeader?` claim, and `ContentVerifierBridge`.
It is a specialization and not an iterating round — ending a general payload
scan needs both a counter and an advancing source marker, and this control has
neither.  It is infrastructure only.
