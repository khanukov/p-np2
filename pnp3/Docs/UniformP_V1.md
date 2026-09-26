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
and the module states no pnp4 reader or parser fact.  Part A G3b later added the
exact first-arrival surface this phase had deferred, against the same untouched
table and with every earlier signature unchanged: `exactClock N zeros` is `6` at
width zero and `2*N + zeros - 6` at a positive width, `malformedExactClock` is
`1`, and at a positive width, at width zero and at a malformed gamma — which has
no decoded width at all — an `*_exact` theorem holds from that
time on while the matching `*_strict` theorem puts the control in neither
terminal state strictly earlier, so each clock is a *first* arrival rather than
an upper bound.  `exactClock_le_deadline` (premise `9+zeros <= N`, which the
gamma contract supplies) recovers the five `*_at_deadline` endpoints from the
exact ones, and `strict_first_terminal` bundles both directions with that bound
and with the identification of the first-arrival configuration with the deadline
one -- the premise shape `UniformTM.seq_handoff` consumes.  Five reduction probes
execute the machine at `B = 0` on the physical (`zeros = 1` with each bit value,
`zeros = 3`) and virtual (`9+zeros = N`) positive-width shapes, at width zero and
on a malformed gamma, each at the exact clock and one step before it.  G3b builds
no composition: it states no `seq`, no composed machine and no composed clock.
It is infrastructure only.

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
itself still states no pnp4 reader or parser fact.  The reading is done outside
pnp3, by the G2p-c3 companion
`Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetSecondPayloadBridge`,
which consumes the width-zero, width-one, and positive-width endpoints above and
reads their registers as leading binary digits of `n+1` for a decoded
`contentHeader? (Fin.append x w) = some (n, consumed)`.  How many digits are
exposed is the width: positive width identifies all three cells `N+1`, `N+2`,
`N+3`, width one identifies the two G2p-b cells `N+1`, `N+2` and leaves every
allocated cell past `N+2` blank, and width zero identifies the single G2p-a cell
`N+1`.  That bridge is one-way — header to endpoint — reuses the phase-local
deadline unchanged, and needed no change to this module.  Deferred: the
remaining `zeros-2` digits, the decrement to `n`, the all-times footprint/budget
package (no `footprint` and no `budget_independence` theorem is exported for any
branch), parser execution and every `contentInput?`/`ContentAccepts` claim, and
`ContentVerifierBridge`.  It is a specialization and not an iterating round —
ending a general payload scan needs both a counter and an advancing source
marker, and this control has neither.  It is infrastructure only.

The Part A G2p-d `FixedGammaTargetPayloadLoopFoundation` installs the two
tape-resident markers that a *self-stopping* payload loop needs, as one fixed
14-state, 42-row machine that halts as soon as they are in place.  It is the
finite preamble of that loop, not the loop: the round, its iteration and the
exhaustion finish are deferred, and a later round machine will start from this
endpoint by the same retag ABI that chains G2p-a → G2p-b → G2p-c.

The markers are a **counter** inside the gamma zero field — a consumed zero
rewritten `some true`, **left to right**, so that scanning left from the terminator
over the blank trail the first non-blank cell is an unconsumed zero (`some false`)
while work is left and the last consumed marker (`some true`) when the payload is
exhausted — and a **walking terminator**: the `some true` at `8+zeros` moves one
cell right per *physical* source consumed and the vacated cell is blanked, so the
cell right of the terminator is always the next source.  Marking left to right is
forced: tag cell `7` is also `some false`, so a right-to-left counter could not be
told from the tag.  Those are exactly the two markers the G2p-c specialization
lacks.

The start configuration is a *phase-local handoff*: it definitionally retags the
actual G2p-c `FixedGammaTargetSecondPayload` configuration at the G2p-c deadline,
replacing only the control field, and `handoff_exact` pins head and tape to that
endpoint.  At a decoded width `2 ≤ zeros` two payload digits are therefore already
consumed when this phase starts — `9+zeros` by G2p-b and `10+zeros` by G2p-c — and
that count is a constant of the phase ABI rather than data read off the tape.  The
degenerate widths have consumed fewer, because their payload holds fewer than two
digits: one digit at `zeros = 1` (the G2p-c endpoint there is still G2p-b's
`firstPayloadTape`) and none at `zeros = 0` (it is the bootstrap's `scratchTape`).
`2 ≤ zeros` is also the only width for which this module proves a quantified
endpoint.  What the phase installs is the `r = 2` instance of the loop invariant:
`markers_installed` states that on a matching tag with `gammaZeros? = some zeros`,
`2 ≤ zeros`, and the inherited G2p-c room
`a+m+3 < tapeLength (pairLength a m) B`, the machine has from step
`exactClock zeros = zeros+7` on halted in the absorbing `qDone` at head
`8+zeros+walk (a+m) zeros 2` with tape `loopTape B x w zeros 2`, and
`markers_strict` excludes both terminals at every earlier step, so that step is the
first terminal time.  `walk N zeros r = min r (N-9-zeros)` covers the three source
shapes in one closed form — both consumed sources physical (`10+zeros < N`), only
the first physical (`10+zeros = N`), neither (`9+zeros = N`) — and a virtual source
costs the same three steps as a physical one, which is what keeps the clock
width-only.  Advancing the terminator is destructive only as far as it moves, so
which cells are rewritten depends on the shape: the both-physical shape overwrites
`9+zeros` and `10+zeros` with `some true` and blanks the first again, the middle
shape overwrites only `9+zeros`, as the new terminator, and the tight shape
overwrites neither.  The input terminator cell `8+zeros` is blanked exactly when
`9+zeros < N`, and `loopTape_layout` states precisely that: the blank at `8+zeros`
is a conditional conjunct, while the two counter marks, the walking terminator, the
three register cells, the blanks past `N+3` and the untouched tag prefix are
unconditional.  The endpoint tape is therefore not `contentTape`.
`markers_at_deadline` restates the endpoint at the phase's length-only
`deadline N = N`; a malformed gamma inherits the G2p-c rejection in one step,
room-free, with no first-arrival direction proved for it.

Room is inherited rather than needed: the head never moves past `N`, a cell every
budget allocates, so none of this phase's `.right` moves can clamp; the
`a+m+3 < tapeLength (pairLength a m) B` premise (`room_iff`: `2 ≤ a+B`) is what
makes the incoming tape known and what allocates the three register cells
`loopTape` mentions.  Nonvacuity is independent of the endpoint theorems: for the
two extreme shapes, plus width zero, width one and a malformed gamma, the surface
tests first identify the phase-local start configuration for every budget from the
landed G2p-c endpoint theorems alone, then reduce this machine's own `run` by
kernel computation at `B = 0` — exposing the two marks appearing at steps two and
three, the new terminator cell, the blanked trail, the restored width-one mark, and
the halt at step nine.

Deferred: the round (counter test, source read, carry, register write), its
iteration, the exhaustion finish that restores the gamma zero field, the complete
target register, the intended loop's own deadline, the all-times
clamp/footprint/budget package, the decrement from `n+1` to `n`, the room a full
loop needs (`N+1+zeros < tapeLength (pairLength a m) B`, assumed nowhere here), and
the *quantified* endpoints of the two degenerate widths — `zeros = 0` halts after
two steps and `zeros = 1` after five with its counter mark restored through `qFin`,
but only the literal probes witness that here — along with `malformed_strict`, the
first-arrival direction of the malformed branch.  Two surface obligations were also
owed to the next slice, left undone by this one only because it already sat at its
1500-changed-Lean-LOC gate: its surface test did not yet restate all 42 table rows
literally, aliasing `table_and_resource_pins` instead, and the audit reached the 14
`Fin` state constants only through `raw`/`machine`.  Both are discharged at this
head, as the next paragraph records.  This foundation is not connected to
`contentHeader?`: no theorem mentions a decoded header field, and no pnp4 bridge
exists for it.  `qDone` is an internal endpoint, never language acceptance, and no
clock here accounts for the steps embedded in `startConfig`.  It is infrastructure,
not P-vs-NP mainline progress.

The two surface obligations that slice left owed are discharged by the G2p-d round
below: all 42 of its table rows are now restated literally in `check_table_rows` of
`Tests.UniformV1FixedGammaTargetPayloadLoopFoundationSurfaceTests`, rather than only
aliased through `table_and_resource_pins`, and the 14 `Fin` state constants now have
direct `#print axioms` entries in `Tests.AxiomsAudit` instead of being reached only
through `raw`/`machine`.

The Part A G2p-d `FixedGammaTargetPayloadRound` executes **one** round of that
self-stopping loop, as a second fixed machine — 22 states, 66 rows, every row pinned
literally in the module and restated literally in its surface test.  It is one round,
not the loop: the iteration, the exhaustion finish and the loop's own deadline are
deferred.  Its start configuration is a *phase-local handoff* by the same retag ABI
that chains G2p-a -> G2p-b -> G2p-c -> G2p-d: it definitionally retags the *actual*
`FixedGammaTargetPayloadLoopFoundation` configuration at that phase's own length-only
deadline, replacing only the control field, and `handoff_exact` pins head and tape to
that endpoint.  It is therefore a real provider but not one fixed machine running from
the raw pair input, and its clock is this phase's cost alone.

The round carries the loop invariant `loopTape B x w zeros r` from `r = 2` to
`r = 3`.  In detail: `qLoop` steps off the walking terminator; `qCntL` runs left over
the blank trail into the gamma zero field, where a `some false` is an unconsumed zero
(work remains) and a `some true` would be the last counter mark, the exhaustion case,
handed to `qFin` -- those rows are fixed in the table but do not run during the first
`roundClock N` transitions covered by `round_step`; `3 <= zeros` excludes that branch
on this exact `r = 2` to `r = 3` segment.  `qCntZ` then runs left over the
unconsumed zeros to the last counter mark, `qCntMark` marks the first unconsumed
zero, which at `r = 2` is cell `10`, and `qCntBack` runs right over the rest of the
field and the blank trail to the terminator and steps onto the cell right of it: the
next source.  `qSrc` reads that cell.  A **physical** source (`some b`) is overwritten
with the new walking terminator, `qClear_b` blanks the cell the terminator just left,
and `qCarry_b` carries `b` right across the content to the boundary blank at `N`; a
**virtual** source *is* that boundary blank, and `qVa`/`qVb` pad that branch so that
both cost the same.  `qReg_b` (resp. `qRegV`) then walks the register to its first
blank, cell `N+2+r`, and writes `b` (resp. the virtual zero) there -- the round's only
register write, an **append**.  There is no arithmetic carry anywhere: the decrement
from `n+1` to `n` is a separate, deferred phase, and `qCarry_b` only names the bit
held in the finite control between the read and the write.  `qBackReg`/`qBackCont`
(physical) and `qBackRegV`/`qVc` (virtual) walk back and re-enter `qLoop` on the new
terminator, restoring the `r+1` invariant.  Every branch is decided by the symbol
under the head: no width, digit index, target address, proof term, advice or producer
mark occurs in the control. It carries only the scanned source result: a physical bit
until its write, and the physical-versus-blank branch until `qLoop` re-entry; the
round never computes its source address.

`round_step` is the execution theorem.  Under a matching tag,
`gammaZeros? (Fin.append x w) = some zeros` with `3 <= zeros`, and the round's own
room `a+m+4 < tapeLength (pairLength a m) B`, the machine is after exactly
`roundClock (a+m) = 2*(a+m)-7` steps in `qLoop` at head `8+zeros+walk (a+m) zeros 3`
with the whole tape equal to `loopTape B x w zeros 3`.  The premise `3 <= zeros` is
the work-remaining condition: the round's source is the third payload digit, index
`2` of the block `[9+zeros, 9+2*zeros)`, i.e. the cell `11+zeros`, and there is such
a digit exactly then -- which is also exactly what makes cell `10` an *unconsumed*
gamma zero, so that the counter can grow.  `source_pins` states the address direction
only: with `11+zeros < N`, `sourceCell N zeros = 11+zeros`, inside the payload block;
with `N <= 11+zeros`, the source address is the boundary blank `N`.  In the latter
branch `round_step` leaves the terminator unmoved, while `registerBit_source` identifies
the appended digit as the virtual `false` through `Option.getD`.  Nothing says
the converse: neither that `qLoop` at `roundClock N`, nor a digit at `N+4`, implies
`3 <= zeros`.

`roundClock N = 2*N-7` is **length-only** and the same in both source shapes.  That
is not an accident of the bookkeeping: the counter walks cancel against the
terminator's position, and `qVa`/`qVb` pad the virtual boundary case to the algebraic
continuation of the physical schedule.  It is an *exact* time and not a
time from which the endpoint persists, because the endpoint control `qLoop` is **not**
absorbing; consequently this slice exports no phase deadline at all, and the next
slice must hand off at exactly `roundClock N`.  Room is strictly wider than the
foundation's, because the register grows by one digit: `room_iff` reads
`a+m+4 < tapeLength (pairLength a m) B` as `3 <= a+B`, one cell more than the
foundation's `2 <= a+B`, and notes that it implies the foundation premise so the
handoff stays available.  This is sufficient for the proved run, whose head reaches
`N+4` and writes there.  By the proof's table trace (not an exported all-times theorem),
the decoded-width path never goes below cell `9`: the tag prefix and first counter mark,
cell `8`, are never scanned, while cell `9` stops `qCntZ` and hands over to `qCntMark`.
`malformed_rejects` handles the one case the retag could otherwise obscure:
`retagLoopFoundation` replaces the foundation's `qReject` with `qLoop`, and a
malformed gamma then rejects again in one step, room-free, at boundary head `a+m`
(cell `8` when `a+m = 8`), on the unchanged content tape -- with no first-arrival
direction and no converse.

Nonvacuity is independent of the endpoint theorems.  Two literal probes first
identify the phase-local start configuration for every budget from the landed G2p-d
foundation endpoint theorem alone, then reduce this machine's own `run` by kernel
computation at `B = 0`, invoking no endpoint theorem of this module.  The physical
probe (`zeros = 3`, `N = 15`) pins the third counter mark at cell `10`, the head on
the source cell `14`, the `true` read there carried in the control as `qClear1`, the
vacated cell `13` blanked, the appended digit written at `N+4 = 19`, a still
non-terminal `qBackCont` at step twenty-two, and the re-entry into `qLoop` at step
`23 = 2*15-7` on the new terminator `14`.  The virtual probe (`zeros = 3`, `N = 12`,
`walk N 3 2 = 0`) pins the opposite schedule: the source address is the boundary
blank `12`, `qVa`/`qVb` are entered, the digit appended at `N+4 = 16` is the virtual
`false`, and `qLoop` is re-entered at step `17` on the *unmoved* terminator `11`.

Deferred: the iteration of this round, the exhaustion finish that restores the gamma
zero field, the complete target register, the loop's own deadline, a cell-by-cell
`r = 3` layout theorem (the endpoint is already a full tape equality to the public
`loopTape`, whose `r = 2` layout the foundation pins cell by cell), a
first-arrival/strictness direction for the round, the all-times clamp/footprint/budget
package, the decrement from `n+1` to `n`, the room a full loop needs
(`N+1+zeros < tapeLength (pairLength a m) B`, assumed nowhere), and the degenerate
widths `zeros <= 2`.  The public `startConfig` at `zeros = 2` can follow the
exhaustion path through `qFin` to `qDone`, but that behavior remains outside the
proved theorem surface.  Nothing here is connected to `contentHeader?` or to any parsed
header value, and no pnp4 bridge exists for this module; `qDone` is not language
acceptance.  Clock composition, the fixed parser,
the checks, advice freedom, `NP` membership and `ContentVerifierBridge` are out of
scope.  It is infrastructure, not P-vs-NP mainline progress.

Three of those deferred items are discharged below: the iteration of the round and the
complete target register by the Part A G2p-e slice, and the exhaustion finish that
restores the gamma zero field by the Part A G2p-f slice.  A fourth moves rather than
closes: the premise `N+1+zeros < tapeLength (pairLength a m) B` recorded above as
assumed nowhere is now assumed and characterized (`zeros <= a+B`), and G2p-f's
`payload_exhausted` proves it *sufficient* for a complete loop with the exhaustion
finish included; whether that much is *necessary* is still open, there being no
footprint theorem.  A fifth shrinks: of the degenerate widths above, `zeros = 2` is now
inside G2p-f's `payload_exhausted`, which needs only `2 <= zeros`, so only `zeros <= 1`
stays outside the proved surface.  The rest -- a *length-only* loop deadline (G2p-f's
exported persistence is from the width-dependent `totalClock N zeros`), the decrement from
`n+1` to `n`, the footprint/budget half of the all-times package, and every header/pnp4
connection -- still stand, and so does strictness for the round itself: G2p-f's
first-arrival direction and all-times clamp hold for the finish, where `qDone` absorbs,
and not for a round endpoint sitting in the non-absorbing `qLoop`.

The Part A G2p-e `FixedGammaTargetPayloadIteration` adds **no new machine**.  The round
machine above re-enters `qLoop` on the new walking terminator, which is exactly the
control its own start configuration carries, so the *same* fixed 22-state, 66-row table
iterates; `check_machine_reused` pins that this module's opened `machine` is
`FixedGammaTargetPayloadRound.machine`, while the full wrappers pin that the new theorems run
that opened machine.  What the slice adds is the
quantification the landed `round_step` lacked, and the induction that quantification
unlocks.

`round_generic` is the reusable round.  Its hypotheses are a matching tag,
`gammaZeros? (Fin.append x w) = some zeros`, an index `r` with `1 <= r` and work
remaining (`r < zeros`), that index's own room
`a+m+2+r < tapeLength (pairLength a m) B`, and the three projections of an
**arbitrary** configuration `c`: `c.state = qLoop`, `c.head.val = 8+zeros+walk N zeros r`
and `c.tape = loopTape B x w zeros r`.  Its conclusion is state, head and the whole
tape of `machine.run (roundClock N) c`: `qLoop`, head `8+zeros+walk N zeros (r+1)`,
tape `loopTape B x w zeros (r+1)`.  Compared with `round_step` two things are general:
the index `r` -- so the counter mark is cell `8+r`, the source cell
`9+zeros+walk N zeros r`, and the appended register cell `N+2+r`, none of them
hard-coded -- and the incoming configuration, which is no longer tied to
`startConfig`.  The physical/virtual split is decided by `9+zeros+r` against `N` alone:
below it the walking terminator advances by one and `walk N zeros (r+1) = r+1`; at or
above it the source address *is* the boundary blank, the terminator does not move, and
`walk N zeros (r+1) = walk N zeros r = N-9-zeros`.

That the cost stays `roundClock N = 2*N-7` at **every** index is the arithmetic heart of
the slice.  A round splits into four pieces: the counter phase, which scans left over the
blank trail and the unconsumed zeros and right back over both, costing
`2*walk N zeros r + 2*(zeros-r) + 3`; the register walk out and back, costing `2*(r+1)`;
the content carry out and back, costing `2*(N-9-zeros-r)`, which only the physical shape
performs; and six fixed steps.  The two shapes cancel `r` differently.  In the physical
shape `walk = r`, so the counter phase collapses to the `r`-free `2*zeros+3`, and it is
the carry's `-2*r` that cancels the register walk's `+2*r`.  In the virtual shape there
is no carry at all and `walk` is the constant `N-9-zeros`, so the counter phase keeps its
`-2*r` and *that* is what cancels the register walk.  Both shapes take the same six fixed
steps; three of the virtual ones pass through the `qVa`/`qVb`/`qVc` padding, standing at
the positions where the physical shape enters `qClear`, `qCarry` and `qBackCont`.  Either way the
sum is `2*N-7`.  This is why one fixed table can be iterated without a per-round clock:
had the cost depended on `r`, the induction below would have had to carry a sum.

That `round_generic` really is a generalisation and not a parallel claim is pinned in the
surface test: `check_round_generic_subsumes_round_step` derives the landed `round_step`
statement -- the `r = 2 -> r = 3` step out of `startConfig` under `3 <= zeros` and the
round slice's own room -- back out of `round_generic` at `r = 2` applied to the G2p-d
foundation endpoint, under exactly those premises.  The iteration only ever instantiates
`2 <= r`; `r = 1` is inside the statement but produced by nothing here.

`rounds_iterate` is that induction.  Under a matching tag, a decoded `2 <= zeros`, the
bound `2+k <= zeros` and the room every round assumes,
`N+1+zeros < tapeLength (pairLength a m) B`, running the same machine for exactly
`k * roundClock N` steps out of the landed G2p-d `startConfig` reaches the `r = 2+k`
instance of the invariant.  The base case `k = 0` is the retagged foundation endpoint
re-read in this module's address form; the step case composes `run_add` with the private
execution kernel `round_at` at `r = 2+k`, whose public wrapper is `round_generic`.  The bound
`2+k <= zeros` is the work-remaining premise of
every round performed, and the rounds beyond it are not covered.

`register_complete` is the `k = zeros-2` instance and the payoff of the slice: after
exactly `loopClock N zeros = (zeros-2)*roundClock N` steps the register
`[N+1, N+1+zeros]` holds all `zeros+1` digits `registerBit x w zeros j`.
`register_digits` spells the digits out -- digit `0` is the bootstrap's leading `true`,
digit `i+1` is the payload cell `9+zeros+i` read through the blank padding, and
`i < zeros` covers exactly the payload block `[9+zeros, 9+2*zeros)`, "exactly" being its
own conjunct, an iff pinning those source addresses as precisely that block -- so a
truncated payload contributes virtual zeros and the register is the full width-`zeros`
payload behind a leading `true`.  This is register **content** at an exact time.  It is not a
decoded number, not a halting run and not language acceptance: the machine sits in the
non-absorbing `qLoop`, and no theorem here mentions `contentHeader?` or any parsed
header value.

`room_iff` reads the iteration's room premise
`N+1+zeros < tapeLength (pairLength a m) B` as
`zeros <= a+B`.  That is the premise the round slice above recorded as "assumed
nowhere"; a single round at index `r` assumes only `r < a+B`, and at `3 <= zeros` the
iteration premise implies the round's `3 <= a+B`, at `2 <= zeros` the foundation's
`2 <= a+B`.  Those premises are sufficient and used -- each round's trace reaches
`N+2+r` and writes there, the largest such cell over the rounds iterated being
`N+1+zeros` at `r = zeros-1` -- but nothing here proves them necessary: there is no
footprint theorem, and the deferred exhaustion finish has none either, so nothing
claims this to be the room a *complete* loop needs.  Because `qLoop` does not
absorb, every endpoint here is an *exact* time, none may be transported later, and the
slice exports no deadline; there is no first-arrival or strictness direction, and no
converse anywhere.  No clock here counts the steps embedded in `startConfig`.

Nonvacuity is again independent of the endpoint theorems.  Two literal probes identify
the phase-local start configuration for every budget from the landed G2p-d foundation
endpoint theorem alone, then reduce the round machine's own `run` by kernel computation
at `B = 0` across **two** consecutive rounds, invoking no endpoint theorem of this
module.  Both probe words decode to `zeros = 4`, so exactly `zeros-2 = 2` rounds remain
and the payload block is `[13,17)`.  The physical probe (`N = 17`, `roundClock 17 = 27`,
`loopClock 17 4 = 54`) pins round one's head on its physical source `15` with the
`false` there carried in the control as `qClear0`, round one ending in `qLoop` on the
advanced terminator `15` with a `false` appended at `21`, then round two in `qCntMark`
on counter cell `11`, its head on the physical source `16` with the `true` there carried
as `qClear1`, and the final register `[18,22] = true, true, false, false, true`; the two
rounds therefore drive both carried-bit halves of the table.  The truncated probe (`N = 15`,
`roundClock 15 = 23`, `loopClock 15 4 = 46`) pins the virtual schedule at both round
endpoints: the terminator is at `14` after each round and the corresponding appended register
digits are false.  In round two it additionally pins the boundary source `15` and entry through
`qVa`/`qVb`/`qVc`; the final register is `[16,20] = true, true, false, false, false`.
`check_probe_inputs_valid` states separately
that both probe words satisfy the tag and width hypotheses the general theorems assume,
and at the probes' own budget `B = 0` the room hypothesis too, so those theorems are not
about an unsatisfiable premise set.

Deferred: the exhaustion finish -- at `r = zeros` the next round's counter scan finds
the marked cell `7+zeros` and leaves `qLoop` through `qFin`, and that behaviour, `qDone`
and the restoration of the gamma zero field are outside every theorem here -- the loop's
own deadline, a first-arrival/strictness direction, the decrement from `n+1` to `n`, the
all-times clamp/footprint/budget package, and every converse.  The exhaustion
finish, the first-arrival direction and the all-times clamp are discharged for that phase by
the G2p-f slice below (the clamp only because `qDone` absorbs, which `qLoop` does not); a
*length-only* loop deadline -- G2p-f exports persistence only from the width-dependent
`totalClock N zeros` -- the decrement from `n+1` to `n`, the footprint/budget half and every
converse still stand.  G2p-f adds no room premise of its own, and its `payload_exhausted` does
claim this slice's `zeros <= a+B` *sufficient* for a complete loop with the finish included, so the
paragraph above reserving that question holds only for *necessity*.  `zeros = 2` is covered
only degenerately, since `loopClock N 2 = 0` makes `register_complete` a restatement of
the retagged foundation endpoint `startConfig`, and `zeros <= 1` is excluded by the
`2 <= zeros` premise.  No pnp4 bridge
exists for this module, `startConfig` is a phase-local retag of an actual prior run
rather than a composed execution from the raw pair input, and `qDone` is not language
acceptance.  Clock composition, the fixed parser, the checks, advice freedom, `NP`
membership and `ContentVerifierBridge` are out of scope.  It is infrastructure, not
P-vs-NP mainline progress.

The Part A G2p-f `FixedGammaTargetPayloadExhaustion` adds **no new machine** either.  The
round machine's `qCntL` and `qFin` rows already carry the stopping rule; this slice proves
what they do.  `machine_reused` pins the identity of the opened `machine` with
`FixedGammaTargetPayloadRound.machine` and the five rows the phase runs -- leaving the
terminator, scanning the blank trail, the rule, the unmarking sweep and the halt -- while the
full wrappers pin that the new theorems run that opened machine.

The counter carries one mark per consumed source and the gamma zero field has exactly `zeros`
cells, so `r = zeros` *is* exhaustion, and the machine detects it without counting anything.
Out of the `r = zeros` instance of `loopTape B x w zeros zeros` -- G2p-e's `register_complete`
endpoint -- `qLoop` leaves the walking terminator into `qCntL`, `qCntL` scans left over the
blank trail of consumed sources, and the first non-blank it meets is cell `7+zeros`.  At every
index `r < zeros` that cell held an unconsumed gamma zero, `some false`, and the same `qCntL`
row sent the round on through `qCntZ` to mark it; at `r = zeros` it is a consumed mark,
`some true`, and the `qCntL` row for `some true` -- the row the round slices leave unexecuted
over their own bounded segments, which their proofs establish by direct inspection of the
table trace rather than by any exported theorem -- sends the machine into `qFin` instead.
The rule reads one tape cell and nothing else: no width, digit index, address, counter value,
proof term, advice or producer mark occurs in control.

`qFin` then walks back left writing `some false` over every mark, so the field `[8, 7+zeros]`
ends holding exactly what the incoming content tape holds there, and the sweep stops of its own
accord on the tag cell `7`, which a matching tag already holds as `some false`.  That
restoration is the semantic point of the finish: the field the loop used as a counter is handed
back unchanged.  `finishTape` is the endpoint and `finishTape_pins` states both halves of what
it is -- on `[7, 8+zeros)` the incoming `contentTape`, reading `some false`; everywhere else the
incoming invariant untouched, with the consumed sources still blank, the walking terminator
still standing at `8+zeros+termWalk N zeros` and the completed register `[N+1, N+1+zeros]` still
holding its `zeros+1` digits.  So the endpoint is **not** `contentTape`, and nothing claims it
is.

`exhaust_generic` is that run out of an **arbitrary** configuration matching the `r = zeros`
invariant.  Its premises are a matching tag, `gammaZeros? (Fin.append x w) = some zeros`,
`1 <= zeros`, and the three projections of the incoming configuration: six propositional
hypotheses and **no room premise at all**, because the finish only ever moves left from a head
the hypothesis already places inside the tape, so it touches no cell the incoming configuration
does not have.  The cost is exactly `exhaustClock N zeros = termWalk N zeros + zeros + 2`, where
`termWalk N zeros = walk N zeros zeros`: one step off the terminator, `termWalk N zeros`
blank-trail steps, the step that fires the rule, `zeros-1` further unmarking steps, and the
halt.  That clock is neither length-only nor shape-independent -- `2*zeros+2` on a physically
present payload, `N-7` on a truncated one, both pinned by `clock_pins`, which also pins
`exhaustClock N zeros <= roundClock N` under the guard `9+zeros <= N`.  That guard is a
hypothesis of the conjunct and not editorial caution: at `N = 0`, `zeros = 100` the finish
costs `102` while `roundClock 0` truncates to `0`.  It is the one clock of this loop that is
not padded flat: a round had to be, because `rounds_iterate` adds up a sequence of round costs and an
`r`-dependent summand would have forced the induction to carry a sum, while the finish is
performed once and nothing adds it up, so the round's `qVa`/`qVb`/`qVc` padding has no
counterpart here.

Because `qDone` absorbs -- unlike `qLoop`, in which both round endpoints of this loop sit --
this endpoint may be transported forward, and `exhaust_strict` proves both directions available
here: the endpoint holds at every later time, and `qDone` is not
entered at any strictly earlier time, so `exhaustClock` is a proved first arrival.  That
minimality is measured from the `r = zeros` configuration, not from `startConfig`: the G2p-e
rounds carry no strictness theorem, so `qDone`-freeness across the round segment is established
nowhere here -- the two probes below pin a handful of pre-endpoint states only, not the absence
of `qDone` throughout that segment.  `exhaust_schedule` pins the control at every time
of the phase -- `qLoop`, then `qCntL` over the blank trail, then `qFin` from the rule to the
halt, with the head walking monotonically left to `7` -- which together with `exhaust_generic`
names the control at every time up to and including the halt, leaving no time at which a source
or register state could occur.

`payload_exhausted` composes the finish with the G2p-e rounds and is the slice's concrete exact
run: on a matching tag, a decoded `2 <= zeros` and the inherited iteration room
`N+1+zeros < tapeLength (pairLength a m) B` -- four premises -- the same machine run out of the
landed G2p-d `startConfig` for exactly `totalClock N zeros = loopClock N zeros + exhaustClock N
zeros` steps is in `qDone` on the tag cell `7`, its tape is `finishTape B x w zeros`, the gamma
zero field is back to the content tape, and the endpoint persists at every later time.  The
register conjunct is **preservation, not completion**: that `[N+1, N+1+zeros]` holds its
`zeros+1` digits `registerBit x w zeros j` is G2p-e's `register_complete`, and all this slice
adds is that the finish carries it through unchanged.  Nothing decodes those digits, and where
the payload is truncated the digits past it are `registerBit`'s virtual `false`, which no
theorem here calls the payload's value or the intended number.  The room premise is inherited,
sufficient and used; it is not shown necessary, since there is still no footprint theorem, and
the finish itself contributes no room premise.  `totalClock` counts those rounds and this finish
only: not one step that `startConfig` embeds, so it clocks no composed pipeline.

Nonvacuity is again independent of the endpoint theorems.  Two literal probes identify the
phase-local start configuration for every budget from the landed G2p-d foundation endpoint
theorem alone, then reduce the round machine's own `run` by kernel computation at `B = 0` across
both remaining rounds **and** the finish.  Both probe words decode to `zeros = 4`.  The physical
probe (`N = 17`, `loopClock 17 4 = 54`, `termWalk 17 4 = 4`, `exhaustClock 17 4 = 10`,
`totalClock 17 4 = 64`) pins `qCntL` on the last counter mark `11` at step fifty-nine, `qFin` on
`10` at step sixty -- so the rule fired on a mark, not on an unconsumed zero -- `qFin` on `7` at
step sixty-three, and `qDone` on `7` at step sixty-four with cells `7,8,9,10,11` all back to
`some false`, the consumed payload cell `13` blank although its input bit is `true`, the walking
terminator at `16`, and the register `[18,22] = true, true, false, false, true`.  The truncated
probe (`N = 15`, `loopClock 15 4 = 46`, `termWalk 15 4 = 2`, `exhaustClock 15 4 = 8`,
`totalClock 15 4 = 54`) is two steps cheaper.  That gap tracks `N` alone: both probes lie in the
band `9+zeros <= N <= 9+2*zeros`, where the clock is `N-7`, so the pair is no witness of the
clock's dependence on `zeros`.  It pins the same restoration, cell `14` carrying the
terminator's `some true` over an input `false`, and the register
`[16,20] = true, true, false, false, false`, its last two digits the virtual zeros of the
truncated payload.  Both probes run past the endpoint, which exhibits `qDone` absorbing.
`check_probe_inputs_valid` states separately that both words satisfy the tag and width
hypotheses the general theorems assume, and at `B = 0` the room hypothesis too.

`qDone` is an internal endpoint rather than language acceptance, and this module states no pnp4
reader or parser fact.  The reading is done outside pnp3, by the G2p-g companion
`Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetPayloadExhaustionBridge`, which consumes
`payload_exhausted` and identifies every register cell `N+1+j`, `j <= zeros`, with
`(n+1).testBit (zeros-j)` for a decoded `contentHeader? (Fin.append x w) = some (n, consumed)`
and for the target `pr.2.n` of a successful `contentInput?` parse.  Its virtual-tail conjunct is
what settles the truncated case this module leaves open: where the payload cell has left the
word, `registerBit`'s `false` and the decoder's virtual zero are proved to be the same digit.
That companion adds no machine and no clock, carries the same room premise, and claims no
converse and no decrement.

The decrement of the register is now performed on the machine side by the G2q slice below, which
borrows one out of this very endpoint's register cells in a new fixed 7-state table, out of a
phase-local retag of this slice's own run; what that slice does not supply is the identification
of the result with `n`, which needs the G2p-g bridge's `n+1`.  That identification has since been
carried out in pnp4 by the G2r bridge
`Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetRegisterDecrementBridge`, which composes
the two and states, at G2q's endpoint and under G2q's stronger room premise, that every
decremented register cell holds `n.testBit (zeros-j)` -- and for the target `pr.2.n` of a
successful `contentInput?` parse.  It adds no machine, states no converse, and restores no gamma
leading-digit convention.  Deferred here, and still absent from pnp3: that identification, any
reading of the register as
a *number* on the tape (`registerBit` gives content, not a value; the companion's uniqueness
conjunct is arithmetic about those digits, not a decoding step the control performs), a
footprint/budget theorem, every converse -- nothing says
that `qDone` at `totalClock N zeros`, or any endpoint cell, implies anything about `zeros` --
first arrival measured from `startConfig`, the degenerate widths, and a malformed-gamma
branch.  Of those widths `zeros = 0` is excluded from `exhaust_schedule`, `exhaust_generic`
and `exhaust_strict` by their `1 <= zeros` premise, which the tape-shape theorem
`finishTape_pins` does not carry, while `zeros = 1` satisfies those three but is produced by
nothing here, since `payload_exhausted` needs `2 <= zeros`.  `zeros = 2` is covered, with
`loopClock N 2 = 0` making
`payload_exhausted` the finish applied directly to the retagged foundation endpoint.  `qDone` is
`machine.accept` of a machine started here from a phase-local retag of an actual prior run
rather than from `initialConfig` on a raw pair input, so reaching it is neither halting of a
composed machine nor language acceptance; the module states no `accepts`, no `AcceptsAt` and no
language membership.  Clock composition, the fixed parser, the checks, advice freedom, `NP`
membership and `ContentVerifierBridge` are out of scope.  It is infrastructure, not P-vs-NP
mainline progress.

The Part A G2q `FixedGammaTargetRegisterDecrement` is the first slice of this loop to add a
**new machine**: a fixed 7-state, 21-row table, the first new table since the G2p-d round
machine.  A new table was unavoidable rather than convenient.  The G2p-d/G2p-e/G2p-f loop only
ever *appends* a digit to the target register and marks a consumed gamma zero, and no row of
its 22-state table performs a borrow -- it has no state that rewrites a register cell right to
left as a function of that cell alone.  `table_and_resource_pins` pins all 21 rows literally
(seven states against the three symbols), with `machine.stateCount = 7`, the three
distinguished states, and `per_step_budget_independent` for the fact that the public
`machine.step` never consults the budget and agrees with `raw` on every row.  The surface test
restates the same 21 rows independently in `check_table_rows`, so a silent table change breaks
the test rather than passing through an alias.

Write `N = a+m`.  The incoming configuration is G2p-f's endpoint: halted on the tag cell `7`
with the tape `finishTape B x w zeros`, whose shape is G2p-f's `finishTape_pins` -- the restored
gamma zero field `[7, 8+zeros)` reading `some false`, the blank terminator trail, the walking
terminator at `8+zeros+termWalk N zeros`, the content untouched from there, the boundary blank
at `N`, and the completed target register `[N+1, N+1+zeros]` holding its `zeros+1` digits
`registerBit x w zeros j`.  On a decoded header those digits are the digits of the *encoded*
gamma integer `n+1`, which is what the G2p-g pnp4 bridge states on the parser side; this module
states nothing about `n`, about a header, or about a parse.  This phase subtracts one from that
register, in place, by the schoolbook borrow.

Everything is symbol-driven, and that is the point of the design.  No width, digit index,
register address, counter, proof term, advice or producer mark occurs in the table: every branch
is decided by the one symbol under the head.  `qStart` leaves the tag cell.  `qSeekTerm` runs
right over everything that is not `some true`, and since the restored gamma zeros are
`some false` and the consumed trail is blank, the first `some true` it meets is the walking
terminator; that sends it into `qSeekGap`.  `qSeekGap` runs right over every non-blank content
cell, so the first blank it meets is the boundary cell `N`; that sends it into `qRegEnd` on the
register's leading digit `N+1`.  `qRegEnd` runs right over the register, so the first blank past
it is `N+2+zeros`, and the one left step from there lands on the least significant digit
`N+1+zeros`.  The register's own right end is therefore found by that blank and by nothing else,
which is the one cell of room this phase needs beyond G2p-f's.  `room_iff` reads that cell two
ways: `N+2+zeros < tapeLength (pairLength a m) B` is exactly `zeros+1 <= a+B`, one more than
G2p-f's `zeros <= a+B`, and it *implies* G2p-f's own premise `N+1+zeros < tapeLength …`, so the
composite run below carries this single room premise and no other.  Sufficient and used; there
is still no footprint theorem here, so it is not shown necessary.

`qBorrow` then reads a digit and does the whole of the arithmetic in two rows: `some false`
becomes `some true` and the head moves one cell left; `some true` becomes `some false` and the
machine halts in the absorbing `qDone` on that cell.  So the run of `false` digits at the low
end is flipped, the `true` that stops it is cleared, and every higher digit is left alone --
which is subtraction of one.  The borrow never walks off the register's left end because digit
`0` is the bootstrap's leading `true`: `borrow_pins` produces the stopping index `borrow x w
zeros` from G2p-d's `registerBit_pins`, and states three conjuncts: the bound
`borrow x w zeros <= zeros`, which is why the sweep stays inside the register, and then that the
digits below the stopping index are `false` and that the digit it stops on is `true`, which are
exactly the symbol-level facts the two `qBorrow` rows read.  `borrow` is a statement-level
quantity computed from the digits, not advice: no row of the table mentions it, and the machine
finds the same cell by reading symbols.

`decClock N zeros d = N+zeros+d-3` is the exact cost at borrow length `d`, and `clock_pins`
decomposes it under the decoded-width guard `9+zeros <= N` as `(N-7) + 1 + (zeros+1) + 1 + d +
1`: `N-7` steps from the tag cell to the boundary blank, one step onto the register, `zeros+1`
steps to the blank past its right end, one step back onto the least significant digit, `d`
borrow steps, and the halt.  It is not length-only, and in two ways: it depends on the decoded
width, and through `d` it depends on the stored digits.  `deadline N = 3*N` is the length-only
bound it meets at every decoded width and every borrow length, and `clock_pins` states that in
the guarded form `9+zeros <= N -> d <= zeros -> decClock N zeros d <= deadline N`; both guards
are hypotheses of the conjunct and not editorial caution, the second being `borrow_pins`'s bound
at `d = borrow x w zeros`.

The handoff consults no decoded data either.  `startConfig` retags the G2p-d round machine's run
at the **length-only** time `priorDeadline N = 3*(N*N)`, and `handoff_exact` pins that retagging
replaces the control and nothing else -- same head, same tape.  `prior_covers` is the arithmetic
that makes the handoff legitimate: at every decoded width `9+zeros <= N`, G2p-f's exact endpoint
time `totalClock N zeros` is at or before `priorDeadline N`, so G2p-f's own all-times clamp
identifies the retagged configuration with the endpoint `payload_exhausted` describes.  That
bound is the *length-only* loop deadline the G2p-e/G2p-f loop itself never stated, and it is
worth being precise about what it is not: it bounds that loop's own phase-local clock and
nothing else, it counts no step that the G2p-d `startConfig` embeds, and `decClock` counts the
steps of this phase alone.  Nothing here composes clocks across phases.

`decTape` is the endpoint tape and `decBit` the endpoint digit: above the borrow's stopping digit
the incoming digits survive, the stopping digit `zeros-d` is cleared, and the `d` digits below it
are set.  `decTape_pins` states that in five conjuncts -- every register cell `N+1+j` holds
`decBit x w zeros d j`; every cell outside `[N+1, N+1+zeros]` is the incoming `finishTape` cell;
the stopping cell is `some false`; the cells under it are `some true`; and below the stopping
digit the cell is the incoming `registerBit`.  It is a statement about the tape function and
carries no claim about which cells the machine visited.

`decrement_generic` is the run out of an **arbitrary** configuration matching that endpoint, on
nine propositional hypotheses: a matching tag, a decoded width, the room premise, a borrow length
`d` with `d <= zeros` together with the two symbol-level facts the borrow rule reads, and the three
projections of the incoming configuration.  After exactly `decClock N zeros d` steps the machine is
in `qDone` on the cell `N+1+zeros-d` the borrow stopped on, with the whole tape equal to
`decTape B x w zeros d`.  `d` enters through those three hypotheses only, and no row of the table
mentions it.  `decrement_schedule` pins the control and the head at
every time of the phase -- `qStart`, then `qSeekTerm` to the walking terminator, then `qSeekGap`
to the boundary blank, then `qRegEnd` to the blank past the register, then `qBorrow` to the halt,
with the head monotonically right to `N+2+zeros` and then monotonically left -- which together
with `decrement_generic` names the control at *every* time up to and including the halt, so no
other state can occur there and `qReject` is entered nowhere in that range -- nor later, since the
clamp below freezes the configuration.  Its head conjuncts cover every time strictly before the
halt; the halting step is a `.stay`, and `decrement_generic` gives the head there.
`decrement_strict` proves both directions available here: `qDone` is not entered at any strictly
earlier time, and because `qDone` absorbs the endpoint holds at every later time -- in particular
at the length-only `deadline N`, which `clock_pins` puts at or past `decClock` under this
theorem's own hypotheses.  That minimality is measured from
*this* configuration, not from the G2p-d `startConfig` of the previous phase, whose round segment
carries no strictness theorem in this loop.

`register_decremented` is the slice's concrete exact run: on a matching tag, a decoded
`2 <= zeros` and the room premise -- four hypotheses -- the phase-local `startConfig` reaches
`qDone` after exactly `decClock N zeros (borrow x w zeros)` steps of this machine, on the stopping
cell, with tape `decTape B x w zeros (borrow x w zeros)`, every register cell `N+1+j` holding
`decBit x w zeros (borrow x w zeros) j`, every cell outside the register still the incoming G2p-f
endpoint cell, and the endpoint persisting at every later time.  The `2 <= zeros` premise is
inherited from G2p-f's `payload_exhausted`, so `zeros <= 1` stays outside the proved surface here
as it does there.

What the decrement *means* is deliberately kept apart from what it *does*.  `sub_one_bits` and
`decBit_sub_one` are arithmetic about `Nat`: no machine, no tape, no parser and no codec occurs
in either.  `sub_one_bits` says that if `v`'s bits below `d` are `false` and its bit `d` is
`true` -- exactly what the two `qBorrow` rows read off the register -- then `v-1` sets every bit
below `d`, clears bit `d` and leaves every higher bit alone.  `decBit_sub_one` transports that to
the register: on an **arbitrary** natural `v` whose bit `zeros-j` is register digit `j` at every
`j <= zeros` and which has no bit above `zeros`, the endpoint digits are the bits of `v-1` at the
same positions, and `v-1` has no bit above `zeros` either, so those `zeros+1` cells carry all of
its digits.  Only the second conjunct uses the no-high-bits hypothesis; the borrow never reaches
past digit `zeros`, so the low digits of `v-1` do not depend on the high bits of `v`.  No theorem
of this module supplies such a `v`.  The two hypotheses are precisely what the G2p-g bridge's
`exhaustion_register_digits` proves for `v = n+1` on a decoded header, and composing the two is a
pnp4 step this slice does not take; nothing here mentions `contentHeader?`, `contentInput?`, or a
parsed target.  The pnp4 G2r bridge
`Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetRegisterDecrementBridge` has since taken
that step, instantiating this `v` at `n+1` so that `v-1` is the decoded target `n`; it changed no
declaration here, and this module still states nothing about a header or a parse.

Nonvacuity is again independent of the endpoint theorems.  Two literal probes identify the
phase-local start configuration for every budget using only G2p-f's `payload_exhausted` and this
module's `prior_covers` -- an arithmetic statement about clocks that executes nothing -- and then
reduce this machine's own `run` by kernel computation at `B = 0`.  The tag is `10110010` and both
words decode to `zeros = 4`, so the register is five digits wide, and the two probes exercise the
two shapes of the borrow.  The physical probe (`N = 17`, `termWalk 17 4 = 4`, walking terminator
at `16 = N-1`, `totalClock 17 4 = 64`, `priorDeadline 17 = 867`, `deadline 17 = 51`) has
`borrow tag physWord 4 = 0` and `decClock 17 4 0 = 18`: `qSeekTerm` stops on the terminator at
step nine, `qSeekGap` is on the boundary blank `17` at step ten, `qRegEnd` enters the register at
`18` at step eleven and leaves it at the blank `23` at step sixteen, `qBorrow` is on the least
significant digit `22` at step seventeen, and since that digit is `some true` the borrow stops at
once: step eighteen is `qDone` on `22`, with `[18,22]` reading `11001` before and `11000` after.
The truncated probe (`N = 15`, `termWalk 15 4 = 2`, terminator at `14`, `totalClock 15 4 = 54`,
`priorDeadline 15 = 675`, `deadline 15 = 45`) has `borrow tag virtWord 4 = 3` and
`decClock 15 4 3 = 19`: the register `[16,20]` ends in three `false` digits, two of them the
virtual zeros of the truncated payload, so `qBorrow` walks `20, 19, 18` and stops on `17`, and
step nineteen is `qDone` on `17` with `[16,20]` reading `11000` before and `10111` after.  Those
bit patterns are cell contents read from the register's leading cell; nothing in the probes claims
them to be a decoded value.  Both probes sample a cell outside the register (`7` and `16`
respectively for the physical one, `14` for the truncated one) and run past the endpoint, which
exhibits `qDone` absorbing.  `check_probe_inputs_valid` states separately that both words satisfy
the tag and width hypotheses the general theorems assume, and at `B = 0` the room hypothesis too,
and `check_clock_values` pins the literal clocks and borrow lengths.
`check_decBit_sub_one_instance` shows the arithmetic's hypotheses are satisfiable: the truncated
probe's five register digits are the bits of `24` and the endpoint digits are then the bits of
`23`.  That `24` is a **hand-written literal** chosen to match the digits; no theorem of this
slice or of pnp3 produces it from a parse, which is exactly the deferred pnp4 step.

Deferred by this module, and deliberately not claimed in it: that pnp4 bridge, and with it every
connection to `contentHeader?`, to `contentInput?`, or to a parsed target -- the bridge has since
landed as G2r, outside pnp3, with no change to any declaration here; a footprint or budget
theorem, so
the room premise is sufficient and used but not shown necessary; every converse -- nothing says
that `qDone` at `decClock`, or any endpoint cell, implies anything about `zeros`, about the borrow
length, or about the incoming digits; a malformed-gamma branch; first arrival measured from the
G2p-d `startConfig` of the previous phase rather than from this one; the handoff of this endpoint
to a next phase; and any restoration of the gamma leading-digit convention.  That last one is a
real gap rather than a formality: when the register holds exactly `2^zeros` the borrow clears
digit `0`, so the decremented register need not begin with a `true`, and nothing here
re-establishes the invariant the gamma encoding relies on.  `qDone` is `machine.accept` of a
machine started here from a phase-local retag of an actual prior run rather than from
`initialConfig` on a raw pair input, so reaching it is neither halting of a composed machine nor
language acceptance; the module states no `accepts`, no `AcceptsAt` and no language membership.
Clock composition, the fixed parser, the checks, advice freedom, `NP` membership and
`ContentVerifierBridge` are out of scope.  It is infrastructure, not P-vs-NP mainline progress.

The Part A G2s-a `FixedGammaTargetUnaryCountdown` is the second slice of this loop to add a
**new machine**: a fixed 11-state, 33-row table, the second new table since the G2p-d round
machine.  A new table was again unavoidable.  G2q's 7-state table halts in the absorbing `qDone`
the moment the borrow stops, so no run of it can perform a second subtraction, and none of its
states walks a tally lane; `table_and_resource_pins` pins all 33 rows literally (eleven states
against the three symbols) with `machine.stateCount = 11`, the three distinguished states, and
`per_step_budget_independent`, and the surface test restates the same 33 rows independently in
`check_table_rows`, so a silent table change breaks the test rather than passing through an alias.

Write `N = a+m`.  The incoming configuration is G2q's endpoint, retagged: the target register
`[N+1, N+1+zeros]` decremented in place, with the digit the borrow stopped on cleared at
`N+1+zeros-d`, the `d` digits below it set, the digits above it untouched, and the head on the
cleared cell.  That is this phase's **entry ABI**, stated in the module docstring and pinned by
`handoff_exact`: `qStart` on a `some false` at `N+1+zeros-d`, exactly `d` cells of `some true` to
its right, the separator blank at `N+2+zeros`, and a blank lane beyond it.  Any phase inserted
before this machine -- the fence below is the one such phase now foreseen -- must end on that ABI,
and when one lands, `startConfig`, `handoff_exact`, `first_round` and both handoff probes are
re-targeted at it.  Exporting the entry as the *generic* `entry_generic` and pinning the ABI is what
keeps that re-targeting to the cost of one handoff derivation.

`startConfig` is a phase-local retag of an **actual** G2q run taken at G2q's own length-only
`deadline (a+m) = 3*(a+m)`; `first_round` identifies it with an explicit configuration through the
all-times clamp of G2q's `register_decremented` and the fifth conjunct of G2q's `clock_pins`, which
bounds `decClock` by that deadline at every decoded width and borrow length.  No decoded data enters
the handoff, and the clocks below count none of the steps `startConfig` embeds.

`loopTape B x w zeros v r` is the tape of the countdown: the G2q/G2p-f content below the boundary
blank `N`, the register `[N+1, N+1+zeros]` holding the `zeros+1` digits of `v` with digit `zeros-j`
at cell `N+1+j`, the separator blank at `N+2+zeros`, `r` marks in the lane
`[N+3+zeros, N+3+zeros+r)`, and blanks beyond.  `loopTape_pins` places every one of those cells with
**no hypothesis at all**, and `loopTape_zero_eq_decTape` identifies the zero-mark tape with G2q's
`decTape` on any `v` whose digit `zeros-j` is G2q's `decBit ... j` at every `j <= zeros`.  Only that
identification and `first_round` carry the tag and the width, because `decTape` falls back to the
finish tape at `N` and past the register and only a decoded width makes those cells blank; the three
generic run theorems carry neither, because the machine never reads a cell left of `N` and
`loopTape` places that blank explicitly.

The round is symbol-driven throughout.  `qSeekSep` runs right over the set digits to the separator
blank and `qLoop` steps left off it onto the least significant digit; `qBorrow` flips the low run of
`false` digits to `true` and clears the `true` that stops it, which is subtraction of one, or -- when
every digit is `false` -- walks off the register's left end onto the boundary blank and hands over
to `qFin`; `qPadL` walks left to that same boundary blank and `qPadR` right to the separator;
`qRunEnd` runs right over the marks already in the lane and writes one more on the first blank; and
`qBackRun` walks back over them to the separator and re-enters `qLoop`.  No width, digit index,
register address, mark count, clock, counter, proof term, advice or producer mark occurs in any row.
The `qPadL`/`qPadR` pair is the whole reason `roundClock zeros r = 2*zeros+2*r+7` is closed-form:
the borrow's own length cancels against the padding walk, so the round costs the same whatever the
stored digits are.  `entry_generic` costs exactly `d+2` and writes nothing; `zeroClock zeros =
2*zeros+5` is the exact exhaustion cost and leaves the tape exactly as it found it, marks included;
`firstClock zeros d = 2*zeros+d+9` is the entry plus the first round, which `clock_pins` states as
`(d+2) + roundClock zeros 0`.  The statement-level `lowRun` is read off the value, is private and
structural in a fuel bound rather than a search, and no row of the table mentions it -- the machine
finds the same cell by reading symbols.  `room_iff` reads the lane as one cell per mark:
`N+3+zeros+r < tapeLength (pairLength a m) B` iff `zeros+2+r <= a+B`, and the `r = 0` room implies
the entry's and the exhaustion's.  It is sufficient and used, never shown necessary.

None of this makes `qLoop` a deadline.  `qLoop` is not terminal, so each `qLoop` endpoint holds at
its exact time and says nothing about any other time; only the exhaustion's `qDone` persists, and
persistence is all `exhaust_generic`'s last conjunct claims.  Nothing here says `qDone` is entered
for the **first** time at `zeroClock zeros`, and no such theorem is proved.

**The fence, and the fence policy.**  The tally lane is uncapped in this slice.  A register too
large for the budget therefore runs `qRunEnd` off the end of the tape and sticks there, which is a
timeout and so neither verdict.  Capping it needs an executed `some false` cell in the lane at a
length-derived offset `F`, laid by its **own** fixed phase inserted between G2q and this machine,
and that phase must end on the entry ABI above; the `qRunEnd`-on-`some false` row is the reject hook
it will use, and it is pinned and deliberately unexercised here.  The iteration slice G2s-c may not
open until this policy is recorded here and in `STATUS.md`, which this entry does: G2s-c's loop
theorem must take `F` as a parameter and its room premise must be `zeros+2+F <= a+B`.  The claim
that `F = N` is sound rests on `contentAccepts_parsed_tableLen_le_of_header_target_wide`
(`pnp4/Pnp4/Frontier/ContractExpansion/ContentTargetSizeBound.lean`), which is codec-specific and covers only the wide case; the plan
must derive it or replace it before G2s-c opens.

**Reconciled by G2u.**  Those are two requirements about two different objects, and they read as one
policy only by accident of being written in one paragraph.  The iteration slice, landed below as
G2u, satisfies the first literally and leaves the second untouched.  G2u's loop theorems take `F` as
a parameter of the *statement* and carry the room premise `zeros+2+F <= a+B` verbatim; they run on
the unchanged canonical `loopTape`, and no cell of that tape is a cutoff.  They are **canonical
bounded execution lemmas**, not execution with an installed cutoff, and they are not claimed to
survive one: an installed `some false` at `N+3+zeros+F` is not a `loopTape` -- `loopTape` is blank
there -- so the G2u execution theorems would have to be re-proved against that tape, and nothing in G2u is
evidence that it can be.  The executed-fence requirement therefore stands unchanged and
undischarged for the fenced machine a later phase must build; it is not a precondition of lemmas
that install nothing.  G2u's production statements leave `F` abstract; its tests use literal
budgets. No general `F = N` bound is claimed by G2u.

The `F = N` half of that obligation has since been supplied separately by G2w-a, without changing
this module: `contentSemanticAccepts_parsed_target_le_pair_length` derives `pr.2.n <= a+m` for
**accepted** words at the concrete `treeCircuitWitnessCodec (thresholdPoly k)`, covering both the
wide and narrow cases.  It remains codec-specific and conditional on acceptance -- parser success
alone still bounds no target -- and installs nothing, so the executed-fence half remains open.

Deferred by this module, and deliberately not claimed in it: the iteration itself; the fence phase;
the pnp4 bridge G2s-b, and with it every connection to `contentHeader?`, to `contentInput?` or to a
parsed target -- `v` is universally quantified here, the probes' `24` and `23` are hand-written
literals, and no theorem of this slice or of pnp3 produces either from a parse; a footprint or
budget theorem, so no room premise is shown necessary; every converse -- nothing says that `qLoop`,
that `qDone`, or that any endpoint cell implies anything about `zeros`, about `v` or about the
incoming digits; a malformed-gamma branch, since G2q characterises no non-`qDone` endpoint to route;
and any restoration of the gamma leading-digit convention, which G2q already destroyed when the
register held exactly `2^zeros` and which this phase destroys further at every round.  The lane
holds `r` marks: calling it the target in unary would be a claim about a decoded value, and nothing
here decodes anything.  `qDone` is `machine.accept` of a machine started from a phase-local retag of
an actual prior run rather than from `initialConfig` on a raw pair input, so reaching it is neither
halting of a composed machine nor language acceptance; the module states no `accepts`, no
`AcceptsAt` and no language membership.  Clock composition, the fixed parser, the checks, advice
freedom, `NP` membership and `ContentVerifierBridge` are out of scope.  It is infrastructure, not
P-vs-NP mainline progress.

The pnp4 bridge (G2s-b above) has since landed, as G2t
`Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetUnaryCountdownBridge`.  It instantiates this
slice's `v` at the decoded target `n`, using the G2r bridge's decremented register digits and `3<=n`,
which gives both `2<=zeros` and `1<=v`, so that the first round's endpoint register holds `n-1` with one mark in the lane,
and it restates the room premise as `2*(n+1) < 2^(a+B)` on a decoded header.  It changed no
declaration here, added no machine, and took neither the iteration nor the fence: this module still
states nothing about a header, a parse or a decoded value, and `v` is still universally quantified
here.

The Part A G2u `FixedGammaTargetUnaryCountdownIteration` is the iteration the G2s-a entry above
deferred, and it adds **no machine and no table row**: every step it runs is G2s-a's fixed
11-state, 33-row table, run for longer.  Write `N = a+m` and `S = N+2+zeros` for the separator
blank.  Three public execution theorems and three clocks, all composing landed ones.

`roundsClock zeros r k = k*k + k*(2*zeros+2*r+6)` is the closed form of
`sum_{i<k} roundClock zeros (r+i)`, written so that no `Nat` subtraction occurs anywhere;
`drainClock zeros r v = roundsClock zeros r v + zeroClock zeros` adds the exhaustion and
`fullClock zeros d v = (d+2) + drainClock zeros 0 v` the entry.  `rounds_clock_pins` pins all three
closed forms, the recurrence
`roundsClock zeros r (k+1) = roundClock zeros r + roundsClock zeros (r+1) k` that drives the
induction, `roundsClock zeros r 1 = roundClock zeros r`, and
`fullClock zeros d 1 = firstClock zeros d + zeroClock zeros`, which is the exact statement that this
slice's one-round case is G2s-a's `first_round` followed by G2s-a's exhaustion.  `high_iff_lt` is
the one piece of new arithmetic: "`v` has no digit above `zeros`" and "`v < 2^(zeros+1)`" are one
condition, which is what lets the decrement be taken `k` times without re-deriving the bound each
round.

`iterate_generic` runs `k` rounds out of an arbitrary `qLoop` configuration on `S` whose register
holds `v` and whose lane holds `r` marks, in exactly `roundsClock zeros r k` steps, and leaves
`qLoop` on `S` with the register holding `v-k` and `r+k` marks -- the same canonical `loopTape`, so
its endpoint is again an entry point of the same theorem, which is the whole reason one induction
suffices.  Two hypotheses are load-bearing and neither is decorative.  `k <= v` is what keeps every
one of those rounds a subtraction rather than an exhaustion: a round that meets a register whose
`zeros+1` cells are all `false` runs, by G2s-a's own `exhaust_generic`, to the absorbing `qDone`
instead of borrowing, so at `0 < k` the conclusion fails in state and tape.  The width hypothesis
`forall b, zeros < b -> v.testBit b = false` is what ties the abstract `v` to the `zeros+1` digits
the register physically holds: at `zeros = 2` and `v = 8` those three cells hold `8.testBit 2`,
`8.testBit 1` and `8.testBit 0`, all `false`, so `loopTape` there is literally the all-`false`
register `exhaust_generic` consumes and the machine again exhausts.  Both failures land in `qDone`
on the *same* separator cell, so neither is a head mismatch.

`drain_generic` takes `k := v`, so the register reaches zero and G2s-a's `exhaust_generic` fires:
after exactly `drainClock zeros r v` steps the machine is in `qDone` on `S` with an all-`false`
register and `r+v` marks, and that endpoint persists.  Persistence is all the last conjunct claims:
`qDone` absorbs, and no theorem says it is entered for the **first** time at `drainClock`.  There is
no `1 <= v` hypothesis -- at `v = 0` no round runs and the exhaustion fires at once.

`register_drained` is the concrete exact run: not an arbitrary configuration but the landed
phase-local `startConfig B x w`, the *actual* G2q machine retagged at G2q's own length-only
`deadline (a+m)`.  It re-derives G2s-a's `first_round` entry identification -- the portion that does
not use positivity -- then composes `entry_generic` with `drain_generic` at `r = 0`.  Out of that
configuration the machine *enters* `qLoop` on `S` after exactly `d+2` steps with the register
holding `v`, and after exactly `fullClock zeros d v` steps is in `qDone` on that same cell with
every register cell `some false`, exactly `v` marks in `[N+3+zeros, N+3+zeros+v)`, blanks beyond,
and the endpoint persisting.  Its hypotheses are G2s-a's `first_round` hypotheses with `1 <= v`
dropped and the room split into `v <= F` and `zeros+2+F <= a+B`.  `v = 0` is a legitimate case of
`drain_generic`, but under `2 <= zeros` it cannot inhabit this theorem's digit hypotheses, so no
concrete zero-target coverage is claimed.

`lane_room` is the room the parameter `F` buys: from `r+k <= F` and `zeros+2+F <= a+B` every round
of the iteration, and the exhaustion, have their own room, and one cell past the last mark is
reserved besides.  It is **sufficient and used, never shown necessary**, and it is not even the
tightest sufficient condition: it reserves exactly the cell an installed cutoff would occupy, so it
can fail on a budget where the canonical unfenced drain still completes.  The surface test's
`check_below_room_drain_probe` exhibits one -- at `a = m = zeros = 0`, `v = F = 1`, `B = 2` the
condition reads `3 <= 2` and fails, while `drainClock 0 0 1 = 12` steps reach `qDone` on the
separator blank with the register cleared and one mark laid.  No footprint or budget theorem exists
here, so no room premise of any slice is shown necessary and none is claimed.

The three execution probes independently reduce the countdown runs.
`check_drain_probe` drains a hand-written five-digit register holding `3` at `zeros = 4`, `B = 1` in
`drainClock 4 0 3 = 64` steps to `qDone` on `23` with `[18,22]` all `some false`, marks at `24`,
`25`, `26` and a blank at `27`, with step `80` showing the clamp; `check_start_iterate_probe` runs
two rounds out of the **actual** `startConfig 0 tag physWord` at `2 + roundsClock 4 0 2 = 34` steps
and pins the second mark at `25`; `check_register_drained_instance` inhabits the capstone's seven
hypotheses at the hand-written literal `24` with `F = 24`, `B = 22`, and
`check_register_drained_literal_endpoint` derives the capstone's endpoint there at
`fullClock 4 0 24 = 927`.

Deferred by this slice, and deliberately not claimed: the **fence phase** itself -- the lane is
still uncapped in the machine, a register too large for the budget still runs `qRunEnd` off the end
of the tape and sticks, which is a timeout and so neither verdict, and the `qRunEnd`-on-`some false`
row stays pinned and unexercised; any **pnp4 bridge**, and with it every connection to
`contentHeader?`, to `contentInput?` or to a parsed target, since `v` is universally quantified here
and no theorem of pnp3 supplies one; every **converse**; **first arrival**; a **footprint or budget
theorem**; a malformed-gamma branch; and any restoration of the gamma leading-digit convention.
The lane holds `v` **marks**, where `v` is the parameter whose
register digits are *hypothesised* -- calling them the target in unary would be a claim about a
decoded value, and no theorem here decodes a register, executes a parser or produces a `v` from a
parse.  `qDone` is `machine.accept` of a machine started from a phase-local retag of an actual prior
run rather than from `initialConfig` on a raw pair input, so reaching it is phase-local acceptance:
neither halting of a composed machine nor raw-input language acceptance, and the module states no
`accepts`, no `AcceptsAt` and no language membership.  Every clock here counts the steps of this
phase alone -- not one of the steps `startConfig` embeds.  Clock composition with earlier phases,
the fixed parser, the checks, advice freedom, `NP` membership and `ContentVerifierBridge` are out of
scope.  It is infrastructure, not P-vs-NP mainline progress.

The pnp4 bridge deferred above has since landed, as G2v
`Pnp4.Frontier.ContractExpansion.ContentFixedGammaTargetUnaryCountdownIterationBridge`.  It
instantiates this slice's `v` at the decoded target `n`, using the G2r bridge's decremented register
digits and `3<=n` for the `2<=zeros` this slice inherits, and it recovers the canonical width
`gammaZeros n` from the physical one before rewriting `lane_room` at that width, so the whole drain
runs on the actual parsed target.  Its companion
`Pnp4.Frontier.ContractExpansion.ContentCountdownLinearCap` supplies a value for `F` from *content
acceptance* -- not from parser success, which bounds no target -- so that `F := a+m` becomes
legitimate for accepted words.  G2w-b, in that same pnp4 module, then supplies a value for `B` as
well, at `polyClock 3 (pairLength a m)`, deriving both the room and `fullClock zeros d n <= B` from
its three hypotheses *jointly* -- the successful parse, the Boolean acceptance and `3 <= pr.2.n` --
rather than from acceptance alone, and running the drain to exactly `B` steps through this slice's
own persistence conjunct; the derived room is sufficient only, and no budget is shown necessary.
`polyClock` occurs there as an arithmetic value only, and no `DecidesWithin`, `UniformP` or runtime
statement is made about this machine.  None of them changed a declaration here, none added a machine,
and **none took the fence**: the executed-fence requirement recorded above stands unchanged, the lane
is still uncapped in this machine, no cutoff cell is laid anywhere, `F` is still a parameter of every
statement here, and this module still states nothing about a header, a parse or a decoded value.

The Part A G2x `SequentialComposition` is the generic half of the first **executed** handoff of
this chain, and it imports only `Machine`.  `UniformTM.seq M₁ M₂` has `M₁.stateCount +
M₂.stateCount` states -- `M₁`'s at their own indices (`seqLeft`), `M₂`'s shifted past them
(`seqRight`) -- and its raw table is the disjoint union of the two public step functions with every
`M₁` row **routed** through `seqRoute`: a target `M₁.accept` becomes `M₂.start` *in that same
transition*, a target `M₁.reject` becomes the composed reject, every other target stays left.  This
is the routed-edge handoff of the P2-3cB2 parser/verifier constructor above with the hard-coded left
component made generic, and as there the handoff costs **zero** steps; routing inspects a row's
target state and nothing else, so `M₁.seq M₂` is a fixed table as soon as `M₁` and `M₂` are.
The composed start is routed too: `seq_initialConfig` identifies its `initialConfig` with `M₁`'s
routed configuration, so a terminal `M₁.start` hands over at time zero.  `seqLeft M₁.accept` and
`seqLeft M₁.reject` are dead states: no routed row or start targets them.  `seq_pins` pins the state
count, the distinguished states, the two injections, their disjointness and the three routing cases;
`seq_step_left`, `seq_step_right` and `seq_step_eq_rawStep` pin every row.  `seq_run_right` runs
`M₂` out of any right-embedded configuration, with no hypothesis.  `seq_run_left` runs `M₁` out of
a routed embedding up to `T`, provided `M₁` does not accept strictly before `T`; an `M₁` rejection
needs no hypothesis, since both machines absorb it.  `seq_handoff` composes them: if `M₁` accepts
**for the first time** at `T`, the composed run at `T + s` is the `M₂` run of `s` steps out of
`M₂.start` on the head and tape `M₁` left.  First arrival is load-bearing and is not a persistence
fact -- had `M₁` accepted earlier, the routed edge would have fired earlier and `M₂` would have run
longer -- which is the reason a proof-level retag at a deadline was never a substitute for it.
`seq_reject_handoff` needs no first-arrival hypothesis.  The module states nothing about any input,
clock or budget and proves no `AcceptsAt`, `DecidesWithin`, `UniformP`, `VerifiesRelation` or
language-membership fact about a composed machine: reaching `(M₁.seq M₂).accept` is reaching
`M₂.accept` inside the composed control.

The Part A G2x `FixedGammaTargetDecrementCountdown` is that combinator applied once, and it adds
**no table row**: `machine` is `FixedGammaTargetRegisterDecrement.machine.seq
FixedGammaTargetUnaryCountdown.machine`, G2q's 7-state, 21-row table on the block `[0, 7)` and
G2s-a's 11-state, 33-row table on `[7, 18)`, one closed 18-state, 54-row table.  G2q's
`qBorrow`-on-`some true` row, which targets G2q's absorbing `qDone`, is routed to the countdown's
`qStart` at index `7`; so the composed machine hands over the moment the borrow stops, on the cell
it stops on, with the tape G2q leaves, which is exactly the entry ABI recorded in the G2s-a entry
above.  `startConfig` is G2q's own `startConfig` routed into the composed control -- still the
retagged *actual* G2p-f endpoint, so still a phase-local retag of every earlier phase -- and
`composedClock N zeros d v = decClock N zeros d + fullClock zeros d v`.

`handoff_exact` is the executed handoff.  On a matching tag, a decoded `2 <= zeros` and G2q's room,
with `T = decClock N zeros (borrow x w zeros)`: the composed run is G2q's run, routed, at every
time up to `T`; the composed control is in neither verdict before `T`; at exactly `T` the composed
configuration **is** the countdown's landed `startConfig B x w` re-embedded; and every later step is
a countdown step out of it.  The identification rests on G2q's `decrement_strict` -- `qDone` is
entered for the *first* time at `T` -- and on G2q's persistence from `T` to its deadline `3N`, at
which G2s-a's `startConfig` retags.  The switch time is `T`, not `3N`: a running composed machine
cannot wait for a length-only deadline, and describing it as switching at `3N` would credit the
countdown with `3N - T` steps it had already taken.  `decrement_countdown_drained` then runs G2u's
`register_drained` on top, under G2u's seven hypotheses unchanged: at exactly `composedClock` the
composed machine is in its accept, the countdown's `qDone`, on the separator blank with the register
cleared, `v` marks laid and blanks beyond, persisting.  `v` is universally quantified here and
nothing in pnp3 supplies it.  The surface test's `check_handoff_probe` identifies the actual
`startConfig 0 tag physWord` with an explicit configuration -- using only the landed G2p-f endpoint
theorem and G2q's prior bound, which executes nothing -- and then reduces the composed run by kernel
computation: G2q's `qBorrow` on the digit `22` at step `17`, the countdown's `qStart` on that same
cell, now `some false`, at step `18`, and one mark at `24` after the first round at step `35`, which
is step `17` of G2u's `check_start_iterate_probe` shifted by the `18` steps G2q takes.

Deferred by G2x, and deliberately not claimed.  **One handoff of seventeen**: `startConfig` still
embeds every earlier phase, the sixteen earlier handoffs stay proof-level in G2x's machine (the G2y
entry below has since executed the last of them, H16), no raw-input `initialConfig` is executed,
and no clock here counts a step of any earlier phase; composing the next handoffs needs
first-arrival theorems from their own start configurations -- the G2p-d/e/f loop's is what the G2y
entry below later supplied, and G2p-b's is what the G3b entry below later supplied.  **First arrival
of the composed accept**: `T` is the first time the handoff fires, but no theorem says
`composedClock` is the first time the composed accept is entered, because G2s-a and G2u prove no
first arrival for `qDone`.  **The fence**: the policy recorded in the G2s-a entry above stands
unchanged; both tables are uncapped, hence so is this one, an oversized register still runs
`qRunEnd` off the tape and sticks, a timeout and neither verdict, and the rows routed to the
composed reject are pinned and never exercised, since G2q characterises no non-`qDone` endpoint.  A
fence phase inserted between G2q and the countdown would become a middle component of `seq`, ending
on the same entry ABI, and `seq_reject_handoff` would propagate its rejection at no extra cost;
nothing here builds it.  Every **converse**, a **footprint** theorem, and the gamma leading-digit
convention.  The composed `accept` is the countdown's phase-local `qDone`: reaching it out of a
retagged actual prior endpoint is neither halting on a raw input nor language acceptance, and the
module states no `accepts`, `AcceptsAt`, `DecidesWithin`, `UniformP` or language membership.  The
pnp4 bridge `ContentFixedGammaTargetDecrementCountdownBridge` runs the composed machine under
exactly G2w-b's three hypotheses at G2w-b's cubic budget and is described in
`pnp4/Pnp4/Frontier/ContractExpansion/README.md`.  Clock composition with the earlier phases, the
fixed parser, advice freedom, `NP` membership and `ContentVerifierBridge` remain out of scope.  It
is infrastructure, not P-vs-NP mainline progress.

The Part A G2y `FixedGammaTargetLoopDecrementCountdown` is that same combinator applied a second
time, one block further left, and it adds **no table row**: `machine` is
`FixedGammaTargetPayloadRound.machine.seq FixedGammaTargetDecrementCountdown.machine`, G2p-d's
22-state, 66-row payload-round table on the block `[0, 22)` and the whole G2x composite on
`[22, 40)` -- inside it G2q's seven decrement states at `[22, 29)` and G2s-a's eleven countdown
states at `[29, 40)` -- one closed 40-state, 120-row table.  The payload round's
`qFin`-on-`some false` row at state index `19`, which targets that machine's own absorbing `qDone`,
is routed to G2x's start at index `22`; so the composed machine hands over the moment the
exhaustion finish halts, on the tag cell `7` it halts on, with the tape the finish leaves, which is
exactly the entry ABI recorded in the G2q entry above.  That is handoff **H16**; G2x's
`qBorrow`-on-`some true` row, now at composed index `26` targeting `29`, is **H17**, inherited
unchanged and re-derived here through `seq_step_right`.  `startConfig` is the payload round's own
`startConfig` routed into the composed control -- still the retagged *actual* G2p-d foundation
endpoint, so still a phase-local retag of every earlier phase -- and
`chainClock N zeros d v = totalClock N zeros + composedClock N zeros d v`.

`loop_strict` is the enabling fact, and it is what G2x said it did not have.  It is assembled from
landed theorems with no new trace: at `loopClock N zeros` G2p-e's `register_complete` puts the round
machine in the non-absorbing `qLoop`, and `no_terminal_of_le` turns that single non-verdict into
"neither verdict at any earlier time", since a verdict entered earlier would have absorbed; above
that time `run_add` reduces the question to the finish out of exactly the `r = zeros` configuration
`register_complete` describes, where G2p-f's `exhaust_strict` already excludes `qDone` before
`exhaustClock N zeros`.  Arrival itself is G2p-f's `payload_exhausted`; only minimality is new.
`handoff_exact` is then the executed handoff, on a matching tag, a decoded `2 <= zeros` and G2p-e's
room, with `T = totalClock N zeros`: the composed run is the round machine's run, routed, at every
time up to `T`; the composed control is in neither verdict before `T`; at exactly `T` the composed
configuration **is** G2x's landed `startConfig B x w` re-embedded; and every later step is a G2x
step out of it.  The identification rests on `loop_strict` and on the round machine's persistence
from `T` to G2q's length-only deadline `priorDeadline N = 3N²`, at which G2q's `startConfig` retags;
`prior_covers` is what puts `T` at or before it.  The switch time is `T`, not `3N²`.
`loop_decrement_countdown_drained` then runs G2x's `decrement_countdown_drained` on top, under
G2u's **seven** hypotheses unchanged -- no eighth room premise: the decrement's room is G2u's
`lane_room` at `r = k = 0` and the loop's weaker room is `room_iff`'s second conjunct on it, both
derived inside the proof.  At exactly `chainClock` the composed machine is in its accept, the
countdown's `qDone`, on the separator blank `N + 2 + zeros` with tape `loopTape B x w zeros 0 v`,
persisting.  `v` is universally quantified here and nothing in pnp3 supplies it.  The surface test's
`check_handoff_probe` identifies the actual `startConfig 0 tag physWord` with an explicit
configuration -- using only the landed G2p-d `markers_at_deadline`, which executes nothing -- and
then reduces the composed run by kernel computation through **both** cross-block edges: the loop's
`qFin` (index `19`) on the tag cell `7` at step `63`, G2q's `qStart` (index `22`) on that same cell
at step `64`, G2q's `qBorrow` (index `26`) on the digit `22` at step `81`, and the countdown's
`qStart` (index `29`) on that cell, now `some false`, at step `82`.

Deferred by G2y, and deliberately not claimed.  **Two handoffs of seventeen**: `startConfig` still
embeds every earlier phase, the fifteen handoffs before H16 stay proof-level, no raw-input
`initialConfig` is executed, and no clock here counts a step of any earlier phase.  Composing the
next handoff down, from G2p-d's marker foundation into the payload round, needs no new
first-arrival theorem: the foundation's `markers_strict`, `markers_installed` and
`exactClock_le_deadline` are the same three ingredients `loop_strict`, `payload_exhausted` and
`prior_covers` supply here, and the round's `startConfig` retags the foundation's run at its
length-only deadline exactly as G2q's retags the loop's.  That handoff, H15, has since been taken by
G2z below, so the counts in this G2y entry are the ones this slice left.  Further down, G2p-b's
first arrival was still missing when this slice landed; the G3b entry below has since supplied
it.  **First arrival of the composed accept**:
`T` is the first time H16 fires, but no theorem says `chainClock` is the first time the composed
accept is entered, because G2s-a and G2u prove no first arrival for `qDone`; the first arrival
proved here is the payload loop's, inside the left block.  **The fence**: the policy recorded in the
G2s-a entry above stands unchanged; all three tables are uncapped, hence so is this one, an
oversized register still runs `qRunEnd` off the tape and sticks, a timeout and neither verdict, and
the rows routed to the composed reject are pinned but not exercised here: this slice states no
rejecting run and composes no malformed-gamma rejection, although the round machine's
`malformed_rejects` (a matching tag with no decoded width rejects in one step, on the unchanged
content tape) together with the generic `seq_reject_handoff` would give one.  Every **converse**, a
**footprint** theorem --
so every room premise stays sufficient and used, never shown necessary -- and the gamma
leading-digit convention.  The composed `accept` is the countdown's phase-local `qDone`: reaching it
out of a retagged actual prior endpoint is neither halting on a raw input nor language acceptance,
and the module states no `accepts`, `AcceptsAt`, `DecidesWithin`, `UniformP` or language membership.
The pnp4 bridge `ContentFixedGammaTargetLoopDecrementCountdownBridge` runs the composed machine
under exactly the same three hypotheses at the same cubic budget and is described in
`pnp4/Pnp4/Frontier/ContractExpansion/README.md`.  Clock composition with the earlier phases, the
fixed parser, advice freedom, `NP` membership and `ContentVerifierBridge` remain out of scope.  It
is infrastructure, not P-vs-NP mainline progress.

The Part A G2z `FixedGammaTargetMarkersLoopDecrementCountdown` is that same combinator applied a
third time, one block further left, and it again adds **no table row**: `machine` is
`FixedGammaTargetPayloadLoopFoundation.machine.seq FixedGammaTargetLoopDecrementCountdown.machine`,
G2p-d's 14-state, 42-row marker-preamble table on the block `[0, 14)` and the whole G2y composite on
`[14, 54)` -- inside it G2p-d's payload round at `[14, 36)`, G2q's decrement at `[36, 43)` and
G2s-a's countdown at `[43, 54)` -- one closed 54-state, 162-row table.  **H15 is executed by four
routed rows.**  Every working-state preamble row targeting its own
absorbing `qDone` is routed to G2y's start at index `14`: `qZeroA`/`some true`,
`qClearB`/`some true`, `qBackB`/`some true` and `qFin`/`some false`; so are the three dead `qDone`
self-rows, on a state the routing leaves unoccupied.  The table reaches `qZeroA`'s exit only on a
terminator already at cell `8` (width zero) and `qFin`'s only on one at cell `9` (width one), both
excluded by `2 <= zeros`, so what the fixtures exercise are the two `qSrcB` selects by reading the
second payload source: `qClearB` (index `9`, writing the blank and moving right) on a content
symbol, `qBackB` (index `10`, preserving the `true` and staying) on the boundary blank.  No theorem
here says which of the four rows a given word takes.  G2y's
`qFin`-on-`some false` row, now at composed index `33` targeting `36`, is **H16**, and G2x's
`qBorrow`-on-`some true` row, now at `40` targeting `43`, is **H17**; both are inherited unchanged
and re-derived here through `seq_step_right`.  `startConfig` is the marker preamble's own
`startConfig` routed into the composed control -- still the retagged *actual* G2p-c second-payload
endpoint, so still a phase-local retag of every earlier phase -- and
`markersChainClock N zeros d v = exactClock zeros + chainClock N zeros d v`.

G2z needs **no new first-arrival theorem**, which is the whole reason it is the smallest next slice.
The preamble already carries arrival with persistence (`markers_installed`), minimality
(`markers_strict`) and the deadline cover (`exactClock_le_deadline`), and the generic
`UniformTM.run_accept_of_le` identifies the preamble's run at its first arrival
`exactClock zeros = zeros + 7` with its run at the length-only `deadline N = N`, which is exactly the
run G2p-d's round `startConfig` retags.  `handoff_exact` is then the executed handoff, on a matching
tag, a decoded `2 <= zeros` and the **preamble's own** weaker room `N + 3 < tapeLength …` -- not
G2y's loop room -- with `S = exactClock zeros`: the composed run is the preamble's run, routed, at
every time up to `S`; the composed control is in neither verdict before `S`; at exactly `S` the
composed configuration **is** G2y's landed `startConfig B x w` re-embedded; and every later step is
a G2y step out of it.  The switch time is `S`, not `N`.  Because the room premise is the weaker one,
the simulation holds even where the tail would later lack room.
`markers_loop_decrement_countdown_drained` then runs G2y's `loop_decrement_countdown_drained` on
top, under G2u's and G2y's **seven** hypotheses unchanged -- no eighth room premise: the preamble's
room is `room_iff`'s `2 <= a + B`, read off the drain's own room premise `zeros + 2 + F <= a + B`
together with `2 <= zeros`, and derived inside the proof.
At exactly `markersChainClock` the composed machine is in its accept, the countdown's `qDone`, on the
separator blank `N + 2 + zeros` with tape `loopTape B x w zeros 0 v`, persisting.  `v` is universally
quantified here and nothing in pnp3 supplies it.  `malformed_reject_handoff` adds the **first routed
reject the chain composition exercises**: on a matching tag with no decoded width the preamble
rejects in one step, and `seq_reject_handoff` carries that verdict into the composed reject at index
`53` -- not the preamble's own `qReject` at `13` -- at the boundary head `N` on the unchanged content
tape, from step one on.  It is no converse and characterises no parsed target.  The surface test
identifies the actual `startConfig B tag ·` for four literal words with explicit configurations --
using only the landed G2p-c `second_payload_at_deadline` and `malformed_at_deadline`, which execute
nothing -- and then reduces the composed run by kernel computation: H15's write-and-right exit on a
`zeros = 4` word with both sources physical (state `9` at head `13` at step `10`, state `14` at head
`14` with cell `13` blanked at step `11`), its stay exit on a `zeros = 2` middle-source word
(`N = 12`; state `10` at head `11` at step `8`, state `14` at that head at step `9`) and on a
`zeros = 2` word with neither source physical (`N = 11`; head `10`), the two inherited edges at steps
`74`/`75` and `92`/`93` -- G2y's `63`/`64` and `81`/`82` shifted by the preamble's eleven steps --
and the routed reject at steps `1` and `5`.

Deferred by G2z, and deliberately not claimed.  **Three handoffs of seventeen** as of that slice:
`startConfig` still
embeds every earlier phase, the fourteen handoffs before H15 stay proof-level, no raw-input
`initialConfig` is executed, and no clock here counts a step of any earlier phase.  Composing the
next handoff down, from G2p-c's second payload into the marker preamble, again needs no new
first-arrival theorem, since `second_payload_strict` is landed; that handoff, H14, has since been
taken by G3a below, so the counts in this G2z entry are the ones this slice left.  Below that,
G2p-b's first arrival was still missing when this slice landed; the G3b entry below has since
supplied it.  **First arrival of the composed accept**: `S` is the first time H15 fires, but no
theorem says `markersChainClock` is the first time the composed accept is entered, because G2s-a and
G2u prove no first arrival for `qDone`; the first arrival proved here is the marker preamble's,
inside the left block.  **The fence**: the policy recorded in the G2s-a entry above stands unchanged;
all four tables are uncapped, hence so is this one, and an oversized register still runs `qRunEnd`
off the tape and sticks, a timeout and neither verdict.  The routed reject is exercised on a
malformed gamma only: there is no rejection converse, no `RejectsAt`, and no parsed-target rejection
characterisation.  Every other **converse**, a **footprint** theorem -- so every room premise stays
sufficient and used, never shown necessary -- and the gamma leading-digit convention.  The table is
fixed and complete but not claimed state-minimal.  The composed `accept` is the countdown's
phase-local `qDone`: reaching it out of a retagged actual prior endpoint is neither halting on a raw
input nor language acceptance, and the module states no `accepts`, `AcceptsAt`, `DecidesWithin`,
`UniformP` or language membership.  The pnp4 bridge
`ContentFixedGammaTargetMarkersLoopDecrementCountdownBridge` runs the composed machine under exactly
the same three hypotheses at the same cubic budget and is described in
`pnp4/Pnp4/Frontier/ContractExpansion/README.md`.  Clock composition with the earlier phases, the
fixed parser, advice freedom, `NP` membership and `ContentVerifierBridge` remain out of scope.  It is
infrastructure, not P-vs-NP mainline progress.

The Part A G3a `FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown` is that same combinator
applied a **fourth** time, one block further left, and it again adds **no table row**: `machine` is
`FixedGammaTargetSecondPayload.machine.seq FixedGammaTargetMarkersLoopDecrementCountdown.machine`,
G2p-c's 14-state, 42-row second-payload table on the block `[0, 14)` and the whole G2z composite on
`[14, 68)` -- inside it G2p-d's marker preamble at `[14, 28)`, G2p-d's payload round at `[28, 50)`,
G2q's decrement at `[50, 57)` and G2s-a's countdown at `[57, 68)` -- one closed 68-state, 204-row
table.  **H14 is executed by a single live routed row.**  `qScanLeft` on the blank is G2p-c's only
row out of a working state into its own absorbing `qDone`, and it is routed to G2z's start at index
`14`, writing `some false` and staying; the three dead `qDone` self-rows are routed too, on a state
the routing leaves unoccupied.  That one transition both restores the anchor G2p-c blanked at cell
`7` and crosses the block boundary, at no cost.  G2z's four `qDone`-targeting preamble rows, now at
composed indices `23`/`24` (the two the `2 <= zeros` surface reaches) targeting `28`, are **H15**;
the payload round's `qFin`-on-`some false` row, now at `47` targeting `50`, is **H16**; and G2x's
`qBorrow`-on-`some true` row, now at `54` targeting `57`, is **H17**.  All three are inherited
unchanged.  `table_and_resource_pins` pins the one *routed* row that is new to this composition --
`qScanLeft`/`none` with its target re-routed to `14`, not a new table row -- together with the
composed indices of all four handoff states; it does **not** restate the inherited rows, because the
universal right-block row equation it also pins transports every G2z row verbatim from G2z's own
audited pins, and the surface test reduces H14, H15's `qClearB` row, H16 and H17 out of an actual
configuration; H15's `qBackB` row is carried by that row equation and G2z's own probes, not by a G3a
fixture.
`startConfig` is G2p-c's own `startConfig` routed into the composed control -- still the retagged
*actual* G2p-b first-payload endpoint, so still a phase-local retag of every earlier phase -- and
`secondChainClock N zeros d v = FixedGammaTargetSecondPayload.exactClock N zeros
+ markersChainClock N zeros d v`.

G3a needs **no new first-arrival theorem** either.  G2p-c already carries arrival
(`second_payload_exact`, `zero_width_exact`, `width_one_exact`), minimality
(`second_payload_strict`, `zero_width_strict`, `width_one_strict`) and the deadline cover
(`exactClock_le_deadline`) at *every* decoded width, and the generic `UniformTM.run_accept_of_le`
identifies G2p-c's run at its first arrival with its run at the length-only `deadline N = 2 * N`,
which is exactly the run G2p-d's marker `startConfig`, and through it G2z's, retags.  The private
`handoff_of_arrival` states that identification once, width-free: given `qDone` at `T`, neither
terminal before `T`, and `T <= deadline N`, the composed run is G2p-c's run routed up to `T`, is in
neither composed verdict before `T`, **is** G2z's landed `startConfig B x w` re-embedded at exactly
`T`, and takes G2z steps afterwards.  The three public width instances then differ only in which
landed pair they feed it.

`handoff_exact` is the `2 <= zeros` instance, on a matching tag, a decoded `2 <= zeros` and G2p-c's
own room `N + 3 < tapeLength …` -- which is `room_iff`'s `2 <= a + B`, the same condition the marker
preamble needs, so the simulation holds on both sides of the switch and even where the tail would
later lack room -- with `S = FixedGammaTargetSecondPayload.exactClock N zeros = 2 * N - 7`.  The
switch time is `S`, not `2 * N`, and unlike G2z's `zeros + 7` it is **length-dependent**.  This is
the only width branch an *accepted parsed target* can reach, since `3 <= pr.2.n` forces
`2 <= gammaZeros pr.2.n`; and inside it G2p-c's endpoint is extensional in its three source shapes
-- a physical source `10 + zeros < N`, the source address on the boundary blank `10 + zeros = N`,
and the first payload cell already on the boundary `9 + zeros = N`, which bypasses `qRead`
altogether -- so all three hand the same configuration over and no shape premise appears.
`zero_width_handoff` (no room premise; first arrival `3`) and `width_one_handoff` (G2p-b's weaker
room `N + 2 < tapeLength …`; first arrival `5`) state the same switch at the two degenerate decoded
widths.  Both are outside every accepted parsed target, neither width leaves a net write -- the tag
cell `7` is blanked and restored, and what G2p-c exports at these widths is a tape equality with the
incoming tape, not a footprint -- and **nothing downstream is claimed for them**: they record only
that the composed table performs the switch at every decoded width, not only at the one the accepted
surface uses.

`second_payload_markers_loop_decrement_countdown_drained` then runs G2z's
`markers_loop_decrement_countdown_drained` on top, under G2u's, G2y's and G2z's **seven** hypotheses
unchanged -- no eighth room premise: G2p-c's room is `room_iff`'s `2 <= a + B`, read off the drain's
own room premise `zeros + 2 + F <= a + B` together with `2 <= zeros`, and derived inside the proof.
At exactly `secondChainClock` the composed machine is in its accept, the countdown's `qDone`, on the
separator blank `N + 2 + zeros` with tape `loopTape B x w zeros 0 v`, persisting.  `v` is universally
quantified here and nothing in pnp3 supplies it.  `malformed_reject_handoff` transports G2p-c's own
landed `malformed_exact`: on a matching tag with no decoded width G2p-c rejects in one step, and
`seq_reject_handoff` carries that verdict into the composed reject at index `67` -- not G2p-c's own
`qReject` at `13`, nor G2z's at `53` -- at the boundary head `N` on the unchanged content tape, from
step one on.  Its first-arrival companion `malformed_strict` is not needed, since both machines
absorb a rejection.  It is stated in the forward direction only: no converse, and it characterises
no parsed target.  The surface test identifies the actual `startConfig B tag ·` for six literal
words with explicit configurations -- using only the landed G2p-b `first_payload_at_deadline`,
`zero_width_at_deadline` and `malformed_at_deadline`, which execute nothing -- and then reduces the
composed run by kernel computation: the single routed row at steps `26`/`27` on a `zeros = 4` word
with both sources physical (`N = 17`; state `11` at head `7` on the blanked anchor, then state `14`
at that head with the anchor restored, the register `true` at `18`, G2p-b's digit at `19` and
G2p-c's digit at the target cell `20`), at `16`/`17` on a `zeros = 2` middle-source word (`N = 12`),
at `14`/`15` on a `zeros = 2` word whose first payload cell is already the boundary (`N = 11`), and
at `2`/`3` and `4`/`5` on the two degenerate widths (`N = 10`, `N = 11`); the three inherited edges
at steps `37`/`38`, `101`/`102` and `119`/`120` -- G2z's `10`/`11`, `74`/`75` and `92`/`93` shifted
by the `27` steps G2p-c takes -- and the routed reject at steps `1` and `5`.

Deferred by G3a, and deliberately not claimed.  **Four handoffs of seventeen**: `startConfig` still
embeds every earlier phase, the thirteen handoffs before H14 stay proof-level, no raw-input
`initialConfig` is executed, and no clock here counts a step of any earlier phase.  Composing the
next handoff down, from G2p-b's first payload into G2p-c, was **blocked** when this slice landed
(the G3b entry below has since supplied the missing premise, the G3c entry below it has since
built that composition as H13, and the G3e entry after that has since taken H12 too, so the count
is now six and the counts recorded here are the ones this slice left): G2p-b exported its endpoint
at its deadline but no first-arrival theorem, so there is nothing to feed `handoff_of_arrival`'s
minimality premise.  **First arrival of the composed accept**: `S` is the first time H14 fires, but
no theorem says `secondChainClock` is the first time the composed accept is entered, because G2s-a
and G2u prove no first arrival for `qDone`; the first arrival proved here is G2p-c's, inside the
left block.  **The fence**: the policy recorded in the G2s-a entry above stands unchanged; all five
tables are uncapped, hence so is this one, and an oversized register still runs `qRunEnd` off the
tape and sticks, a timeout and neither verdict.  The routed reject is exercised on a malformed gamma
only: there is no rejection converse, no `RejectsAt`, and no parsed-target rejection
characterisation.  Every other **converse**, a **footprint** theorem -- so every room premise stays
sufficient and used, never shown necessary -- and the gamma leading-digit convention.  The table is
fixed and complete but not claimed state-minimal.  The composed `accept` is the countdown's
phase-local `qDone`: reaching it out of a retagged actual prior endpoint is neither halting on a raw
input nor language acceptance, and the module states no `accepts`, `AcceptsAt`, `DecidesWithin`,
`UniformP` or language membership.  The pnp4 bridge
`ContentFixedGammaTargetSecondPayloadMarkersLoopDecrementCountdownBridge` runs the composed machine
under exactly the same three hypotheses at the same cubic budget and is described in
`pnp4/Pnp4/Frontier/ContractExpansion/README.md`.  Clock composition with the earlier phases, the
fixed parser, advice freedom, `NP` membership and `ContentVerifierBridge` remain out of scope.  It is
infrastructure, not P-vs-NP mainline progress.

The Part A G3b slice adds no module, no machine and no table row: it is the exact first-arrival
surface of the G2p-b `FixedGammaTargetFirstPayload` phase, proved against that phase's own untouched
18-state, 54-row table, with every signature it already exported unchanged.  The G3a entry above
records why it was needed: `UniformTM.seq_handoff` switches blocks at the left machine's *first*
acceptance, and G2p-b exported only its length-only deadline `3 * N`, so that minimality premise
could not be discharged for this phase.  `exactClock N zeros` is the first terminal time on a
decoded width -- `6` at width zero, where the run blanks the terminator, walks back to tag cell `6`,
blanks the anchor at `7`, finds the marker directly after it, restores both and halts, at every
length, and `2 * N + zeros - 6` at a positive width, where the head also walks out to the target
cell `N + 2` and back to the anchor -- and `malformedExactClock` is `1`.  Both numbers are read off
the fixed schedules this phase already used for its endpoint, not chosen: the last branch of
`posState` is the only one that is `qDone`, and none is `qReject`.

At a positive width, at width zero and at a malformed gamma — the last of which has no decoded width
at all — the slice proves both directions.  `first_payload_exact` puts a
positive-width run in `qDone` at head `7` with the carried bit at `N + 2` from `exactClock N zeros`
on, under the same room premise `a + m + 2 < tapeLength (pairLength a m) B` the landed endpoint
already used, and `first_payload_strict` puts the control in neither `qDone` nor `qReject` at every
strictly earlier time; `first_physical_exact` and `first_virtual_exact` name the two positive-width
source shapes at that time, and `zero_width_exact`/`zero_width_strict` and
`malformed_exact`/`malformed_strict` do the same for width zero and for a malformed gamma.
`exactClock_le_deadline`, whose premise `9 + zeros <= N` is the width bound
`FixedContentGammaTerminator.gamma_contract` already supplies for a decoded width, recovers the five
landed `*_at_deadline` endpoints from the exact ones -- they are now derived rather than proved a
second time -- and `exactClock_add` records that the subtraction never truncates there.
`strict_first_terminal` bundles what a sequential composition consumes, on any decoded width and
assuming room only when that width is positive: neither verdict before `exactClock (a + m) zeros`,
`machine.accept` exactly there, that time at or below `deadline (a + m)`, and the configuration
there *is* the configuration at the deadline -- the one G2p-c's `startConfig` retags.  The last
conjunct is absorption of `qDone`, not a second run.

The surface test restates all of it and then executes.  Five probes identify the *actual*
`startConfig B tag ·` -- the retagged G2p-a bootstrap endpoint -- with an explicit configuration for
every budget, using only G2p-a's landed `run_deadline` and `malformed_at_deadline`, which execute
nothing there, and then reduce this phase's own run at `B = 0` by kernel computation at the exact
clock and one step before it: a physical payload cell carrying `1` and one carrying `0`
(`zeros = 1`, `N = 11`, clock `17`), a physical payload cell at `zeros = 3` (`N = 13`, clock `23`),
the virtual source `9 + zeros = N` (`zeros = 2`, `N = 11`, clock `18`) -- the largest width that
length can decode -- width zero at its own extreme `9 = N` (clock `6`), where the target cell is
left blank, and a malformed gamma (clock `1`).  No probe appeals to the theorem it checks.

Deferred by G3b, and deliberately not claimed.  **No composition**: the slice states no `seq`, no
composed machine, no composed clock and no new handoff, so the handoff counts of the G3a entry above
were unchanged at four of seventeen when it landed, and what blocked the next one down was then that
composition itself rather than a missing premise; the G3c entry below has since built it.  **No
converse**: nothing says that `qDone` at the exact clock
implies a positive width, or that `qReject` implies a malformed gamma, and no theorem covers a
positive width without room, unchanged from G2p-b.  The **fence** is unchanged: the table is
uncapped, and this slice adds no cap.  `qDone` is an internal endpoint reached out of a retagged
actual prior endpoint, which is neither halting on a raw input nor language acceptance; the module
states no `accepts`, `AcceptsAt`, `DecidesWithin`, `UniformP`, `VerifiesRelation` or language
membership, and no pnp4 reader, parser or `ContentVerifierBridge` fact.  It is infrastructure, not
P-vs-NP mainline progress.

The Part A G3c slice applies the generic sequential composition a fifth time, one block further
left.  The new module
`Complexity.Uniform.V1.FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown`
defines `machine` as `FixedGammaTargetFirstPayload.machine.seq
FixedGammaTargetSecondPayloadMarkersLoopDecrementCountdown.machine`: G2p-b's fixed 18-state, 54-row
first-payload table on the left block `[0, 18)` and the whole landed G3a 68-state composite on the
right block `[18, 86)` -- inside it G2p-c's second payload at `[18, 32)`, G2p-d's marker preamble at
`[32, 46)`, G2p-d's payload round at `[46, 68)`, G2q's decrement at `[68, 75)` and G2s-a's countdown
at `[75, 86)` -- as one closed 86-state, 258-row table.  **No table row is new**: every row is a row
of one of those six tables with its target routed, and `table_and_resource_pins` pins the counts,
the three distinguished states (`0`, `84`, `85`), the two block injections with their disjointness,
the two block-offset equations that locate every G3a state, the three routing cases, the universal
left- and right-block row equations, the public step against the composed raw table, and the one
*routed* row this composition adds.

**H13 is executed by a single live routed row.**  `qSeekAnchor` on the blank is G2p-b's only row out
of a working state into its own absorbing `qDone`, and `seq` routes it to G3a's start at composed
index `18`, in that same transition, on that cell, writing `some false` and staying, at no cost.
The three `qDone` self-rows are routed too, but that state stays dead: no routed row and no start
targets it.  H14 (`29 -> 32`), H15 (four routed rows into `46`, of which `2 <= zeros` reaches only
`qClearB` at `41` and `qBackB` at `42`), H16 (`65 -> 68`) and H17 (`72 -> 75`) are inherited from
G3a; their rows are transported verbatim by the right-block row equation and their composed indices
are the G3a indices shifted by eighteen.

G3c adds **no new first-arrival theorem**.  G3b landed G2p-b's arrival (`first_payload_exact`,
`zero_width_exact`), its minimality (`first_payload_strict`, `zero_width_strict`) and its deadline
cover (`exactClock_le_deadline`) at every decoded width, and `UniformTM.run_accept_of_le` identifies
G2p-b's run at its first arrival with its run at the length-only `deadline N = 3 * N`, which is
exactly the run G2p-c's `startConfig`, and through it G3a's, retags.  The private
`handoff_of_arrival` states that identification once, width-free, and the two public width instances
differ only in which landed pair they feed it.

`handoff_exact` is the whole positive branch, on a matching tag, a decoded `0 < zeros` and G2p-b's
own room `N + 2 < tapeLength …`, with `S = FixedGammaTargetFirstPayload.exactClock N zeros
= 2 * N + zeros - 6`.  The switch time is `S`, not `3 * N`, and unlike G2p-c's it moves with the
width as well as the length.  G2p-b splits its widths as `0` against `0 < zeros`, so there is no
separate width-one statement to make, and an *accepted parsed target* -- where `3 <= pr.2.n` forces
`2 <= gammaZeros pr.2.n` -- is a sub-case of this one branch.  Inside it G2p-b's endpoint is
extensional in its two source shapes, a physical payload cell `9 + zeros < N` and a payload cell
that *is* the boundary blank `9 + zeros = N` and copies the virtual zero, so both hand the same
configuration over and no shape premise appears.  G2p-b's room is weaker than G2p-c's, so the
simulation holds even where the tail would later lack room.  `zero_width_handoff` (no room premise;
first arrival `6`) states the same switch at the one degenerate decoded width, which leaves no net
write -- the anchor at `7` and the terminator at `8` are blanked and restored, and what G2p-b
exports there is a tape equality with the incoming bootstrap scratch tape, not a footprint -- is
outside every accepted parsed target, and for which **nothing downstream is claimed**.

`first_payload_second_payload_markers_loop_decrement_countdown_drained` then runs G3a's drain on
top, under G2u's, G2y's, G2z's and G3a's **seven** hypotheses unchanged -- no eighth room premise:
G2p-b's room follows from G2p-c's, which G3a already derives from the drain's own
`zeros + 2 + F <= a + B` together with `2 <= zeros`.  At exactly `firstChainClock N zeros d v
= FixedGammaTargetFirstPayload.exactClock N zeros + secondChainClock N zeros d v` the composed
machine is in its accept, the countdown's `qDone`, on the separator blank `N + 2 + zeros` with tape
`loopTape B x w zeros 0 v`, persisting.  `v` is universally quantified here and nothing in pnp3
supplies it.  `malformed_reject_handoff` transports G2p-b's own landed `malformed_exact`: on a
matching tag with no decoded width G2p-b rejects in one step, and `seq_reject_handoff` carries that
verdict into the composed reject at index `85` -- not G2p-b's own `qReject` at `17`, nor G2p-c's at
`31` -- at the boundary head `N` on the unchanged content tape, from step one on.  Its first-arrival
companion `malformed_strict` is not needed, since both machines absorb a rejection.  It is stated in
the forward direction only: no converse, and it characterises no parsed target.

The surface test identifies the actual `startConfig B tag ·` for six literal words with explicit
configurations -- using only the landed G2p-a `run_deadline` and `malformed_at_deadline`, which
execute nothing -- and then reduces the composed run by kernel computation: the single routed row at
steps `31`/`32` on a `zeros = 4` word with a physical payload cell (`N = 17`; state `15` at head `7`
on the blanked anchor, then state `18` at that head with the anchor restored, the register `true` at
`18` and G2p-b's digit `true` at the target cell `19`), at `19`/`20` on a `zeros = 2` word
(`N = 12`) and `16`/`17` on a `zeros = 1` word (`N = 11`), both physical, at `17`/`18` on a
`zeros = 2` word whose payload cell is already the boundary (`N = 11`, virtual `false` at the target
cell `13`), and at `5`/`6` on width zero (`N = 10`, target cell left blank); the four inherited
edges at steps `58`/`59`, `69`/`70`, `133`/`134` and `151`/`152` -- G3a's `26`/`27`, `37`/`38`,
`101`/`102` and `119`/`120` shifted by the `32` steps G2p-b takes -- and the routed reject at steps
`1` and `5`.

Deferred by G3c, and deliberately not claimed.  **Five handoffs of seventeen**: `startConfig` still
embeds every earlier phase, the twelve handoffs before H13 were proof-level at that slice, no raw-input
`initialConfig` is executed, and no clock here counts a step of any earlier phase.  Composing the
next handoff down, from G2p-a's scratch bootstrap into G2p-b, needs no new first-arrival theorem
either -- G2p-a's `strict_first_terminal` and `exactClock_le_deadline` are landed -- so what is owed
there is that composition itself; the G3e entry below has since built it, taking the count to six,
so the counts in this G3c entry are the ones that slice left.  **First arrival of the composed
accept**: `S` is the first time
H13 fires, but no theorem says `firstChainClock` is the first time the composed accept is entered,
because G2s-a and G2u prove no first arrival for `qDone`; the first arrival proved here is G2p-b's,
inside the left block.  **The fence**: the policy recorded in the G2s-a entry above stands
unchanged; all six tables are uncapped, hence so is this one, and an oversized register still runs
`qRunEnd` off the tape and sticks, a timeout and neither verdict.  The routed reject is exercised on
a malformed gamma only: there is no rejection converse, no `RejectsAt`, and no parsed-target
rejection characterisation.  Every other **converse**, a **footprint** theorem -- so every room
premise stays sufficient and used, never shown necessary -- and the gamma leading-digit convention.
The table is fixed and complete but not claimed state-minimal.  The composed `accept` is the
countdown's phase-local `qDone`: reaching it out of a retagged actual prior endpoint is neither
halting on a raw input nor language acceptance, and the module states no `accepts`, `AcceptsAt`,
`DecidesWithin`, `UniformP` or language membership.  The pnp4 bridge
`ContentFixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdownBridge` runs the
composed machine under exactly the same three hypotheses at the same cubic budget and is described
in `pnp4/Pnp4/Frontier/ContractExpansion/README.md`.  Clock composition with the earlier phases, the
fixed parser, advice freedom, `NP` membership and `ContentVerifierBridge` remain out of scope.  It
is infrastructure, not P-vs-NP mainline progress.

The Part A G3e slice applies the generic sequential composition a sixth time, one block further
left again.  (The slice label `G3d` is intentionally unused here; the immediately preceding composite is G3c.)  The new
module
`Complexity.Uniform.V1.FixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdown`
defines `machine` as `FixedGammaTerminatorScratchBootstrap.machine.seq
FixedGammaTargetFirstPayloadSecondPayloadMarkersLoopDecrementCountdown.machine`: G2p-a's fixed
9-state, 27-row scratch-bootstrap table on the left block `[0, 9)` and the whole landed G3c
86-state composite on the right block `[9, 95)` -- inside it G2p-b's first payload at `[9, 27)`,
G2p-c's second payload at `[27, 41)`, G2p-d's marker preamble at `[41, 55)`, G2p-d's payload round
at `[55, 77)`, G2q's decrement at `[77, 84)` and G2s-a's countdown at `[84, 95)` -- as one closed
95-state, 285-row table.  **No table row is new**: every row is a row of one of those seven tables
with its target routed, and `table_and_resource_pins` pins the counts, the three distinguished
states (`0`, `93`, `94`), the two block injections with their disjointness, the four nested
block-offset equations that locate the G2p-b, G2p-c, G3a and G2z sub-blocks inside G3c, the three
routing cases, the universal
left- and right-block row equations, the public step against the composed raw table, and the one
*routed* row this composition adds.

**H12 is executed by a single live routed row.**  `qScanLeft` on the blank is G2p-a's only row out
of a working state into its own absorbing `qTerm`, and `seq` routes it to G3c's start at composed
index `9`, in that same transition, on that cell, writing `some true` -- the gamma terminator the
bootstrap had blanked as its return marker -- and staying, at no cost.  The three `qTerm` self-rows
are routed too, but that state stays dead: no routed row and no start targets it.  H13 (`24 ->
27`), H14 (`38 -> 41`), H15 (four routed rows into `55`, of which `2 <= zeros` reaches only
`qClearB` at `50` and `qBackB` at `51`), H16 (`74 -> 77`) and H17 (`81 -> 84`) are inherited from
G3c; their rows are transported verbatim by the right-block row equation and their composed indices
are the G3c indices shifted by nine.

G3e adds **no new first-arrival theorem**.  G2p-a landed arrival, minimality and the deadline cover
in one place: `strict_first_terminal` excludes both `qTerm` and `qReject` at every time strictly
before `exactClock N zeros = 2 * N - 11 - zeros` and lands `qTerm` exactly there, and
`exactClock_le_deadline` holds for all `N` and `zeros` with no premise at all, so
`UniformTM.run_accept_of_le` identifies G2p-a's run at its first arrival with its run at the
length-only `deadline N = 2 * N`, which is exactly the run G2p-b's `startConfig`, and through it
G3c's, retags.  The private `handoff_of_arrival` states that identification once, width-free, and
`handoff_exact` feeds it the landed pair.

`handoff_exact` takes **two** hypotheses only, a matching tag and a decoded width, with
`S = FixedGammaTerminatorScratchBootstrap.exactClock N zeros = 2 * N - 11 - zeros`.  Unlike every
earlier handoff in this chain it needs no width case and no room premise.  G2p-a's clock does not
split on the width -- the degenerate width zero differs only in the incoming G2m dispatcher head,
`7` against `6`, which G2p-a's own trace absorbs -- so `zeros = 0` enters through the same
statement as a positive width and there is no separate degenerate theorem to state; and G2p-a needs
no room, because `tapeLength (pairLength a m) B = 2 * a + m + B + 2` allocates its scratch cell
`N + 1` for every budget including `B = 0`.  An *accepted parsed target*, where `3 <= pr.2.n`
forces `2 <= gammaZeros pr.2.n`, is a sub-case.

`handoff_endpoint_pins` reads the switch configuration back semantically, which is the dependency
H12 has to preserve: at `S` the composed head is the restored terminator cell `8 + zeros` and the
composed tape is G2p-a's `scratchTape B x w` -- `contentTape` with `true` at the scratch cell
`N + 1` and nothing else changed -- and those are *the same two projections* that G2p-b's own
`startConfig` carries, so the theorem also states the two equalities directly.  It is a statement
about the two configurations only and claims nothing about what G2p-b then computes.

`scratch_bootstrap_first_payload_second_payload_markers_loop_decrement_countdown_drained` then runs
G3c's drain on top, under G2u's, G2y's, G2z's, G3a's and G3c's **seven** hypotheses unchanged -- no
eighth premise, because G2p-a's phase has none to add.  At exactly `bootChainClock N zeros d v
= FixedGammaTerminatorScratchBootstrap.exactClock N zeros + firstChainClock N zeros d v` the
composed machine is in its accept, the countdown's `qDone`, on the separator blank `N + 2 + zeros`
with tape `loopTape B x w zeros 0 v`, persisting.  `v` is universally quantified here and nothing
in pnp3 supplies it.  `malformed_reject_handoff` transports G2p-a's own landed `malformed_exact`:
on a matching tag with no decoded width the G2m dispatcher stopped at the blank boundary cell `N`,
so G2p-a's first read is a blank and it rejects in one step, and `seq_reject_handoff` carries that
verdict into the composed reject at index `94` -- not G2p-a's own `qReject` at `8`, nor G2p-b's at
`26` -- at the boundary head `N` on the unchanged content tape, from step one on.  Its
first-arrival companion is not needed, since both machines absorb a rejection.  It is stated in the
forward direction only: no converse, and it characterises no parsed target.

The surface test identifies the actual `startConfig B tag ·` for six literal words with explicit
configurations -- using only G2m's landed `tagged_endpoint_classification`, which executes nothing
-- and then reduces the composed run by kernel computation: the single routed row at steps `18`/`19`
on a `zeros = 4` word (`N = 17`; state `6` at head `12` on the blanked terminator, then state `9`
at that head with the terminator restored, the boundary blank at `17` and G2p-a's scratch `true` at
`18`), at `10`/`11` on a `zeros = 2` word (`N = 12`), at `9`/`10` on a `zeros = 1` word (`N = 11`),
at `8`/`9` on a second `zeros = 2` word (`N = 11`) and at `8`/`9` on width zero (`N = 10`), the one
probe whose incoming dispatcher head is `7`; the five inherited edges at steps `50`/`51`, `77`/`78`,
`88`/`89`, `152`/`153` and `170`/`171` -- G3c's own steps shifted by nine states and by the `19`
steps G2p-a takes -- and the routed reject at steps `1` and `5`.

Deferred by G3e, and deliberately not claimed.  **Six handoffs of seventeen**: `startConfig` still
embeds every earlier phase, the eleven handoffs before H12 stay proof-level, no raw-input
`initialConfig` is executed, and no clock here counts a step of any earlier phase.  The next
handoff down, **H11** from G2m's payload dispatcher into G2p-a, is blocked twice over:
`FixedGammaPayloadDispatcherDeadline` exports the deadline-indexed endpoint classification but no
first-arrival theorem for its own terminal, so it needs a G3b-style slice first; and it has *two*
non-reject absorbing outcomes, `qAllZero` (its `machine.accept`) and `qHasOne`, of which `UniformTM.seq`
routes only the first, so the generic combinator does not apply to it unchanged.  **First arrival
of the composed accept**: `S` is the first time H12 fires, but no theorem says `bootChainClock` is
the first time the composed accept is entered, because G2s-a and G2u prove no first arrival for
`qDone`; the first arrival proved here is G2p-a's, inside the left block.  **The fence**: the
policy recorded in the G2s-a entry above stands unchanged; all seven tables are uncapped, hence so
is this one, and an oversized register still runs `qRunEnd` off the tape and sticks, a timeout and
neither verdict.  The routed reject is exercised on a malformed gamma only: there is no rejection
converse, no `RejectsAt`, and no parsed-target rejection characterisation.  Every other
**converse**, a **footprint** theorem for the composite -- so every room premise of the tail stays
sufficient and used, never shown necessary -- and the gamma leading-digit convention.  The table is
fixed and complete but not claimed state-minimal.  The composed `accept` is the countdown's
phase-local `qDone`: reaching it out of a retagged actual prior endpoint is neither halting on a raw
input nor language acceptance, and the module states no `accepts`, `AcceptsAt`, `DecidesWithin`,
`UniformP` or language membership.  The pnp4 bridge
`ContentFixedGammaTargetScratchBootstrapFirstPayloadSecondPayloadMarkersLoopDecrementCountdownBridge`
runs the composed machine under exactly the same three hypotheses at the same cubic budget and is
described in `pnp4/Pnp4/Frontier/ContractExpansion/README.md`.  Clock composition with the earlier
phases, the fixed parser, advice freedom, `NP` membership and `ContentVerifierBridge` remain out of
scope.  It is infrastructure, not P-vs-NP mainline progress.
