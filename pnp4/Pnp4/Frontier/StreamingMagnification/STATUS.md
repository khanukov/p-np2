# Streaming magnification status

Status: **GLOBAL EAE BRIDGE, EXACT FIXED GAMMA/TRIPLE RUNS, AND REAL-CODEC `startOffset` HANDOFF ADDED; AMBIENT-END/TAIL-PARSER/ROW-TM/NORMALIZATION/COMPILER BLOCKERS; NO MMW UPPER THEOREM OR CAPSTONE**

Base: `main@5d8ee5f80e1dbc4fb7bd0c725fa98f1a999770d0`

Local branch: `research/mmw-chmy-streaming-p-ne-np`

Primary sources:

- McKay, Murray, Williams, [*Weak lower bounds on resource-bounded compression imply strong separations of complexity classes*](https://people.csail.mit.edu/rrw/MCSP-MKTP-stoc19.pdf), STOC 2019 (MMW).
- Chen, Jin, Santhanam, Williams, [*Constructive Separations and Their Consequences*](https://theoretics.episciences.org/12881/pdf), TheoretiCS 2024, especially Lemma 3.2.
- Hirahara, Ilango, Williams, [*Beating Brute Force for Compression Problems*](https://eccc.weizmann.ac.il/report/2023/171/download), STOC 2024/ECCC TR23-171, especially Lemma 2.1.

## Result classification

The primary result of this branch remains a **model/definition audit**, not a
streaming lower bound and not a proof of `P != NP`.  The finite objects needed
to state and test the MMW construction are concrete.  A separate operational
uniformity track is now available, but the repository's canonical `P` and
`NP` still do not supply the normalization needed to enter that track from an
old `P = NP` hypothesis.

Under the repository governance policy, the completed work is infrastructure.
It does not reduce `SearchMCSPWeakLowerBound` or
`VerifiedNPDAGLowerBoundSource`, and the direct uniform MMW route has not been
bridged to the repository's `PpolyDAG` mainline.

## Closed finite and operational layers

The following components are implemented without a contract, source/provider
field, axiom, or hidden existence assumption:

| Layer | What is now formalized | Deliberate boundary |
| --- | --- | --- |
| Standard DAG MCSP | A list-backed, topologically ordered shared Boolean DAG; exact conversion to and from the frozen `DagCircuit`; gate-count reconciliation; explicit lexicographic truth-table order | The structural carrier includes constant gates only to round-trip the frozen repository representation.  The target predicate `UsesOnlyAndOrNot` filters every MCSP witness and Stream-Merge candidate to the paper's exact `AND`/`OR`/`NOT` basis. |
| Local DAG evaluation trace | A Boolean value for every shared-DAG gate, a checker using the current gate, at most one external-input bit, and strictly earlier trace entries, canonical-trace existence, uniqueness, exact equivalence to `DagCircuit.eval` / `FlatCircuit.eval`, and a canonical zero-padded `s`-bit form | This proves the semantic local-verifier layer.  An operational polynomial checker is still required before assigning a uniform complexity class. |
| Fixed DAG codec | A fixed-length circuit body, canonical padding, executable encode/decode, exact round trips and injectivity, finite enumeration, and an explicit `O(s log(n+s))` code-length bound | The codec can represent the broader structural carrier; successful target search additionally checks `UsesOnlyAndOrNot`. |
| Total search-MCSP | A genuine tagged `found`/`noCircuit` result with soundness and completeness in both directions; an executable exhaustive reference solver and exact decision bridge | This is finite reference computation, not a streaming-time algorithm. |
| Streaming RAM | One fixed length-aware one-pass bit program, explicit input cursor and next-bit requests, finite bit-local instruction palette, indirect addressing, write-only output/report phase, and trace-derived space, maximum update-gap, and report-time measures | This is the operational machine model.  No polynomial-resource Stream-Merge implementation has been constructed in it. |
| Stream-Merge reference | Executable finite size-then-physical-lex minimization, malformed-request semantics, exact final partial blocks, `blockLength > 2^n`, prefix agreement, optimality, and final `found`/`noCircuit` equivalences | The reference search may enumerate the entire code cube and evaluate whole tables, so it proves no RAM resource bound. |
| Search-free choice/output graph | `selectCode = some code` is equivalent to successful canonical decoding, merge consistency, minimum gate count, and first serialized-lex body; `noCircuit` is equivalent to universal failure of every fixed-length code; one true output bit is decomposed exactly into those two branches | Candidate failure now has one `n + 2s`-bit witness covering decode failure, wrong basis, or one locally checked mismatch.  This is a semantic replacement for exhaustive search, not yet an operational running-time theorem. |
| Fixed-slice EAE output-bit shell | For a valid prior and well-formed block, `referenceOutputBit = true` is equivalent to `exists choice, forall query, exists inner, OutputBitMatrix`; the three carriers have exact lengths `1 + codeLength n s`, `1 + n + codeLength n s`, and `n + 2s`, and an interpreter-tested reflected Bool checker.  Their common length is at most `14(m+1)^2`, and hence at most `certificateLength m 64`, whenever `n,s <= m`. | The row still contains executable bounded `Fin` loops, and no operational polynomial-time bound for them is proved.  The theorem also keeps `n`, `s`, `start`, the block, and its proof as Lean parameters, so it is not yet one self-delimiting `Sigma_3` language. |
| Certificate-length EAE padding | Explicit zero-extension embeds the three fixed wires into the successive lengths `certificateLength m 64`, `certificateLength (m + cert(m)) 64`, and `certificateLength (m + cert(m) + cert(m + cert(m))) 64`.  Canonical outer/inner suffixes and vacuous noncanonical universal rows preserve the complete E-A-E shell exactly. | This is a semantic carrier conversion.  It does not make the padded matrix operationally polynomial-time. |
| Global self-delimiting output-bit/EAE language | An executable exact-length codec serializes tag, canonical gamma-coded `n,s,blockLength`, fixed-width start, full prior DAG code, exact final block, and output position.  The parser rejects malformed fields and every wrong ambient length; `parse (encode r) = some r`, and parsed `n,s` are bounded by ambient length.  A bounded, unique base-length recovery and exact suffix unpacker define one real malformed-false `GlobalPaddedRowLanguage`, and `OutputBitLanguage = FinitePHClosure.EAEProject 64 64 64 GlobalPaddedRowLanguage` is proved as an equality of languages. | The parser, length recovery, and padded row are executable Lean definitions, not one constructed `OperationalTM`; no polynomial clock or repaired finite-PH membership theorem follows from executability alone.  Invalid-prior/malformed Stream-Merge result bits are rejected rather than included in this valid-call language. |
| Repaired finite-quantifier closure | `ExistsProject` has exact fixed-bitstring semantics and maps an operational `UniformP` matrix into `UniformNP`; complement gives the universal projection; under the explicit repaired-class equality `UniformP = UniformNP`, an E-A-E projection of a `UniformP` matrix is again in `UniformP`.  Applying the global language equality yields explicit capstones from `UniformP GlobalPaddedRowLanguage` (or its canonical variant) plus repaired-class equality to `UniformP OutputBitLanguage`. | Both premises remain explicit.  This is not a bridge from conventional repository `P = NP`, and it still requires an operational decider for the global padded matrix row. |
| Fixed-control dynamic scan | One two-state `OperationalTM`, independent of input length, scans zeroes to the first `true` bit at the exact `n+1` clock.  Zero-step, first-one, absorbing-done, all-zero, and arbitrary-prefix runs are proved; it decides the contains-one language in `UniformP`. | The scan itself records the terminator only in its final head position.  The standalone gamma counter described below now preserves the prefix length on tape, but is destructive; global value-preserving parser composition remains open. |
| Fixed-control gamma front end | The 57-state value-preserving zipper has exact arbitrary-list cycle composition, first-hit control, shifted `front`/`tail`/suffix preservation, useful time `5*k^2+4*k+2` from its sentinel, and a step-for-step bridge to the actual finite repository `TM`.  The 181-state wrapper validates tag `179` and transforms three canonical gamma fields in exact time `5*(k1^2+k2^2+k3^2)+4*(k1+k2+k3)+11`; the exact run is also transferred to the actual finite `TM` and its longer quartic clock. | The three-field result is deliberately one-sided.  A formal actual-TM prefix-closure theorem shows that every arbitrary finite suffix is untouched and accepted after the wrapper enters absorbing `done`.  Thus exact-length parser soundness is false for this machine and requires an end-check redesign; no global padded-row decider follows. |
| Block driver | A generic positive-block-length driver with exact last partial block, immediate propagation of genuine `noCircuit`, an induction invariant, and final `found iff HasCircuit` / `noCircuit iff not HasCircuit` endpoints | `paperBlockLength c s = c * s * ceil(log_2(s+2))` is defined separately and is positive for positive `c,s`; the generic driver can be instantiated with it.  This does not supply the paper's oracle algorithm. |
| Result wire | A collision-free fixed-length Stream-Merge result wire with five semantic tags, a canonical empty body on non-circuit cases, and total/functional per-position output-bit graphs | The output-bit surface is only a finite semantic graph.  No finite-PH membership theorem is claimed for those bits. |
| Concrete MMW problem | The exact tagged total-search output is connected to completed operational runs, including full input consumption and both YES and NO semantics | This closes the problem specification, not existence of a solver. |

The merge constraint uses

```text
actualBlockLength = min nominalBlockLength (2^n - consumed),
```

so correctness includes the last partial block and all small-length edge
cases; it does not rely on the divisibility shortcut in the STOC pseudocode.

## Exact eventual quantifiers

For `s_k(n) = max n (n^k)`, the positive predicate has one program outside all
length quantifiers.  It then existentially chooses space/update exponents,
coefficients, a report coefficient, and one cutoff.  **Both correctness and
all resource bounds hold for every `n >= cutoff` and every truth table of
length `2^n`.**  In schematic form:

```text
exists one uniform StreamingRAM program M,
exists exponents, constants, cutoff,
forall n >= cutoff,
forall T : TruthTable n,
  M completes correctly on T for threshold s_k(n) and
  space(M,T), maxUpdateGap(M,T), reportTime(M,T)
    satisfy their stated polynomial envelopes in s_k(n).
```

`NoPolyStreamingSearchMCSPSolver k` negates that entire existential.  It is
not the assertion that one chosen machine or one chosen exponent fails.
`CorrectAtAllLengths` remains a stronger auxiliary notion and is not silently
substituted for this exact eventual normal form.

## Proved repository-model blocker

The current repository machine type contains an unrestricted field
`TM.runTime : Nat -> Nat`.  Membership in repository `P` bounds this field
pointwise but does not require it to be computable or time-constructible.
`RuntimeAdviceBarrier.lean` makes the consequence exact:

```text
forall A : Nat -> Bool,
  lengthAdviceLanguage A is in the current repository P,
```

using `runTime n = if A n then 1 else 0`.  The machine starts rejecting and
takes the single accepting transition exactly at lengths where `A n` is true.

This theorem proves that a current `P`-membership witness need not itself
expose a callable uniform `StreamingRAM.Program`; arbitrary length-indexed
information may reside in its runtime field.  Therefore the intended
`P = NP`-to-operational-algorithm step needs a prior repair or a separately
proved normalization/extraction theorem.

It does **not** prove that every conceivable compiler from some repaired
uniform model is impossible, and it does not assert an unformalized
noncomputability or cardinality theorem.  The blocker is specifically the
missing operational content of the definitions currently used by this
repository.

## Separate operational-uniformity repair

`OperationalUniformity.lean` introduces an additive repaired track without
changing the repository-wide classes:

- `OperationalTM` keeps one finite transition system and one exponent and has
  no `Nat -> Nat` field; its execution clock is `n^c + c` by definition and
  its Boolean output is a function
  of the final finite state, so deterministic complement changes only that
  output map and is proved by `uniformP_complement`;
- `UniformP` and `UniformNP` quantify over one such fixed program/verifier;
- `concatBitstring` is now the executable `Fin.addCases` construction rather
  than a `noncomputable` choice of the right-hand index;
- `CanonicalClockTM` is an explicitly numbered finite syntax with no
  `Nat -> Nat` field.  Its deterministic and verifier variants have proved
  one-way bridges into both the old repository `P` / `NP` and the repaired
  `UniformP` / `UniformNP`.  The latter compilation preserves the exact
  transition table and clock; an explicit configuration induction proves that
  changing the repository carrier's observational `accept` field does not
  change the run.

There is deliberately no theorem `UniformP subset repository-P` for arbitrary
Boolean output maps, no converse bridge from old witnesses, and no equality
between repaired and old classes.  The exact assumption relevant to a future
MMW reconstruction is
`forall L, UniformNP L -> UniformP L`, not the current repository equality.

The repaired classes also use an exact canonical clock and observe the final
state after exactly that many steps.  Equivalence with a conventional
early-halting machine padded by absorbing accept/reject states has not yet been
formalized.  `OperationalTM.ofRepoCore` only copies finite control while
discarding the old runtime field; it intentionally does not assert correctness
at the replacement clock.

`OperationalDynamicScan.lean` closes the first concrete input-uniform loop:
the same two-state controller handles every input length, its done state is
fully absorbing, and it accepts exactly the bitstrings containing a `true`
bit.

`OperationalGammaPrefix.lean` now supplies the next complete operational
checkpoint.  One fixed 12-state Boolean-tape controller converts a standalone
`0^k 1 payload[k]` field into a unary moving-marker trace and is proved to
reach its finished configuration after `1` useful step for `k = 0` and
`2*k^2 + 7*k` for positive `k`; it then
absorbs inside the canonical cubic clock.  The natural-coordinate trace is
proved equal to the repository `TM` execution; canonical `gammaBit` inputs end
with the head at `gammaLen`.  This first machine is deliberately destructive
and uses the physical left clamp at cell zero.  It also has an explicit theorem
showing that a truncated all-zero payload is accepted from blank work cells,
so it is not presented as a full parser.

`OperationalGammaZipper.lean` and its `Global`, `Active`, `Context`, and
`Actual` companions remove the payload-destruction obstacle end to end.  The
fixed 57-state sentinel machine uses alternating pairs; arbitrary-list local
kernels compose to the literal final frame, the exact useful clock is
`5*k^2 + 4*k + 2` from the sentinel, and no earlier state is `done` or
`reject`.  The same result holds after any finite front while preserving a
finite tail and an arbitrary infinite suffix.  A step-for-step finite-tape
simulation proves the canonical frame is accepted by the actual repository
machine at its longer cubic clock.

`OperationalTaggedGamma.lean`, `OperationalTaggedGammaGlobal.lean`,
`OperationalTaggedGammaActual.lean`, and
`OperationalTaggedGammaPrefixClosure.lean` give a fixed 181-state front end that validates
the real byte `179 = 10110011`, reuses tag bit seven as the first sentinel, and
delegates three consecutive gamma fields to the same zipper controller.  The
phase handoffs, first-hit simulation, constant state count, codec tag equality,
length-preserving frame algebra, and the full canonical-prefix run are proved.
A step-for-step bridge transfers the exact endpoint to the repository's actual
finite tape and proves acceptance at its longer quartic clock.  The actual-TM
prefix-closure theorem then proves that every arbitrary finite suffix is
preserved literally and accepted.  Hence exact ambient-length soundness is
false for the present absorbing-`done` design, not merely an unfinished proof.

`OperationalRequestHandoff.lean` now connects that front end to the literal
`StreamMergeRequestCodec.encodeRequest`, rather than only to an abstract
three-word frame.  It proves that each codec gamma word is exactly a zipper
body with width `bitLength(value + 1) - 1`, and that the encoded request is
literally
`tripleInitialFrame ++ start ++ prior ++ block ++ position`.  The three
operational field starts coincide with `tagLen`, `sOffset`, and
`blockLengthOffset`; most importantly,
`tripleFootprint = startOffset`.  A direct step-for-step theorem for
`runConfig (initialConfig (encodeRequest request))` reaches `done` at the exact
three-field time with its head on the first `start` bit and its actual finite
tape agreeing cell-for-cell with the transformed gamma prefix plus the
untouched four-field tail.  This is a canonical-request handoff theorem, not a
parser for that tail or a sound acceptance theorem.

`OperationalTaggedGammaShapeBarrier.lean` records a separate information-loss
boundary at that handoff.  The concatenations
`zippedBody [] ++ zippedBody [true]` and
`zippedBody [true] ++ zippedBody []` are identical.  Swapping these first two
payload shapes also preserves the aggregate footprint, exact useful time, and
the complete transformed natural handoff configuration when the third payload
and suffix are fixed.  Consequently no function of the transformed triple
frame alone can recover the ordered first two widths on every input.  This is
not a collision of two full canonical Stream-Merge requests: a redesigned
wrapper can retain the three zero-width flags in eight fixed control variants,
or use additional tail information.  The theorem rules out only silent
post-hoc width recovery from the present transformed prefix.

`OperationalClockBoundary.lean` rules out a tempting local workaround at the
model level.  For every repository TM, the head still has strict room for a
right move before each transition of its canonical run, so the physical right
clamp cannot reveal the ambient input boundary.  Cross-length simulation also
proves that an input and any all-zero extension have exactly the same state,
numeric head, and common tape cells throughout the shorter canonical trace.
A two-state toggle witness confirms that length is nevertheless observable
through the externally chosen final sampling time.  Thus, for distinguishing
an input from an all-zero extension in the present model, the remaining
ambient-length channel is clock scheduling, not scanning a blank or probing
the finite-tape clamp.

`OperationalLeftClampProbe.lean` supplies the first tape-backed timer
primitive on the other boundary.  One fixed 19-state Boolean controller uses
the complement of the saved right-neighbour bit as a temporary marker.  In
exactly six steps it distinguishes `head = 0` from `head > 0`, returns the
head to its original `Fin` coordinate, and restores the whole tape
extensionally.  The actual finite-tape theorem needs only the sharp one-cell
premise `head + 1 < tapeLength`, rather than a coarse
six-cell reserve.  This detects the fixed physical origin, not the ambient
input end, and is therefore a navigation kernel for a future tape timer rather
than an end-of-request test.

`OperationalTaggedGammaPulse.lean` now closes the smallest end-sensitive
experiment without changing the parser's finite control: `done` is a one-tick
accepting pulse followed by absorbing `reject`.  A new composed first-hit
theorem proves that the tag-plus-three-gamma run visits neither terminal state
before its exact useful endpoint, and a second finite-tape bridge transfers the
pulse trace to the actual repository semantics.  The result is a sharp no-go:
the immediate pulse rejects even the exact canonical triple, as well as every
finite continuation, because the useful trace ends strictly before the
quartic observation clock.

The missing delay is no longer implicit.  For
`S = k₁ + k₂ + k₃` and
`C = k₁*k₂ + k₁*k₃ + k₂*k₃`, it is exactly
`16*S^4 + 352*S^3 + 2899*S^2 + 10644*S + 14634 + 10*C`.
The file proves positivity, equality with `runTime - taggedTripleTime`, and
the decomposition into a distribution equalizer `10*C` followed by a
length-only quartic filler.  It also proves the cubic filler identity.  A
concrete counterexample, `(2,0,0)` versus `(1,1,0)`, shows that no additive
post-parse delay which depends only on the aggregate footprint can align the
unmodified traces.
These are arithmetic targets for a future fixed-control tape timer, not a
timer supplied as advice or an assumed implementation.

## What remains unproved

The valid-call output-bit problem is now exactly one literal repaired-model
`EAEProject` over a global decidable padded row, as a language equality rather
than only a valid-request slice theorem.  There is still no `OperationalTM`
deciding that global row with proved polynomial bounds.  The fixed-control
zero-prefix counter, globally composed value-preserving zipper, exact
tag-plus-three-gamma canonical-prefix run, and direct handoff at the real
encoded request's `startOffset` now exist, but a redesigned
finite-input/end check, malformed-input rejection, decoded-value operations,
operational parsers for `start`, `prior`, `block`, and `position`, DAG row
evaluation, and full parser composition are still
open.  There is also no bridge from conventional `P = NP` to equality of the
repaired classes, no reconstruction of the paper's sequential
oracle calls as one `StreamingRAM.Program`, and no polynomial
space/update/report analysis of such a program.  Consequently this branch
contains neither the MMW upper direction nor its contrapositive capstone.

The single minimal open theorem signature is retained **in prose only**:
for every `k >= 1`, repaired `UniformNP subset UniformP` should imply
`PolyStreamingSearchMCSPSolvable k`.  Before attempting that theorem, the
ambient-length discipline must be completed, then the
global parser and padded row must be decided by one `OperationalTM` with a
proved polynomial clock, and the operational TM-to-streaming-RAM compiler
must be constructed.  Connecting the repaired
class equality back to the old mainline additionally
requires a normalization/extraction bridge.  These open statements must not be
encoded as an axiom, typeclass, `Contract`, `Source`, `Provider`, structure
field, or implicit instance.

The next constructive object is correspondingly precise: compose the proved
left-clamp probe into a fixed-state, tape-backed walk/equalizer/timer that
physically realizes the proved transition counts, together with a nonterminal
continuation state at the now-proved `startOffset` handoff which retains the
bounded gamma-shape flags before the present wrapper collapses to `done`.  It
may not put `kᵢ`, the delay, or the ambient length in the control state.  The
three gamma fields are only the beginning of an
actual Stream-Merge request: the four tail fields are preserved and their
starting coordinate is now proved exactly, but `start`, `prior`, `block`, and
`position` still have to be operationally parsed.
The unique acceptance pulse for the final machine must therefore be scheduled
only after those fields and the row check, against the full
`requestLength n s blockLength start`; the triple-level pulse in the barrier
module is deliberately not presented as a repaired request parser.

## Later-literature check (through 2026-07-10)

- [Chen--Jin--Santhanam--Williams, Lemma 3.2](https://theoretics.episciences.org/12881/pdf)
  gives a clean constructive/one-sided-error specialization of the same merge
  route, but still relies on Circuit-Min-Merge and PH collapse.
- [Williams, ECCC TR25-017, Theorem 1.1](https://eccc.weizmann.ac.il/report/2025/017/download/)
  simulates multitape time in square-root space; Remark 1.6 does not extend it
  to arbitrary random-access models.  It is not an operational extraction
  theorem for the present `P` interface.
- Recent conditional MCSP-hardness results concern different targets and do
  not supply the missing output-bit verifier, uniform normalization, or RAM
  compiler for the MMW streaming construction.
- The newest ECCC report scan through July 10 includes
  [conditional implicit-MCSP hardness (TR26-091)](https://eccc.weizmann.ac.il/report/2026/091/)
  and [unrelated quantum search/streaming lower bounds (TR26-117)](https://eccc.weizmann.ac.il/report/2026/117/),
  but no theorem realizing the MMW global row or closing the unconditional
  target.

No primary source found in this audit supersedes MMW Theorem 1.3 or closes the
exact model and operational gaps above.  This literature finding is not a
complexity lower bound.
