# Streaming magnification status

Status: **GLOBAL EAE BRIDGE AND FIXED GAMMA FRONT END ADDED; ROW-TM/GLOBAL PARSER/NORMALIZATION/COMPILER BLOCKERS; NO MMW UPPER THEOREM OR CAPSTONE**

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

`OperationalGammaZipper.lean` removes the payload-destruction obstacle at the
finite-control level.  Its fixed 57-state sentinel machine uses alternating
pairs: the proved local kernels implement `b,0 -> 0,b`, move the delimiter,
and implement `x,0,b -> b,0,x`.  Initial, cycle, and final frames have the same
`2*k+2` footprint.  The last pair ends in `1`, preserving the last payload bit
while providing the sentinel for the next gamma word.  The remaining precise
proof obligation is the global induction composing those local kernels over
an arbitrary processed-bit list.

`OperationalTaggedGamma.lean` is a fixed 181-state front end that validates
the real byte `179 = 10110011`, reuses tag bit seven as the first sentinel, and
delegates three consecutive gamma fields to the same zipper controller.  The
phase handoffs, constant state count, quartic clock, codec tag equality, and
length-preserving three-field frame algebra are proved.  No global run theorem
is claimed before the zipper induction and an exact ambient-length check are
available.

## What remains unproved

The valid-call output-bit problem is now exactly one literal repaired-model
`EAEProject` over a global decidable padded row, as a language equality rather
than only a valid-request slice theorem.  There is still no `OperationalTM`
deciding that global row with proved polynomial bounds.  The fixed-control
zero-prefix counter, value-preserving two-symbol zipper, and executable
tag-plus-three-gamma wrapper now exist, but the zipper's arbitrary-list run
induction, exact finite-input/end check, decoded-value operations, remaining
request fields, DAG row evaluation, and full parser composition are still
open.  There is also no bridge from conventional `P = NP` to equality of the
repaired classes, no reconstruction of the paper's sequential
oracle calls as one `StreamingRAM.Program`, and no polynomial
space/update/report analysis of such a program.  Consequently this branch
contains neither the MMW upper direction nor its contrapositive capstone.

The single minimal open theorem signature is retained **in prose only**:
for every `k >= 1`, repaired `UniformNP subset UniformP` should imply
`PolyStreamingSearchMCSPSolvable k`.  Before attempting that theorem, the
zipper induction and ambient-length discipline must be completed, then the
global parser and padded row must be decided by one `OperationalTM` with a
proved polynomial clock, and the operational TM-to-streaming-RAM compiler
must be constructed.  Connecting the repaired
class equality back to the old mainline additionally
requires a normalization/extraction bridge.  These open statements must not be
encoded as an axiom, typeclass, `Contract`, `Source`, `Provider`, structure
field, or implicit instance.

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
