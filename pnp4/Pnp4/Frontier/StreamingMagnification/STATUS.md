# Streaming magnification status

Status: **MODEL/DEFINITION BLOCKER; FINITE REFERENCE LAYERS COMPLETE; NO MMW UPPER THEOREM OR CAPSTONE**

Base: `main@5d8ee5f80e1dbc4fb7bd0c725fa98f1a999770d0`

Local branch: `research/mmw-chmy-streaming-p-ne-np`

Primary sources:

- McKay, Murray, Williams, [*Weak lower bounds on resource-bounded compression imply strong separations of complexity classes*](https://people.csail.mit.edu/rrw/MCSP-MKTP-stoc19.pdf), STOC 2019 (MMW).
- Chen, Jin, Santhanam, Williams, [*Constructive Separations and Their Consequences*](https://theoretics.episciences.org/12881/pdf), TheoretiCS 2024, especially Lemma 3.2.
- Hirahara, Ilango, Williams, [*Beating Brute Force for Compression Problems*](https://eccc.weizmann.ac.il/report/2023/171/download), STOC 2024/ECCC TR23-171, especially Lemma 2.1.

## Result classification

The primary result of this branch is a **model/definition blocker**, not a
streaming lower bound and not a proof of `P != NP`.  The finite objects needed
to state and test the MMW construction are now concrete, but the repository's
current definition of `P` does not supply the operational uniformity needed to
extract a single streaming program from a `P = NP` hypothesis.

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
| Fixed DAG codec | A fixed-length circuit body, canonical padding, executable encode/decode, exact round trips and injectivity, finite enumeration, and an explicit `O(s log(n+s))` code-length bound | The codec can represent the broader structural carrier; successful target search additionally checks `UsesOnlyAndOrNot`. |
| Total search-MCSP | A genuine tagged `found`/`noCircuit` result with soundness and completeness in both directions; an executable exhaustive reference solver and exact decision bridge | This is finite reference computation, not a streaming-time algorithm. |
| Streaming RAM | One fixed length-aware one-pass bit program, explicit input cursor and next-bit requests, finite bit-local instruction palette, indirect addressing, write-only output/report phase, and trace-derived space, maximum update-gap, and report-time measures | This is the operational machine model.  No polynomial-resource Stream-Merge implementation has been constructed in it. |
| Stream-Merge reference | Executable finite size-then-physical-lex minimization, malformed-request semantics, exact final partial blocks, `blockLength > 2^n`, prefix agreement, optimality, and final `found`/`noCircuit` equivalences | The reference search may enumerate the entire code cube and evaluate whole tables, so it proves no RAM resource bound. |
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

## What remains unproved

There is no formal finite polynomial-hierarchy hierarchy in this route, no
proof that Stream-Merge or Circuit-Min-Merge output bits lie in the required
finite-PH level, no finite-PH collapse under `P = NP`, no reconstruction of
the paper's oracle calls as a uniform RAM program, and no polynomial
space/update/report analysis of such a program.  Consequently this branch
contains neither the MMW upper direction nor its contrapositive capstone.

The single minimal open theorem signature is retained **in prose only**:
for every `k >= 1`, repository-uniform `P = NP` should imply
`PolyStreamingSearchMCSPSolvable k`.  Before attempting that theorem, the
repository must use a genuinely operational uniform definition or prove the
missing normalization/extraction bridge.  This open statement must not be
encoded as an axiom, typeclass, `Contract`, `Source`, `Provider`, structure
field, or implicit instance.
