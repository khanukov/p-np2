# Source Search Contract Expansion — R1-B Prefix Language

## Status

**OPEN — R1-B only.**

R1-C is gated. Full contract expansion is **NOT** authorised.

## Progress classification

Infrastructure / interface specification for the mainline source-search contract expansion.

R1-B may specify and, in a later worker execution, optionally stage the NP prefix-extension language interface. It must not be reported as an unconditional `P != NP` advance, and it must not claim a lower-bound endpoint.

## Why R1-B exists

R1-A approved the `C_DAG` adapter and alignment between the pnp4 circuit-family view and the frozen pnp3 DAG-circuit interface. R1-B now defines the prefix-extension language and its NP verifier.

The intended role is limited: make the language and verifier precise enough that a later, separately gated R1-C extraction step can be evaluated without ambiguity. R1-B does not perform that extraction.

## Purpose

Specify and optionally begin formalizing:

- `L_prefix_target`

for a concrete tree-MCSP search target.

The language should depend only on the concrete target problem, parser/codec data, and the relation being verified. It must not depend on a solver, a lower-bound contradiction, or any endpoint witness.

## R1-B authorised deliverables

### A. Prefix language specification

The worker may provide a Lean skeleton or precise markdown report that fixes the following details.

1. **Input format**
   - Encoded input has fields `⟨tag,n,x,i,p,pad⟩`.
   - `tag` identifies the prefix-extension language version and must reject unrelated encodings.
   - `n` is the underlying target length.
   - `x` is the target instance of length `problem.instanceBits n`.
   - `i` is the prefix length, bounded by `problem.witnessBits n`.
   - `p` is the proposed witness prefix of length `i` or a fixed-width padded representation with only the first `i` coordinates active.
   - `pad` exists only to enforce the agreed length convention and must carry no hardness content.

2. **Length convention `M(n)`**
   - Prefer a single canonical ambient length `M(n)` for every well-formed encoding at target length `n`.
   - `M(n)` must include the tag, encoding of `n`, instance bits, prefix index, prefix payload, and padding budget.
   - The convention should be monotone or otherwise easy to audit for polynomial bounds.
   - Any deviation from a single-length convention must be explicitly justified in the report.

3. **Malformed input behavior**
   - Malformed inputs are nonmembers.
   - Rejection must be syntactic and must not hide a promise, lower bound, solver failure, diagonalization, or endpoint assumption.
   - Examples of malformed inputs include bad tags, inconsistent lengths, out-of-range `i`, incorrectly sized `x` or `p`, and invalid padding.

4. **Membership condition**
   - For a well-formed input `⟨tag,n,x,i,p,pad⟩`, membership means that there exists a full witness `w` of length `problem.witnessBits n` such that:
     - `w` agrees with prefix `p` on the first `i` witness coordinates; and
     - `problem.relation n x w` holds.
   - If the concrete tree-MCSP relation already implies the promise, prefer the relation-only condition to avoid adding a separate promise-decidability obligation. Otherwise, state the required promise condition explicitly.

### B. NP verifier specification

The worker may specify or stage an NP verifier with the following components.

1. **Witness `w`**
   - The NP witness is the full target witness of length `problem.witnessBits n`.
   - Any auxiliary codec witness must be accounted for explicitly and bounded polynomially in the ambient input length.

2. **Prefix agreement**
   - The verifier checks that `w` agrees with `p` for all positions below `i`.
   - The report must specify how `p` is decoded and how inactive padded prefix positions are ignored or constrained.

3. **Relation check**
   - The verifier checks the concrete target relation, intended for the tree-MCSP search target.
   - Codec assumptions required for checking the relation must be listed rather than hidden.

4. **Codec requirements**
   - The parser and witness codec must be deterministic, canonical enough for audit, and polynomial-time decodable.
   - The verifier must identify all required size schedules, including the tree-circuit witness encoding length and any threshold parameter.

5. **Polynomial witness-length/runtime conditions**
   - The verifier specification must state polynomial bounds for witness length and verification runtime as functions of the ambient language input length `M(n)`.
   - If the current interfaces do not expose enough data to prove these bounds, the worker must record the exact missing budget as a structured failure or audit note.

### C. Optional Lean skeleton only if safe

A later R1-B worker may land a Lean skeleton only if it is safe and stays inside the authorised scope. Acceptable contents are limited to:

- parser data structures;
- predicate definitions;
- language definition;
- NP verifier theorem only if the verifier budget is explicit.

If a Lean module is attempted, it must be one of the paths named in `WORKER_PROMPT_R1B.md`, and it must not introduce an extraction theorem or endpoint consequence.

## Explicit non-goals

R1-B must not construct, prove, or edit any of the following:

- extraction theorem;
- `PpolyDAG` lower bound;
- `BoundedSearchSolver`;
- `target.noBoundedSolver` contradiction;
- `VerifiedNPDAGLowerBoundSource`;
- `ResearchGapWitness`;
- endpoint;
- R1-C;
- `SourceTheorem` or `gap_from`.

## Success criteria

### Outcome A

A Lean module or precise markdown report lands defining or staging `L_prefix_target` and its NP verifier.

### Outcome B

A structured failure explains why the prefix language or NP verifier cannot be cleanly specified.
