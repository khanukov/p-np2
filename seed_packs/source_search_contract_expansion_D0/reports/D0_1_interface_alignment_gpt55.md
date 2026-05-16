# D0.1 interface alignment and extraction design — `gpt55`

Seed pack: `source_search_contract_expansion_D0`  
Slot: D0.1 — interface alignment and extraction design for SearchMCSP contract expansion  
Scope: markdown-only.  No Lean code, no lakefile edits, no JSONL/spec/trust-root edits, no Round 1 seed pack.

## 1. Executive verdict

**READY_FOR_OPERATOR_REVIEW**

D0.1 makes the five missing design pieces precise enough for an operator to
decide whether a *limited* Round 1 should be opened.  This is not a GREEN-light
for the mathematical source theorem and not an endpoint claim.  It is only a
review-ready design for the prefix-extension extraction route identified in D0.

The core result of this memo is:

- a pnp4 `CircuitFamilyClass` can represent the frozen pnp3 `DagCircuit` model
  by an interface wrapper without changing trust roots;
- this wrapper is definitionally aligned at the slice level, while its relation
  to `PpolyDAG` is polynomial-bound/package-level, not definitional;
- the prefix-extension language can be specified without a solver, diagonal
  choice, advice, or hidden `noBoundedSolver` assumption;
- the NP verifier is realistic for the codec-shaped tree-MCSP target, but still
  requires concrete bit-serialization and runtime lemmas;
- the decider-to-solver extraction has a polynomial-size design **if** Round 1
  formalizes a shared-DAG sequential composition lemma rather than recursively
  inlining previously constructed output circuits.

The main risk is therefore not an immediate wrapper/circularity failure.  The
main risk is whether the required DAG closure/composition and concrete codec
lemmas can be proved cleanly without modifying trust roots.

## 2. DAG class alignment memo

### 2.1 What `CircuitFamilyClass` expects

The pnp4 interface `CircuitFamilyClass` is intentionally minimal.  It provides:

```text
Family : Nat → Type
eval   : Family n → BitVec n → Bool
size   : Family n → Nat
```

It does not itself contain a polynomial bound, a language, a correctness field,
or a closure theory.  Those must be supplied by separate packages or theorems.
This is good for interface wrapping, but it means that simply defining a class
is not the same as proving membership in `PpolyDAG`.

### 2.2 What pnp3 `PpolyDAG` provides

The frozen pnp3 DAG endpoint is:

```text
InPpolyDAG L where
  polyBound      : Nat → Nat
  polyBound_poly : ∃ c, ∀ n, polyBound n ≤ n^c + c
  family         : ∀ n, DagCircuit n
  family_size_le : ∀ n, DagCircuit.size (family n) ≤ polyBound n
  correct        : ∀ n x, DagCircuit.eval (family n) x = L n x

PpolyDAG L := ∃ _ : InPpolyDAG L, True
```

Thus `PpolyDAG` is a language-level nonuniform polynomial-size package.  It is
not itself a circuit-class object.  The class wrapper must expose the slice
syntax and semantics; a separate equivalence/alignment statement must relate
polynomial-size `C_DAG` families to `PpolyDAG`.

### 2.3 Size alignment

The pnp3 DAG size is:

```text
DagCircuit.size C = C.gates + 1
```

A pnp4 wrapper should use exactly this size measure:

```text
C_DAG.Family n := Pnp3.ComplexityInterfaces.DagCircuit n
C_DAG.eval C x := Pnp3.ComplexityInterfaces.DagCircuit.eval C x
C_DAG.size C := Pnp3.ComplexityInterfaces.DagCircuit.size C
```

This is definitionally aligned up to namespace/import details: no new circuit
semantics, size measure, or trust-root object is needed.

### 2.4 Can pnp4 wrap pnp3 `DagCircuit` without changing trust roots?

Yes, as an interface wrapper.  The wrapper would not redefine `PpolyDAG`,
`DagCircuit`, `DagCircuit.size`, or `DagCircuit.eval`; it would point pnp4's
neutral `CircuitFamilyClass` fields at the existing frozen pnp3 data.  That is a
safe direction for a future limited Round 1 because it adds an adapter, not a new
endpoint.

### 2.5 Definitional vs polynomial-equivalent vs missing

The alignment has three layers:

1. **Slice syntax/semantics:** definitional wrapper over pnp3 `DagCircuit`.
2. **Size measure:** definitional wrapper over `DagCircuit.size`.
3. **Language-level polynomial class:** polynomial-equivalent package theorem,
   not definitional, because `CircuitFamilyClass` alone lacks `polyBound` and
   correctness fields.

### 2.6 Proposed alignment statement

A future Round 1 should target a statement of the following shape, modulo exact
names:

```text
PpolyDAG_as_CircuitFamilyClass_alignment:
  Let C_DAG be the pnp4 CircuitFamilyClass with
    Family n = pnp3 DagCircuit n,
    eval = DagCircuit.eval,
    size = DagCircuit.size.

  (A) Any pnp3 InPpolyDAG L gives a polynomially bounded nonuniform C_DAG
      family computing L.

  (B) Any polynomially bounded nonuniform C_DAG family computing L gives
      pnp3 PpolyDAG L.
```

For the extraction, the most important corollary is narrower:

```text
PpolyDAG_decider_as_C_DAG_decider:
  PpolyDAG L_prefix_target
  → for every encoded length m, obtain a C_DAG circuit D_m deciding L at length m,
    with size bounded by m^c + c for some global c.
```

This corollary is currently missing but appears interface-safe.

## 3. Prefix language specification

### 3.1 Target family

Use the tree-MCSP target shape from the existing seed pack:

```text
target = treeMCSPSearchWeakLowerBoundTarget threshold encoding C_DAG sizeBound
```

For D0.1, `C_DAG` is the wrapper class from §2.  The problem is:

```text
problem = treeMCSPSearchProblem threshold encoding
```

At target length `n`:

```text
x : BitVec (problem.instanceBits n)
problem.instanceBits n = tableLen n
w : BitVec (problem.witnessBits n)
```

For tree-MCSP, `x` is the full truth table on `n` input variables.

### 3.2 Encoded input format

Define a pnp3 language `L_prefix_target : Language`.  An input bitstring `y` of
length `m` is parsed as either malformed or as:

```text
⟨tag, n, x, i, p, pad⟩
```

Fields:

- `tag`: fixed marker for this prefix language;
- `n`: self-delimiting binary or unary/binary canonical encoding of the target
  length;
- `x`: exactly `problem.instanceBits n` bits;
- `i`: an index with `0 ≤ i ≤ problem.witnessBits n`;
- `p`: a fixed-width `problem.witnessBits n`-bit area, of which only the first
  `i` bits are active;
- `pad`: deterministic padding so all accepted encodings have a predictable
  length schedule.

Using fixed-width `p` avoids variable-length prefix encodings inside the final
language.  The active prefix relation is:

```text
prefix_i(w) = active_prefix_i(p)
```

meaning `w k = p k` for every `k < i`.

### 3.3 Length convention

A future formalization should choose a monotone schedule:

```text
M(n) = encOverhead(n) + problem.instanceBits n + problem.witnessBits n
```

where `encOverhead(n)` covers `tag`, `n`, `i`, and padding.  The parser should
ensure that all well-formed inputs at target length `n` have length exactly
`M(n)` or lie in a small finite set `M(n,i)` with a canonical map back to `n`.
For extraction simplicity, D0.1 recommends the single-length-per-`n` convention
`M(n)`.

Malformed inputs are **nonmembers**.  Malformed behavior must be trivial and
must not encode hardness.

### 3.4 Membership condition

For a well-formed input `y = ⟨tag,n,x,i,p,pad⟩`:

```text
L_prefix_target m y = true
iff
  problem.promise n x ∧
  ∃ w : BitVec (problem.witnessBits n),
    (∀ k < i, w k = p k) ∧
    problem.relation n x w
```

For tree-MCSP with a codec-induced encoding, `problem.relation n x w` says that
`w` verifies as an encoding of a tree circuit of size at most `threshold n` that
computes truth table `x`.

### 3.5 Promise handling

The promise is included in membership, not assumed externally by the language.
For tree-MCSP this is safe because the codec relation is sound:

```text
relation n x w → promise n x
```

Therefore the explicit `problem.promise n x` conjunct can be redundant for the
codec path, but keeping it in prose clarifies that the prefix language is about
promised instances.  In formal work, prefer the relation-only form if it avoids a
separate promise-decidability obligation:

```text
∃ w, prefix_i(w)=p ∧ relation n x w
```

because relation soundness then supplies the promise.

### 3.6 Dependency audit

| Question | Answer | Risk |
| --- | --- | --- |
| Does `L_prefix_target` depend on the solver? | No.  It depends only on `target.problem`, parser data, and relation. | addressed |
| Does it depend on a diagonal choice? | No.  It does not enumerate or diagonalize against DAGs. | addressed |
| Does it use nonuniform advice? | No in the definition.  Nonuniformity appears only later when assuming `PpolyDAG L`. | addressed |
| Does it hide `noBoundedSolver`? | No.  `noBoundedSolver` is not used in membership. | addressed |
| Does it hide `¬ PpolyDAG`? | No.  Hardness is intended to follow from extraction. | addressed if extraction is explicit |

## 4. NP verifier design

### 4.1 Witness format

For input `y = ⟨tag,n,x,i,p,pad⟩`, the NP witness is a full target witness:

```text
w : BitVec (problem.witnessBits n)
```

For the tree-MCSP codec route, this is an encoded tree circuit.  No solver, DAG
lower-bound certificate, or nonuniform advice is included in the witness.

### 4.2 Witness length

The witness length is:

```text
problem.witnessBits n
```

A future Round 1 must prove:

```text
problem.witnessBits n ≤ poly(M(n))
```

For a concrete `TreeCircuitWitnessCodec`, this should follow if the chosen
serialization uses `poly(threshold n, n)` bits and `threshold n ≤ poly(tableLen n)`.
It is not guaranteed by the abstract `TreeMCSPSearchWitnessEncoding` interface.

### 4.3 Verifier algorithm

On input `y` and witness `w`:

1. Parse `y` as `⟨tag,n,x,i,p,pad⟩`.
2. Reject if parsing fails.
3. Reject if `i > problem.witnessBits n`.
4. Check prefix agreement: for all `k < i`, `w k = p k`.
5. Check `problem.relation n x w`.
6. Accept iff all checks pass.

For the codec route, step 5 expands to:

1. decode `w` as a tree circuit `c`;
2. check `Circuit.size c ≤ threshold n`;
3. evaluate `c` on all `2^n = tableLen n` assignments;
4. compare the resulting truth table to `x`.

### 4.4 Verification time against encoded input length

The prefix check costs `O(problem.witnessBits n)`.  The tree-MCSP relation check
costs approximately:

```text
poly(decode_time(w)) + tableLen n × eval_time(c)
```

This is polynomial in `M(n)` if:

- `problem.witnessBits n ≤ poly(M(n))`;
- decode is polynomial in witness length;
- `Circuit.size c ≤ threshold n ≤ poly(M(n))`;
- circuit evaluation is polynomial in circuit size and assignment length.

### 4.5 Current-interface realism

- For an arbitrary `SearchMCSPCompressionProblem`, this NP verifier is **not**
  realistic yet because `relation` is merely a `Prop`, not a time-bounded
  decidable verifier.
- For `treeMCSPSearchProblem` built from `TreeMCSPSearchWitnessEncoding`, it is
  still underspecified because `verifies` is abstract.
- For `treeMCSPSearchProblem` built via `TreeCircuitWitnessCodec`, it is
  realistic but still needs new concrete codec definitions: bit serialization,
  decode runtime, size bound of serialization, and truth-table evaluation budget.

D0.1 status: **ready for operator review, but Round 1 must start with the codec
and verifier budget, not with the final magnification theorem.**

## 5. Extraction size ledger

### 5.1 Assumption and goal

Assume:

```text
PpolyDAG L_prefix_target
```

Via §2 alignment, obtain DAG deciders `D_m` of size:

```text
|D_m| ≤ m^c + c
```

for a global constant `c`.

Goal:

```text
BoundedSearchSolver target.problem C_DAG sizeBound
```

where `C_DAG` is the pnp4 wrapper around pnp3 `DagCircuit`.

### 5.2 Sequential shared-DAG extraction

For each target length `n`, build a **multi-output design DAG** internally and
then expose each output bit as a single-output DAG circuit.

Let:

```text
W(n) := problem.witnessBits n
M(n) := encoded prefix-language length for target length n
D(n) := size of the L_prefix_target decider at length M(n)
E(n) := size overhead for parser/encoder wiring for one query
```

At stage `j`, the circuit has already created wires for bits
`b_0(x), ..., b_{j-1}(x)`.  To create `b_j(x)`, it wires a query
`⟨tag,n,x,j+1,prefix=b_0...b_{j-1}1,pad⟩` into a fresh copy of `D_{M(n)}`.
The output of that decider copy is `b_j`.

This is the lexicographically-1-preferring search rule:

```text
b_j(x) = D_{M(n)}(encode(n, x, j+1, b_0(x)...b_{j-1}(x) 1))
```

If the `1` extension is possible, choose `1`; otherwise choose `0`.  The
invariant is that the chosen prefix remains extendable on promised instances.

### 5.3 Recurrence

The **bad recurrence** to avoid is recursive inlining of previously exported
single-output circuits:

```text
S_{j+1} ≤ D + E + Σ_{k≤j} S_k
```

This can become exponential in `j`.

The required shared-DAG construction instead uses previous prefix bits as
already-computed internal wires inside one growing DAG for the same output
length `n`.  Let `T_j(n)` be the size of the shared DAG after constructing prefix
bits `0..j-1`.  Then:

```text
T_0(n)      ≤ E_0(n)
T_{j+1}(n)  ≤ T_j(n) + D(n) + E(n) + O(1)
T_W(n)      ≤ E_0(n) + W(n) × (D(n) + E(n) + O(1))
```

The exported circuit for bit `j` is the prefix of this shared DAG ending at wire
`b_j`, so:

```text
S_j(n) ≤ E_0(n) + (j+1) × (D(n) + E(n) + O(1))
```

This is polynomial if `W(n)`, `M(n)`, `D(n)`, and `E(n)` are polynomial in the
original instance length.

### 5.4 Solver correctness

On a promised input `x`:

- `totalOnPromise` gives at least one valid witness, so the empty prefix is
  extendable.
- If prefix `p` is extendable, then at least one of `p0` or `p1` is extendable.
- The decider returns whether `p1` is extendable.  If yes, choose `1`; if no,
  choose `0`, which must be extendable.
- After `W(n)` stages, the full produced bitstring is extendable only by itself,
  hence satisfies `problem.relation n x output(x)`.

Thus a correct decider for `L_prefix_target` yields a bounded search solver,
provided the size bound absorbs `S_j(n)`.

### 5.5 Ledger table

| object | size/cost | dependency | risk |
| --- | --- | --- | --- |
| `L` decider DAG `D_{M(n)}` | `D(n) ≤ M(n)^c + c` | `PpolyDAG L_prefix_target` plus DAG-class alignment | medium: needs pnp3-to-pnp4 adapter theorem |
| encoder/parser circuit | `E(n) = poly(M(n))` expected | fixed encoding of `⟨tag,n,x,i,p,pad⟩`; constants and projections | medium: not yet defined |
| previous prefix circuits/wires | shared internal wires, not recursively inlined | shared-DAG sequential construction | high if sharing lemma is not formalized |
| next-bit query circuit | `D(n) + E(n) + O(1)` per bit | one copy of decider plus hardwired `n,i,1,pad` and prefix wires | medium |
| output bit circuit `B_{n,j}` | `S_j(n) ≤ E_0(n) + (j+1)(D(n)+E(n)+O(1))` | projection of shared DAG up to bit `j` | medium/high: export-to-single-output lemma needed |
| full solver family | `W(n)` circuits, each size ≤ `T_W(n)` | one output circuit per witness bit as required by `BoundedSearchSolver` | medium |
| `sizeBound` needed | at least `E_0(n)+W(n)(D(n)+E(n)+O(1))` | chosen target schedule | high: existing target leaves it arbitrary |

### 5.6 Size-bound requirement

A review-ready target must set:

```text
sizeBound n ≥ E_0(n) + W(n) × (M(n)^c + c + E(n) + O(1))
```

for every polynomial exponent `c` arising from a hypothetical `PpolyDAG` decider.
Since `c` is not fixed in advance, the clean theorem should phrase `sizeBound`
as a polynomial-closure family or quantify over polynomial envelopes.  A single
near-linear `sizeBound` is unlikely to absorb the extraction.

This is the strongest design warning from D0.1: the prefix-extraction route
naturally proves hardness from absence of **polynomial-size DAG search solvers**,
not from an arbitrary weak near-linear solver lower bound unless the size loss is
made explicit.

## 6. Closure requirements

| closure lemma | existing in repo? | missing/easy/hard | trust-root risk |
| --- | --- | --- | --- |
| `C_DAG` wrapper over `DagCircuit` | missing as pnp4 adapter | easy | low, if definitional wrapper only |
| constants | likely constructible from `DagGate.const`, but no named pnp4 closure lemma | easy | low |
| projections/input wires | constructible from `DagWire.input`, but no named pnp4 closure lemma | easy | low |
| hardwired fixed bits | partly analogous to input masking infrastructure, but DAG-specific adapter missing | easy/medium | low |
| Boolean connectives | DAG syntax has `not`, `and`, `or`; named closure lemmas missing | easy | low |
| parser/encoder wiring | not present for this prefix language | medium | low if local adapter; high if it changes encodings globally |
| composition of DAG with input subcircuits | missing as a reusable theorem | hard | medium: must preserve frozen semantics and size accounting |
| sequential oracle-copy composition | missing | hard | medium |
| shared-subcircuit reuse/fanout | DAG model supports sharing syntactically, but extraction lemma missing | hard | low/medium |
| export one output wire of multi-output shared design as `DagCircuit` | multi-output design not currently an interface | hard | medium |
| polynomial size preservation | missing for this construction | hard | low if theorem-only |
| pnp4 `Family` to pnp3 `DagCircuit` conversion | trivial for `C_DAG`; missing for arbitrary `C` | easy for `C_DAG`, impossible for arbitrary `C` | low for `C_DAG`; high if generalized |
| `PpolyDAG` witness to bounded decider circuits | missing alignment corollary | medium | low |

The closure package must be theorem-only and adapter-only.  It must not redefine
`DagCircuit`, `PpolyDAG`, `size`, `eval`, `ResearchGapWitness`, or any endpoint.

## 7. Barrier mini-audit

### 7.1 Natural Proofs

Does the extraction define a large constructive useful property of Boolean
functions?  Not directly.  It defines a language tied to a search relation and
uses a search-to-decision transformation.  The proof of hardness is by
contradiction against `noBoundedSolver`, not by identifying a large set of truth
tables with an efficiently checkable property.

However, the endpoint is useful against `PpolyDAG`, and the verifier is
constructive.  Without a formal `NaturalProofBypassWitness`, this cannot be
called a bypass.

```text
natural_proofs_risk: medium
```

### 7.2 Relativization

The search-to-decision self-reduction is strongly relativizing: it treats the
`L_prefix_target` decider like an oracle and adaptively queries it.  That is not
fatal for an interface-level magnification contract, but it means the extraction
alone should not be advertised as a nonrelativizing final lower-bound proof.

```text
relativization_risk: medium/high
```

### 7.3 Algebrization

The design does not use arithmetization, low-degree extensions, or algebraic
oracles.  It therefore does not obviously algebrize, but it also provides no
explicit non-algebrizing ingredient.

```text
algebrization_risk: medium
```

### 7.4 Barrier conclusion

Do not overclaim a barrier bypass.  A limited Round 1, if opened, should be
advertised only as formalizing an interface/extraction transformation.  It should
not be advertised as endpoint progress or as a natural-proofs/relativization/
algebrization bypass.

## 8. NoGo / fake-progress cross-check

### 8.1 NOGO entries

| item | status | reason |
| --- | --- | --- |
| `NOGO-000001` | addressed | No `OverbroadUniformProvenance` or fixed-params support-bounds route is used. |
| `NOGO-000002` | addressed | No support-function range filter or alternating-slice exclusion is used. |
| `NOGO-000003` | addressed | No support-cardinality-only predicate is used; log-width truth-table hardwiring is not positive evidence. |
| `NOGO-000004` | addressed | The prefix-AND log-width counterexample is irrelevant to the extraction design. |
| `NOGO-000005` | addressed | The design does not patch only the prefix-AND special case. |
| `NOGO-000006` | addressed | Arbitrary all-essential log-width ttFormula payloads are not used as filters or witnesses. |
| `NOGO-000007` | addressed | The route is not support-cardinality-only. |
| `NOGO-000008` | addressed | The route is not a syntactic gate-count / OR-NOT filter. |
| `NOGO-000009` | addressed | No normalize-then-filter repair is used. |

### 8.2 Fake-progress checks

| hidden/fake-progress pattern | status | note |
| --- | --- | --- |
| hidden `VerifiedNPDAGLowerBoundSource` | addressed | The report demands construction of `L`, `NP L`, and `¬ PpolyDAG L`; it does not assume the package. |
| hidden `ResearchGapWitness` | addressed | Not used and remains forbidden. |
| hidden `SearchMCSPMagnificationContract` | addressed | The design replaces the contract with adapter/verifier/extraction pieces. |
| hidden `¬ PpolyDAG` | risk | Must be proved by extraction; any Round 1 shortcut here is a RED-light. |
| refuted support-bounds | addressed | No support-bounds theorem is cited. |
| wrapper field `target.noBoundedSolver → VerifiedNPDAGLowerBoundSource` | risk | Must not be introduced as `Hextract`; extraction must output explicit circuits. |
| arbitrary target `C` | risk | Extraction only aligns cleanly for `C = C_DAG`; arbitrary `CircuitFamilyClass` would be a wrapper/mismatch. |
| undersized `sizeBound` | risk | Near-linear or restricted size schedules likely do not absorb the polynomial oracle-composition overhead. |

## 9. Minimum Round 1 proposal, if any

Because the executive verdict is `READY_FOR_OPERATOR_REVIEW`, this report
proposes a limited Round 1 with **at most three slots**.  Do not create the Round
1 seed pack in D0.1.

### R1-A — DAG adapter and alignment statement

Scope: Lean or markdown+Lean skeleton, operator's choice.

Goal:

- define the pnp4 `C_DAG` wrapper around pnp3 `DagCircuit`;
- prove or state precisely the `PpolyDAG` ↔ polynomially bounded `C_DAG` family
  alignment;
- prove the corollary extracting length-indexed DAG deciders from
  `PpolyDAG L_prefix_target`.

Must remain forbidden:

- no trust-root changes;
- no new endpoint;
- no `ResearchGapWitness`;
- no `SearchMCSPMagnificationContract` assumption.

### R1-B — Prefix language and NP verifier

Scope: first markdown specification, then Lean only if R1-A is clean.

Goal:

- fix the parser and length convention for `L_prefix_target`;
- instantiate a concrete `TreeCircuitWitnessCodec` or explicitly record the
  codec gap;
- prove `L_prefix_target ∈ NP` only after witness length and verifier runtime are
  explicit.

Must remain forbidden:

- no hidden promise carrying hardness;
- no nonuniform advice in `L`;
- no endpoint theorem.

### R1-C — Shared-DAG extraction and size ledger

Scope: formalize closure lemmas only after R1-A establishes `C_DAG`.

Goal:

- prove constants/projections/hardwiring/connective closure;
- prove shared-DAG sequential oracle-copy composition;
- prove the size recurrence
  `S_j(n) ≤ E_0(n)+(j+1)(D(n)+E(n)+O(1))`;
- state the exact `sizeBound` envelope required for contradiction.

Must remain forbidden:

- no recursive-inlining proof that hides exponential blowup;
- no abstract `PpolyDAG L → BoundedSearchSolver` field without circuit
  construction;
- no final `VerifiedNPDAGLowerBoundSource` package until all components are
  proved.

## 10. Final recommendation

**operator_review_for_limited_round1**

D0.1 is review-ready because the interface alignment, prefix language, verifier
plan, extraction size recurrence, closure requirements, and barrier/fake-progress
risks are now explicit.  The operator should only open a limited Round 1 if they
accept the following constraints:

1. specialize the target to `C_DAG`, not an arbitrary `CircuitFamilyClass`;
2. formalize adapter/closure lemmas before any endpoint packaging;
3. use shared-DAG sequential composition to avoid exponential recursive inlining;
4. set `sizeBound` to an explicit polynomial envelope large enough for the
   extraction;
5. keep all endpoint, `ResearchGapWitness`, `SourceTheorem`, and `gap_from` work
   out of scope until the extraction theorem is real.

If any of those constraints is rejected, the recommendation should immediately
fall back to `repair_D0_1_before_round1` or `red_light_contract_expansion`.
