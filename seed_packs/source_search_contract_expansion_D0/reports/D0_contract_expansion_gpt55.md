# D0 contract-expansion feasibility report — `gpt55`

Seed pack: `source_search_contract_expansion_D0`  
Slot: D0 — SearchMCSPMagnificationContract expansion feasibility audit  
Scope: markdown-only; no Lean code, no JSONL/spec/trust-root/endpoint edits.

## 1. Executive verdict

**INCONCLUSIVE**

D0 found a plausible non-wrapper *shape* for expanding
`SearchMCSPMagnificationContract`: build an NP prefix-extension language whose
`PpolyDAG` decider can be self-reduced into output-bit circuits for the promised
search target.  However, this is not GREEN-light yet because the current
repository interfaces do not provide enough concrete data to make the
contrapositive extraction auditable for the selected target:

1. the `SearchMCSPWeakCircuitLowerBoundTarget.circuitClass` is an arbitrary
   `CircuitFamilyClass`, while the endpoint is specifically `PpolyDAG`;
2. there is no selected pnp4 `CircuitFamilyClass` instance corresponding to the
   frozen pnp3 `PpolyDAG` interface;
3. the required closure/composition theorem turning a nonuniform `PpolyDAG`
   decider for the constructed language into one circuit per witness bit is not
   present;
4. the tree-circuit witness encoding remains abstract, and no threshold / output
   size schedule has been fixed;
5. no explicit natural-proofs, relativization, or algebrization bypass witness is
   available.

This is also not RED-light at D0, because the proposed operational
prefix-extension route does **not** need to assume
`VerifiedNPDAGLowerBoundSource`, `ResearchGapWitness`, or a field of type
`target.noBoundedSolver → VerifiedNPDAGLowerBoundSource`.  The obstruction is
missing concrete reductions and barrier audits, not an already-detected wrapper.

## 2. Exact theorem surface

### 2.1 Surface under study

For a target with enough DAG-closure structure, the intended theorem surface is:

```text
contract_expansion_prefix_search
  (target : SearchMCSPWeakCircuitLowerBoundTarget)
  (Hcodec : concrete polynomial-time verifier / encoding data for target.problem.relation)
  (HdagModel : target.circuitClass is the frozen PpolyDAG family class)
  (Hprefix : polynomial-time prefix-extension language PrefixExt_target is defined)
  (Hextract : every PpolyDAG decider for PrefixExt_target yields
              a BoundedSearchSolver target.problem target.circuitClass target.sizeBound)
  : target.noBoundedSolver → VerifiedNPDAGLowerBoundSource
```

Equivalently, after expanding `VerifiedNPDAGLowerBoundSource`, the desired
conclusion is:

```text
target.noBoundedSolver →
  ∃ L, NP L ∧ ¬ PpolyDAG L
```

with:

- `L = PrefixExt_target`, explicitly constructed from the target relation;
- `NP L` proved by an explicit verifier for witness-prefix extendability;
- `¬ PpolyDAG L` proved by contraposition: a `PpolyDAG` decider for `L` gives a
  bounded search solver for the target, contradicting `target.noBoundedSolver`.

### 2.2 Existing hypotheses/interfaces

Already present in the repository:

- `SearchMCSPCompressionProblem`, with `instanceBits`, `witnessBits`, `promise`,
  `relation`, and `totalOnPromise`.
- `BoundedSearchSolver`, which packages one circuit per output witness bit plus
  a size bound and correctness condition.
- `SearchMCSPWeakCircuitLowerBoundTarget`, with `problem`, `circuitClass`, and
  `sizeBound`.
- `SearchMCSPWeakCircuitLowerBoundTarget.noBoundedSolver`, the no-bounded-solver
  proposition.
- `SearchMCSPMagnificationContract`, whose unexpanded field is precisely the
  implication under audit.
- `VerifiedNPDAGLowerBoundSource`, whose fields are an explicit language `L`, a
  proof `NP L`, and a proof `¬ PpolyDAG L`.
- `treeMCSPSearchProblem` and `treeMCSPSearchWeakLowerBoundTarget`.
- `TreeMCSPSearchWitnessEncoding` and `TreeCircuitWitnessCodec`, but only as
  abstract encoding/codec interfaces.

### 2.3 New hypotheses required by the proposed expansion

The following would be new and must not be hidden inside a wrapper field:

1. **Concrete pnp4-to-pnp3 DAG model alignment.**  A selected
   `CircuitFamilyClass` must compute exactly the frozen pnp3 `PpolyDAG` slices,
   with size measures related polynomially.
2. **Prefix-extension language definition.**  A concrete pnp3 language encoding
   `(n, x, i, p)` or a length-normalized bitstring containing an instance `x`, a
   prefix length `i`, and a witness prefix `p`.
3. **Polynomial-time verifier.**  A proof that prefix extendability for the
   target relation is in NP.
4. **Self-reduction / extraction theorem.**  From a `PpolyDAG` decider for the
   prefix-extension language, build `BoundedSearchSolver` output circuits.
5. **Closure and size accounting.**  DAG closure under constants, projections,
   composition with previously constructed output-bit circuits, and polynomial
   overhead small enough to fit `target.sizeBound` or a deliberately selected
   schedule.
6. **Barrier audits.**  Evidence that the route is not a large constructive
   useful property, or else an explicit reason it escapes natural-proofs,
   relativization, and algebrization barriers.

The new hypotheses are not allowed to include `VerifiedNPDAGLowerBoundSource`,
`ResearchGapWitness`, `NP_not_subset_PpolyDAG`, `SearchMCSPMagnificationContract`,
or any field of the form
`target.noBoundedSolver → VerifiedNPDAGLowerBoundSource`.

## 3. Concrete target

### 3.1 Target choice

The best D0 target to discuss is the existing tree-MCSP search weak-lower-bound
shape:

```text
treeMCSPSearchWeakLowerBoundTarget threshold encoding C sizeBound
```

This is concrete enough to name the problem and relation, but not yet concrete
enough for GREEN-light extraction because `threshold`, `encoding`, `C`, and
`sizeBound` remain parameters.

### 3.2 Problem

The underlying problem is:

```text
treeMCSPSearchProblem threshold encoding
```

At length `n`, the instance has:

```text
instanceBits n = Pnp3.Models.Partial.tableLen n
```

so the input is a truth table on `n` variables.

### 3.3 Promise

The promise is:

```text
promise n tt := treeMCSPPredicate n (threshold n) tt
```

That is, the truth table `tt` is promised to have a tree circuit of size at most
`threshold n`.

### 3.4 Relation

The relation is:

```text
relation n tt w := encoding.verifies n tt w
```

For a codec-shaped encoding, this means `w` decodes to a circuit `c` such that:

- the decode succeeds;
- `Circuit.size c ≤ threshold n`;
- `c` computes the truth table `tt`.

### 3.5 Circuit class

For this contract expansion to reach `VerifiedNPDAGLowerBoundSource`, the target
should specialize `C` to a class aligned with frozen `PpolyDAG`, not an arbitrary
restricted circuit class.  If `C` is left arbitrary, a `PpolyDAG` decider for the
constructed language need not yield a solver in `C`.  That mismatch is the first
major D0 gap.

### 3.6 Size bound

The target has a schedule:

```text
sizeBound : Nat → Nat
```

For the prefix-self-reduction, `sizeBound n` must dominate roughly:

```text
poly(inputEncodingLength(n)) × poly(witnessBits n)
```

because each witness bit circuit may include a copy of the prefix-language DAG
decider plus prior-bit circuitry.  No exact schedule is currently fixed.

### 3.7 Encoding

The current repository has an abstract `TreeMCSPSearchWitnessEncoding threshold`
and a more concrete `TreeCircuitWitnessCodec threshold`.  D0 recommends using the
codec-shaped path for any future Round 1 because it makes witness decoding,
size-checking, and truth-table correctness explicit.  However, the bit
serialization and polynomial verifier budget are still not instantiated.

### 3.8 Threshold schedule

No threshold schedule is selected in this report.  A future attempt must choose
one and prove:

- `witnessBits n` is polynomially bounded in the eventual NP-language input
  length;
- verification of `encoding.verifies n tt w` is polynomial-time;
- the extraction size blowup fits the chosen `sizeBound`.

## 4. Constructed language `L`

### 4.1 Intended language

The most plausible language is a prefix-extension language for the search
relation:

```text
L_prefix_target = {
  encode(n, x, i, p) :
    target.problem.promise n x ∧
    ∃ w : BitVec (target.problem.witnessBits n),
      prefix(w, i) = p ∧
      target.problem.relation n x w
}
```

Here:

- `x` is the search instance;
- `i` is a prefix length or next-bit index;
- `p` is a proposed prefix for the witness;
- membership says that `p` can be extended to a full valid witness.

This language is better than the direct graph language
`{(x,w) : relation x w}` because a decider for prefix extendability supports the
standard bit-by-bit search self-reduction.

### 4.2 Input format

A future formal input should be a single bitstring encoding:

```text
⟨n, x, i, p, padding/control bits⟩
```

with length normalized so that all fields can be decoded in polynomial time.
For the tree-MCSP target:

- `x` has `tableLen n` bits;
- `i ≤ witnessBits n`;
- `p` has `i` bits, or is stored in a fixed `witnessBits n`-bit area plus an
  index `i` saying which prefix is active.

A fixed-width prefix area is preferable because it avoids a variable-length
language family whose length conventions obscure the polynomial budget.

### 4.3 Length convention

D0 recommends a normalized length:

```text
N(n) = poly(tableLen n + witnessBits n + log n)
```

and a parser that rejects malformed encodings.  The parser must be part of the
NP verifier, not an implicit promise.

### 4.4 Membership condition

For a well-formed encoding `y = encode(n, x, i, p)`, membership is:

```text
target.problem.promise n x ∧
∃ w, prefix(w, i) = p ∧ target.problem.relation n x w
```

Malformed inputs should be nonmembers, or should follow a fixed harmless
convention.  They must not carry hidden hardness.

### 4.5 Witness/certificate format

The NP certificate is the full witness:

```text
w : BitVec (target.problem.witnessBits n)
```

plus, if needed, auxiliary decoding certificates for the codec.  For the
codec-shaped tree-MCSP relation, `w` itself should decode to a tree circuit; no
extra hard certificate should be required.

### 4.6 Dependencies of `L`

`L_prefix_target` depends on:

- the chosen target;
- the target's encoding and threshold schedule;
- a fixed parser/length convention.

It must **not** depend on:

- a solver;
- a diagonal choice against all DAGs;
- an oracle;
- nonuniform advice;
- a promise that already encodes `¬ PpolyDAG L`.

## 5. NP verification

### 5.1 Witness format

Given input `y`, the verifier parses `y` as `⟨n, x, i, p⟩` and receives a full
candidate witness:

```text
w : BitVec (target.problem.witnessBits n)
```

### 5.2 Verifier

The verifier checks:

1. `y` is well formed;
2. `i ≤ target.problem.witnessBits n`;
3. `prefix(w, i) = p`;
4. `target.problem.promise n x` if this is efficiently decidable, or otherwise
   folds the promise into the relation check for promised search targets;
5. `target.problem.relation n x w`.

For tree-MCSP via `TreeCircuitWitnessCodec`, this becomes:

1. decode `w` to a circuit `c`;
2. check `Circuit.size c ≤ threshold n`;
3. check `c` computes truth table `x` by evaluating `c` on every assignment of
   length `n` and comparing with the `tableLen n` bits.

Because the input already contains a full truth table of length `2^n`, the
truth-table correctness check is polynomial in the input length `tableLen n` as
long as circuit evaluation and decoding are polynomial in the witness length.

### 5.3 Polynomial witness length

A future proof must show:

```text
witnessBits n ≤ poly(N(n))
```

where `N(n)` is the encoded input length of `⟨n, x, i, p⟩`.  This is plausible
for tree-circuit encodings if `threshold n` and the circuit serialization size
are polynomial in `tableLen n`, but it is not currently fixed by a concrete
codec instantiation.

### 5.4 Polynomial verification time

For the tree-MCSP codec path, verification is polynomial in the truth-table
input length if:

- decoding runs in polynomial time;
- the encoded circuit has size bounded by a polynomial in `tableLen n`;
- evaluating the circuit on all `2^n = tableLen n` assignments is polynomial in
  `tableLen n` times circuit size.

This is a credible NP-verifier plan, but it is still a plan rather than a
repository theorem.

### 5.5 Relation to tree-MCSP witness encoding

`TreeMCSPSearchWitnessEncoding` gives soundness and completeness as propositions
but not yet a time-bounded verifier.  `TreeCircuitWitnessCodec` is the better
starting point because it exposes decode/encode and a concrete circuit witness,
but it still needs a bit-level serialization and runtime analysis before it can
support `L ∈ NP` in the frozen pnp3 sense.

## 6. Contrapositive extraction

This is the core of the proposed expansion.

### 6.1 Hypothetical input

Assume:

```text
PpolyDAG L_prefix_target
```

Informally, for each encoded input length `N`, there is a polynomial-size DAG
circuit `D_N` deciding membership in `L_prefix_target`.

### 6.2 Desired output

Build:

```text
BoundedSearchSolver target.problem target.circuitClass target.sizeBound
```

For each original search length `n` and witness bit index `j`, the solver needs
a circuit:

```text
B_{n,j} : target.circuitClass.Family (target.problem.instanceBits n)
```

such that, on a promised instance `x`, the output vector
`(B_{n,0}(x), ..., B_{n,witnessBits n-1}(x))` is a valid witness.

### 6.3 Bit-by-bit self-reduction sketch

Define prefix circuits recursively.  For a promised `x`, let the already-built
prefix be `p_j(x) = b_0(x) ... b_{j-1}(x)`.  Define the next bit by querying the
prefix-extension decider:

```text
b_j(x) = 1  iff  D_{N(n,j+1)}(encode(n, x, j+1, p_j(x) ++ 1)) = 1
```

If the `1` branch is extendable, choose `1`; otherwise choose `0`.

Correctness follows by induction using `totalOnPromise`:

- Base: the empty prefix is extendable because promised instances have some
  valid witness.
- Step: if the current prefix is extendable, at least one of the two one-bit
  extensions is extendable.  The rule chooses `1` if possible, otherwise `0`;
  hence the new prefix remains extendable.
- End: after `witnessBits n` steps, the full prefix is a complete valid witness,
  so `target.problem.relation n x output(x)` holds.

### 6.4 How the DAG decider is used

The DAG decider for `L_prefix_target` is used as an oracle subcircuit inside each
output-bit circuit.  It tests whether a candidate next prefix has an extension to
a full witness.

This use is nonuniform: for each `n` and each relevant encoded length, the
corresponding DAG decider circuit is selected nonuniformly from the `PpolyDAG L`
witness.

### 6.5 Building output circuits

To make `B_{n,j}` a circuit over the original instance bits `x`, the construction
must hardwire:

- the length field `n`;
- the index `j+1`;
- parser-control and padding bits;
- the candidate bit `1`;
- the previously constructed prefix circuits `B_{n,0}, ..., B_{n,j-1}`;
- the DAG decider `D_{N(n,j+1)}`.

Then it composes these into the input wires of the decider for
`L_prefix_target`.

### 6.6 Uniformity/nonuniformity

The extraction is nonuniform, matching `PpolyDAG` and `BoundedSearchSolver`.
No uniform algorithm is required to generate the circuits, but the proof must
show the required circuits exist at every length.

### 6.7 Size blowup

A naive recurrence is:

```text
S_0(n) = O(size(D) + encoder_overhead)
S_{j+1}(n) ≤ O(size(D) + encoder_overhead + Σ_{k≤j} S_k(n))
```

If implemented by literal recursive substitution, this can blow up by a factor
roughly linear or worse in `witnessBits n`.  A DAG-sharing construction may keep
this polynomial, but that requires explicit closure under shared subcircuits and
composition.

The target's `sizeBound n` must be chosen large enough to dominate this blowup.
If `sizeBound` is intended to be a weak regime such as near-linear size, the
extraction may fail.  This is the second major D0 gap.

### 6.8 Why solver correctness follows

Assuming exact decider correctness for `L_prefix_target`, the recursive prefix
invariant implies the final output is an extendable full-length prefix.  A
full-length prefix can only be extended by itself, so it is a valid witness.
Therefore the output circuits solve the search problem on every promised input.

### 6.9 Where `target.noBoundedSolver` is contradicted

If the extraction successfully builds a solver satisfying the target's
`sizeBound`, then:

```text
Nonempty (BoundedSearchSolver target.problem target.circuitClass target.sizeBound)
```

contradicts:

```text
target.noBoundedSolver :=
  ¬ Nonempty (BoundedSearchSolver target.problem target.circuitClass target.sizeBound)
```

Thus `PpolyDAG L_prefix_target` is impossible, yielding `¬ PpolyDAG L`.

### 6.10 D0 extraction status

**Partially specified, not GREEN-light complete.**

The logical search-to-decision skeleton is clear, but the repository currently
lacks the concrete pnp3/pnp4 DAG-class alignment and closure/size theorems needed
to certify that the extracted circuits are exactly a bounded solver for the
selected target.

## 7. Why this is not just `VerifiedNPDAGLowerBoundSource` in disguise

The proposal is not simply to assume:

```text
VerifiedNPDAGLowerBoundSource
```

or:

```text
target.noBoundedSolver → VerifiedNPDAGLowerBoundSource
```

Instead, it attempts to construct the fields of `VerifiedNPDAGLowerBoundSource`
from lower-level data:

- `L` is the prefix-extension language;
- `inNP` is the verifier for prefix extendability using a full witness;
- `notInPpolyDAG` is obtained by the decider-to-bounded-solver extraction.

However, this remains only non-wrapper if the new hypotheses are operational
closure, encoding, and verifier facts.  If a future Round 1 replaces
`Hextract` by a field saying "every `PpolyDAG L` gives a contradiction" without
building the solver, or by a field returning `VerifiedNPDAGLowerBoundSource`, it
would become exactly the same wrapper failure as `fp3b8`.

## 8. Non-circularity audit

| Possible hidden assumption | D0 status |
| --- | --- |
| `¬ PpolyDAG L` | Must not be assumed.  It should be proved from extraction.  Current sketch does not assume it. |
| no small DAG witness | Risk.  If the selected target says "no bounded PpolyDAG solver" and the extraction merely restates this without constructing the solver, it becomes circular. |
| `NP_not_subset_PpolyDAG` | Not assumed in the sketch.  It is the final consequence after constructing `L`. |
| `ResearchGapWitness` | Not used.  Forbidden. |
| `VerifiedNPDAGLowerBoundSource` | Not used as a hypothesis.  It is the target package to be constructed. |
| `SearchMCSPMagnificationContract` | Not used.  The expansion is supposed to replace it. |
| `target.noBoundedSolver → VerifiedNPDAGLowerBoundSource` | Forbidden as a field.  A future report must not introduce this as `Hmag`, `Hextract`, or similar. |
| Refuted support-bounds route | Not part of the prefix-extension sketch; see NOGO cross-check. |

The largest circularity risk is that `Hextract` could be stated too abstractly.
It must be a concrete theorem that takes a decider family and returns explicit
output-bit circuits with size and correctness proofs.

## 9. Natural Proofs audit

### 9.1 Constructivity

The prefix-extension language is decidable in NP and, if the relation verifier is
polynomial-time, membership has a constructive verifier.  If the proof of
`¬ PpolyDAG L` proceeds by showing that every small DAG fails a property that can
be checked efficiently on truth tables, it risks being constructive in the
Razborov--Rudich sense.

### 9.2 Largeness

The current prefix-search sketch does not define a large property of Boolean
functions.  It defines a language tied to one search relation and uses a
search-to-decision extraction.  That is better than the previous support-filter
routes.

However, no formal largeness negation is provided.  If future work recasts the
argument as "many functions satisfy an easy-to-check hardness predicate," the
natural-proofs risk becomes severe.

### 9.3 Usefulness

The intended conclusion is useful against `PpolyDAG`: no polynomial-size DAG
family decides `L`.  This is exactly the usefulness side of the natural-proofs
triad.

### 9.4 D0 audit result

**Risk / INCONCLUSIVE.**

The proposed route is not obviously a large constructive property, but it also
has no `NaturalProofBypassWitness` or precise explanation blocking the triad.
Future work must keep the proof as a search-to-decision extraction, not as a
support-cardinality, syntactic, or truth-table-large property.

## 10. Relativization audit

The proof skeleton appears highly relativizing at D0:

- define a prefix-extension language;
- use a decider for it as an oracle/subcircuit;
- self-reduce search to decision;
- derive contradiction with a no-solver assumption.

No explicit non-relativizing ingredient has been identified.  If the same
argument relativizes to oracle versions of the target, then it cannot by itself
explain an unconditional NP-vs-P/poly DAG lower bound beyond the strength already
contained in the no-solver premise.

**D0 result:** INCONCLUSIVE barrier risk.  A future Round 1 would need an
oracle-parameterized statement and either a bypass witness or a precise reason
why the implication is only a nonuniform search/decision transformation rather
than a relativizing proof of a final endpoint from weak assumptions.

## 11. Algebrization audit

The sketch uses no algebraic extension, low-degree polynomial representation, or
arithmetization.  That avoids introducing an algebrizing method, but it also
means there is no explicit non-algebrizing step.

**D0 result:** INCONCLUSIVE barrier risk.  The current route is combinatorial and
nonuniform, but a future proof must still explain why any black-box/algebraic
oracle version does not turn the implication into a barred algebrizing argument.

## 12. NOGO cross-check

| Entry | Status | Reason |
| --- | --- | --- |
| `NOGO-000001` | addressed | The sketch does not use `OverbroadUniformProvenance` or reconstruct the old fixed-params support-bounds route. |
| `NOGO-000002` | addressed | The route does not rely on a support-function range condition vulnerable to alternating or multi-slice hardwiring. |
| `NOGO-000003` | addressed | The route does not classify witnesses by support cardinality, so log-width truth-table hardwiring is not used as positive evidence. |
| `NOGO-000004` | addressed | The prefix-AND log-width support-cardinality counterexample is not a filter input to this proposal. |
| `NOGO-000005` | addressed | The route is not restricted to excluding prefix-AND while admitting arbitrary truth-table payloads; it avoids that filter family entirely. |
| `NOGO-000006` | addressed | Arbitrary all-essential log-width truth-table payloads do not help the prefix-extension extraction unless they already produce a decider-to-solver construction. |
| `NOGO-000007` | addressed | The proposed theorem is not support-cardinality-only.  Any future assumption depending only on support cardinality would re-trigger this NOGO. |
| `NOGO-000008` | addressed | The proposal is not a syntactic gate-count / OR-NOT-presence filter, so tautological-seed rewriting is not currently relevant. |
| `NOGO-000009` | addressed | The proposal does not use normalize-then-filter machinery.  A future syntactic normalizer patch is forbidden as evidence for this route. |

Overall NOGO status: the prefix-extension proposal avoids the known FP-N
support/syntax-filter failures, but this does not prove the contract expansion.
It only says the currently identified NOGO entries are not the main D0 blocker.

## 13. Verdict and recommended next action

### 13.1 Verdict

**INCONCLUSIVE**

### 13.2 Main reason

The best non-wrapper route is a prefix-extension search-to-decision reduction,
but D0 cannot certify the core contrapositive extraction against the existing
interfaces because the concrete `PpolyDAG` circuit-class alignment, closure under
composition, size blowup, witness encoding, and barrier bypass audits are still
missing.

### 13.3 Recommended next action before any Round 1

Do **not** authorize full Round 1 source-theorem work yet.  Authorize a narrow
D0.1 markdown/design slot, or at most interface-mapping documentation, with the
following exact deliverables:

1. **DAG class alignment memo.**  Specify whether a pnp4 `CircuitFamilyClass` can
   represent frozen pnp3 `PpolyDAG` without changing trust roots.
2. **Prefix language specification.**  Fix the encoding of `⟨n, x, i, p⟩`, the
   length convention, malformed-input behavior, and verifier budget.
3. **Extraction size ledger.**  Give a recurrence for output-bit circuit sizes
   and state the required `sizeBound` schedule.
4. **Closure requirements.**  List exact DAG operations needed: constants,
   projections, fixed-bit hardwiring, parser/encoder wiring, composition, and
   shared-subcircuit accounting.
5. **Barrier mini-audit.**  Oracle-parameterize the theorem and state whether the
   proof is merely relativizing/algebrizing; separately explain why it is not a
   large constructive useful property.

Only after those items are precise should a later operator decide whether a
limited Round 1 formalization is justified.  In that later round, the first
formalized object should be the prefix language and NP verifier; the final
`VerifiedNPDAGLowerBoundSource` package must remain unavailable until the
actual decider-to-solver extraction is proved.
