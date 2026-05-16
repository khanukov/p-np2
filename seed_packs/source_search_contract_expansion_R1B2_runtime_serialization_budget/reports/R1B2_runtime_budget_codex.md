# R1-B2 runtime budget report — codex

## Outcome

`REPORT_LANDED`

This report is R1-B2 only.  It does not attempt R1-C, extraction, a
`PpolyDAG → BoundedSearchSolver` construction, a `VerifiedNPDAGLowerBoundSource`,
a `ResearchGapWitness`, a source theorem, an endpoint, or any P-vs-NP claim.

## 1. What was attempted

I audited the current prefix-extension language surface and the concrete
Tree-MCSP search target to determine whether the R1-B / R1-B1
`PrefixExtensionLanguage` can honestly be promoted to an NP language under a
concrete parser / codec / runtime budget.

The audit focused on the load-bearing distinction requested by R1-B2:

- polynomial time in the target parameter `n`; versus
- polynomial time in the ambient encoded input length `M(n)`.

The key result is:

- `TreeCircuitWitnessCodec.verifiesDecidable` is not a polynomial-time theorem.
- The truth-table agreement part is exponential in `n`, because it quantifies
  over all `BitVec n` assignments.
- For tree-MCSP, that same enumeration is plausibly polynomial in the ambient
  length `M(n)` if the length convention includes the truth table payload
  `problem.instanceBits n = tableLen n = 2^n` and if circuit evaluation / codec
  decoding are themselves polynomially budgeted in the relevant encoded sizes.
- A full NP theorem is not currently honest without additional local parser,
  codec-size, decode-runtime, and adapter facts.  The largest global blocker is
  the missing bridge from the staged R1-B budget predicates to the existing
  `NP_TM` verifier interface.

## 2. Exact signatures inspected

### Prefix-extension language layer

The R1-B language layer defines parsed inputs as:

```lean
structure PrefixInput
    (problem : SearchMCSPCompressionProblem)
    (m : Nat) where
  tag : Nat
  n : Nat
  x : PrefixBitVec (problem.instanceBits n)
  i : Nat
  prefixLength_le : i ≤ problem.witnessBits n
  p : PrefixBitVec i
  padBits : Nat
  pad : PrefixBitVec padBits
```

The parser boundary is:

```lean
structure PrefixParser
    (problem : SearchMCSPCompressionProblem) where
  tag : Nat
  M : Nat → Nat
  parse : ∀ {m : Nat}, PrefixBitVec m → Option (PrefixInput problem m)
```

The semantic language predicate is:

```lean
def PrefixExtendableInput
    {problem : SearchMCSPCompressionProblem}
    {m : Nat}
    (input : PrefixInput problem m) : Prop :=
  ∃ w : PrefixBitVec (problem.witnessBits input.n),
    input.prefixAgrees w ∧ problem.relation input.n input.x w
```

The R1-B budget surface is only propositional at present:

```lean
structure PrefixExtensionNPVerifierBudget
    {problem : SearchMCSPCompressionProblem}
    (parser : PrefixParser problem) : Type where
  parser_polynomial_time : Prop
  witness_length_polynomial : Prop
  prefix_agreement_polynomial_time : Prop
  relation_decidable : Prop
  relation_polynomial_time : Prop
  codec_serialization_available : Prop
  codec_decode_available : Prop
  codec_witness_length_bound : Prop
  truth_table_verification_runtime : Prop
```

### R1-B1 parser / codec layer

The staged tree-MCSP parser constructor is:

```lean
def treeMCSPPrefixParser
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold)
    (tag : Nat)
    (M : Nat → Nat)
    (parse : ∀ {m : Nat},
      PrefixBitVec m →
        Option (PrefixInput (treeMCSPSearchProblem threshold encoding) m)) :
    PrefixParser (treeMCSPSearchProblem threshold encoding)
```

The parser-obligation record is:

```lean
structure TreeMCSPPrefixParserObligations
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold) where
  tag : Nat
  M : Nat → Nat
  parse : ∀ {m : Nat},
    PrefixBitVec m →
      Option (PrefixInput (treeMCSPSearchProblem threshold encoding) m)
  parser_polynomial_time : Prop
  malformed_inputs_rejected_by_parse : Prop
  length_convention_matches_M : Prop
```

The R1-B1 relation-decidability result for codec targets is:

```lean
def TreeCircuitWitnessCodec.verifiesDecidable
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (tt : TruthTable n)
    (w : PrefixBitVec (codec.witnessBits n)) :
    Decidable (codec.verifies n tt w)
```

The R1-B1 partial progress record is:

```lean
structure TreeMCSPPrefixCoreBudgetProgress
    {threshold : Nat → Nat}
    {encoding : TreeMCSPSearchWitnessEncoding threshold}
    (parser : PrefixParser (treeMCSPSearchProblem threshold encoding)) where
  parser_polynomial_time : Prop
  relation_decidable :
    ∀ n : Nat,
      ∀ x : PrefixBitVec ((treeMCSPSearchProblem threshold encoding).instanceBits n),
      ∀ w : PrefixBitVec ((treeMCSPSearchProblem threshold encoding).witnessBits n),
        Decidable ((treeMCSPSearchProblem threshold encoding).relation n x w)
  relation_polynomial_time : Prop
  witness_length_polynomial : Prop
  remaining_runtime_or_codec_blockers : Prop
```

### Concrete tree-MCSP target layer

The generic search target has separate instance and witness lengths:

```lean
structure SearchMCSPCompressionProblem where
  instanceBits : Nat → Nat
  witnessBits : Nat → Nat
  promise :
    ∀ n : Nat,
      AlgorithmsToLowerBounds.BitVec (instanceBits n) →
        Prop
  relation :
    ∀ n : Nat,
      AlgorithmsToLowerBounds.BitVec (instanceBits n) →
        AlgorithmsToLowerBounds.BitVec (witnessBits n) →
          Prop
  totalOnPromise :
    ∀ n : Nat, ∀ x : AlgorithmsToLowerBounds.BitVec (instanceBits n),
      promise n x →
        ∃ w : AlgorithmsToLowerBounds.BitVec (witnessBits n),
          relation n x w
```

For tree-MCSP, the concrete instance length is the truth-table length:

```lean
def treeMCSPSearchProblem
    (threshold : Nat → Nat)
    (encoding : TreeMCSPSearchWitnessEncoding threshold) :
    SearchMCSPCompressionProblem where
  instanceBits := fun n => Pnp3.Models.Partial.tableLen n
  witnessBits := encoding.witnessBits
  promise := fun n tt => treeMCSPPredicate n (threshold n) tt
  relation := encoding.verifies
  totalOnPromise := encoding.complete
```

The table length definition is:

```lean
def tableLen (n : Nat) : Nat := Nat.pow 2 n
```

The truth-table agreement predicate is:

```lean
def ComputesTruthTable
    (C : CircuitFamilyClass)
    {n : Nat}
    (c : C.Family n)
    (tt : TruthTable n) : Prop :=
  ∀ x : BitVec n, C.eval c x = truthTableFunction tt x
```

The codec verifier relation is:

```lean
def TreeCircuitWitnessCodec.verifies
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (tt : TruthTable n)
    (w : AlgorithmsToLowerBounds.BitVec (codec.witnessBits n)) : Prop :=
  ∃ c : Pnp3.Models.Circuit n,
    codec.decode n w = some c ∧
      Pnp3.Models.Circuit.size c ≤ threshold n ∧
        ComputesTruthTable treeCircuitClass c tt
```

### Existing NP formalism

The canonical repository NP interface is TM-based:

```lean
def NP_TM (L : Language) : Prop :=
  ∃ (M : Internal.PsubsetPpoly.TM.{0}) (c k : Nat),
    (∀ n,
      M.runTime (n + certificateLength n k) ≤
        (n + certificateLength n k) ^ c + c) ∧
    (∀ n (x : Bitstring n),
      L n x = true ↔
        ∃ w : Bitstring (certificateLength n k),
          Internal.PsubsetPpoly.TM.accepts
              (M := M)
              (n := n + certificateLength n k)
              (concatBitstring x w) = true)
```

and `NP` is currently:

```lean
abbrev NP (L : Language) : Prop := NP_TM L
```

## 3. Ambient length convention status

### Recommended R1-B2 convention

For a prefix input at target parameter `n`, use a single ambient length schedule
of the following shape:

```text
M(n) = overhead(n)
     + problem.instanceBits n
     + enc_i_bits(n)
     + problem.witnessBits n
     + padding_budget(n)
```

For the tree-MCSP target this specializes to:

```text
M_tree(n) = overhead(n)
          + tableLen n
          + enc_i_bits(n)
          + codec.witnessBits n
          + padding_budget(n)
```

where:

```text
tableLen n = 2^n
```

This convention deliberately allocates room for a full `problem.witnessBits n`
prefix payload, even when the active prefix length `i` is smaller.  The inactive
suffix is represented by padding / unused prefix slots; this keeps a
single-length-per-target convention and makes `M(n)` monotone enough for later
runtime statements.

### Load-bearing arithmetic status

Under the convention above:

```text
tableLen n ≤ M_tree(n)
```

is immediate if all overhead terms are nonnegative natural-number summands.  In
Lean this should be a small `Nat.le_add_right` / associativity lemma once
`M_tree` is fixed.

This is the arithmetic fact R1-B2 needs: enumerating all assignments costs
`2^n = tableLen n` iterations, so the iteration count is linear in the truth
-table segment and therefore polynomial in `M_tree(n)`.

### Important caveat

The statement is **not** polynomial in `n`.  It is polynomial in the ambient
encoded input length.  Any later theorem named `relation_polynomial_time` must
say which length parameter it uses.  For tree-MCSP, an `n`-polynomial statement
for truth-table verification would be false for the obvious verifier.

## 4. Parser serialization status

No concrete bit-level parser exists yet for:

```lean
parseTreeMCSPPrefix
treeMCSPPrefixParser_concrete
```

The current parser boundary is honest: `PrefixParser.parse` is an explicit
field, and `TreeMCSPPrefixParserObligations` exposes
`parser_polynomial_time`, `malformed_inputs_rejected_by_parse`, and
`length_convention_matches_M` as obligations rather than silently proving them.

A concrete parser should fix all of the following before any NP theorem:

1. `tag` layout: a fixed domain/version separator for R1-B2 inputs.
2. `n` layout: either fixed-width inside `M(n)`, self-delimiting, or recovered
   from ambient length by an injective length schedule.
3. `x` layout: exactly `tableLen n` bits for tree-MCSP.
4. `i` layout: enough bits to encode values up to `codec.witnessBits n`.
5. `p` layout: either exactly `i` active bits plus padding, or a fixed
   `codec.witnessBits n` block with only the first `i` active.
6. `pad` layout: canonical zeros are preferable; otherwise parser must prove
   noncanonical padding is rejected or semantically ignored.
7. malformed-input behavior: parse failure must imply nonmembership via
   `PrefixExtensionLanguage_rejects_malformed`.

Precise missing parser theorem list:

```text
parseTreeMCSPPrefix_length:
  parse accepts only strings whose ambient length matches M(n), or rejects.

parseTreeMCSPPrefix_fields:
  successful parse returns the tag, n, x, i, p, pad encoded in y.

parseTreeMCSPPrefix_i_bound:
  successful parse proves i ≤ problem.witnessBits n.

parseTreeMCSPPrefix_padding:
  padding is canonical/rejected or ignored in a specified way.

parseTreeMCSPPrefix_malformed_rejected:
  malformed encodings parse to none.

treeMCSPPrefixParser_concrete_polynomial_time_in_M:
  parsing runs in time polynomial in the ambient input length M(n).
```

## 5. Relation runtime status

For codec-induced tree-MCSP relation verification, the operational verifier has
three conceptual phases:

1. `codec.decode n w`.
2. Check `Pnp3.Models.Circuit.size c ≤ threshold n`.
3. Check truth-table agreement:

   ```lean
   ∀ x : BitVec n, treeCircuitClass.eval c x = truthTableFunction tt x
   ```

R1-B1 proved decidability by using finite enumeration of `BitVec n`, via
`Fintype.decidableForallFintype`.  This tells us the relation is decidable, not
that any concrete verifier is polynomial time.

### Runtime in `n`

The truth-table agreement check enumerates all assignments `x : BitVec n`.
There are exactly `2^n = tableLen n` such assignments.  Therefore the obvious
truth-table verifier is exponential in `n`.

An R1-B2 theorem claiming this verifier is polynomial in `n` would be dishonest
unless it uses a different oracle/model or a compressed instance representation.
That is not the current tree-MCSP target: instances are truth tables.

### Runtime in `M(n)`

Under the ambient convention in Section 3, `tableLen n ≤ M_tree(n)`.  Therefore
the number of assignments checked is at most linear in `M_tree(n)`.

The full relation verifier is polynomial in `M_tree(n)` provided the following
local conditions are supplied:

```text
codec.decode_runtime_polynomial_in_M:
  decode n w runs in poly(M_tree(n)).

codec.size_check_runtime_polynomial_in_M:
  computing/checking Circuit.size c ≤ threshold n is poly(M_tree(n)).

codec.eval_runtime_polynomial_in_M:
  evaluating the decoded circuit c on one assignment is poly(M_tree(n)).

codec.decoded_size_bound:
  any accepted decoded circuit has encoded/syntactic size poly(M_tree(n)),
  or at least each evaluation of an accepted decoded circuit is poly(M_tree(n)).

truth_table_lookup_runtime:
  reading tt at the index for x is poly(M_tree(n)), preferably O(n) or O(1)
  under the selected bit-vector/list representation model.
```

With these assumptions, total agreement-check time is:

```text
O(tableLen n × per_assignment_cost(M_tree(n)))
```

which is polynomial in `M_tree(n)` because `tableLen n ≤ M_tree(n)`.

### Current status

The current Lean code does not expose runtime contracts for `codec.decode`,
`Circuit.size`, `Circuit.eval`, or truth-table lookup.  Thus R1-B2 can honestly
record the relation as **plausibly polynomial in `M(n)` but not discharged**.

## 6. Witness-length status

The R1-B / R1-B1 generic interfaces keep witness length abstract:

```lean
TreeMCSPSearchWitnessEncoding.witnessBits : Nat → Nat
TreeCircuitWitnessCodec.witnessBits : Nat → Nat
```

Therefore `witness_length_polynomial` cannot be discharged for all codecs.
A malicious or simply oversized codec could choose, for example,
`witnessBits n = 2^(2^n)`.

For a concrete tree-circuit codec, the desired condition is:

```text
∃ c, ∀ n, codec.witnessBits n ≤ M_tree(n)^c + c
```

or, if `M_tree(n)` itself contains `codec.witnessBits n`, a more careful NP
certificate condition should be stated against the ambient language length `m`:

```text
∃ c, ∀ m y, verifier certificate length for y ≤ m^c + c.
```

The second formulation is closer to the existing `NP_TM` interface, where the
certificate length is a fixed polynomial in the language input length.  It also
avoids circularity when `M(n)` includes `codec.witnessBits n` as part of the
encoded prefix input.

Current blocker:

```text
codec_witness_length_bound is codec-specific and currently absent.
```

This is a local obstruction for any concrete codec, but a global obstruction for
a generic theorem over arbitrary `TreeCircuitWitnessCodec` values.

## 7. Polynomial-time formalism status

The repository has a real global NP formalism: `NP` abbreviates `NP_TM`, a
Turing-machine verifier with certificate length `certificateLength n k` and
runtime polynomial in the concatenated input/certificate length.

However, the R1-B / R1-B1 budget fields are currently plain `Prop` fields, not
instances of a reusable parser/relation-verifier runtime predicate.  There is no
local adapter theorem of the form:

```text
concrete_parser_runtime
+ concrete_relation_runtime
+ concrete_witness_length
+ serialization_correctness
→ Pnp3.ComplexityInterfaces.NP (PrefixExtensionLanguage parser)
```

So the global formalism exists, but R1-B2 lacks the bridge from structured
parser/codec budgets to `NP_TM`.

Minimal local predicate recommended before an NP theorem:

```lean
structure TreeMCSPPrefixRuntimeBudget
    {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (parser : PrefixParser (treeMCSPSearchProblem threshold
      (TreeMCSPSearchWitnessEncoding.ofCodec codec))) : Type where
  ambientLength : Nat → Nat
  ambientLength_eq_parser_M : ∀ n, ambientLength n = parser.M n
  tableLen_le_ambientLength : ∀ n,
    Pnp3.Models.Partial.tableLen n ≤ ambientLength n
  parser_polynomial_time_in_ambient_length : Prop
  malformed_inputs_rejected_by_parse : Prop
  decode_polynomial_time_in_ambient_length : Prop
  circuit_eval_polynomial_time_in_ambient_length : Prop
  truth_table_verification_polynomial_time_in_ambient_length : Prop
  relation_polynomial_time_in_ambient_length : Prop
  witness_length_polynomial_in_language_input_length : Prop
```

This is intentionally not a fake budget: every runtime field remains a real
obligation.  Do not fill these fields with `True`.

## 8. Local vs global obstruction

### Local obstructions

- No fixed concrete serialization for `tag`, `n`, `x`, `i`, `p`, and `pad`.
- No concrete `parseTreeMCSPPrefix` or `treeMCSPPrefixParser_concrete`.
- No concrete codec with a proved witness-bit bound.
- No runtime contracts for `codec.decode`, `Circuit.size`, `Circuit.eval`, or
  truth-table lookup.
- No arithmetic lemma yet tying a fixed `M_tree(n)` to `tableLen n`, because
  `M_tree` has not been fixed.

### Global obstruction

- R1-B budget fields are not connected to the repository's actual `NP_TM`
  interface by an adapter theorem.
- The current `TreeCircuitWitnessCodec.verifiesDecidable` proof is purely
  propositional/decidability-level and cannot itself supply a machine runtime.

## 9. What R1-C must know

R1-C must not assume an `n`-polynomial tree-MCSP verifier.  The safe fact for
R1-C is conditional:

```text
truth-table verification is polynomial in the ambient encoded input length M(n)
when M(n) includes tableLen n = 2^n, subject to concrete codec/parser runtime
bounds.
```

R1-C should also treat the following as prerequisites, not as consequences of
R1-C:

- concrete parser correctness and malformed-input rejection;
- concrete witness-length polynomial bound in language input length;
- relation-verifier runtime polynomial in ambient length;
- an adapter from these runtime budgets to `NP_TM`.

## 10. Recommended next move

Do not open R1-C yet.

Recommended R1-B2 follow-up:

1. Add a small Lean module only for noncontroversial arithmetic and budget-shape
   definitions, for example `TreeMCSPPrefixRuntimeBudget`, with no `True`
   runtime fillers.
2. Fix a concrete `M_tree(n)` convention with canonical padding and prove
   `tableLen n ≤ M_tree(n)`.
3. Choose or define a concrete tree-circuit witness codec and prove a real
   `codec.witnessBits` bound.
4. Write the parser theorem list from Section 4 as Lean statements or prove them
   if serialization is fixed.
5. Only after the above, build the adapter from R1-B2 runtime budgets to
   `Pnp3.ComplexityInterfaces.NP`.

## Final classification

- Ambient length status: `tableLen n ≤ M(n)` is the right target and is easy once
  `M(n)` is fixed; not yet formalized because no concrete `M(n)` exists.
- Parser status: blocked on concrete serialization.
- Relation runtime status: exponential in `n`; plausibly polynomial in `M(n)`
  under explicit decode/eval/lookup size assumptions; not discharged.
- Witness length status: blocked for abstract codecs; needs concrete codec bound
  or an assumption field.
- Polynomial-time formalism status: global `NP_TM` exists, but no local adapter
  from staged budget records to `NP_TM` exists.
- Budget fields discharged: relation decidability only, inherited from R1-B1;
  no polynomial-time fields discharged here.
- R1-C readiness: not ready.
