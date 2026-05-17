# D0 polynomial-time formalism scoping — gpt55

## 1. Executive verdict

**Verdict:** `GREEN-light_formalism_investment`

This is an **infrastructure** recommendation, not mainline P-vs-NP progress.  It does not reduce `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`, and it must not be reported as a lower-bound advance.

The repo has enough ingredients to justify a small, focused investment in a pnp4 polynomial-time verifier layer, but it does **not** yet have enough machinery to turn the existing R1-B2a runtime records directly into `Pnp3.ComplexityInterfaces.NP L`.  The missing piece is not another local parser arithmetic lemma; it is a uniform bridge from audited local executable/runtime facts to the canonical pnp3 `NP_TM` witness.

## 2. What formalism is needed

The minimum useful formalism must connect local facts of the following shape:

- `parser_polynomial_time_in_M`
- `decode_polynomial_time_in_M`
- `relation_polynomial_time_in_M`
- `witnessBits_poly_in_M`

with the canonical target:

- `Pnp3.ComplexityInterfaces.NP L`

A merely propositional checklist is not enough.  The layer must identify an actual verifier computation and relate its runtime and semantics to pnp3's `NP_TM` interface.  At minimum, the formalism needs four components:

1. **Certificate sizing and padding.**  A local witness-length function may be `f m`, while pnp3 `NP_TM` uses certificates of exactly `certificateLength m k = m^k + k`.  The layer must prove `f m ≤ certificateLength m k` and specify that unused certificate bits are ignored or treated as padding.
2. **Executable verifier semantics.**  A verifier must be more than a `Prop`; it needs an object whose acceptance behavior can be related to bitstrings.  The local verifier should parse the input, read a bounded certificate, check prefix agreement, decode the witness circuit, and check the target relation.
3. **Polynomial runtime accounting.**  Local bounds in ambient length `M` must compose into a single polynomial bound in the actual language input length `m`.  For prefix inputs, this requires the parser length convention `m = M input.n` on successful parses and harmless rejection on malformed inputs.
4. **A bridge to pnp3 TM acceptance.**  Either the verifier object is already a pnp3 `Internal.PsubsetPpoly.TM`, or the layer includes a compiler/simulation theorem producing such a TM with a proved runtime and correctness theorem.

Therefore, the right minimal interface is not just `verifier_poly_time : Prop`; it is a TM-backed or compiler-backed verifier package whose fields are strong enough to construct the existential witness required by `NP_TM`.

## 3. Existing pnp3 `NP_TM` analysis

The canonical pnp3 definition is TM-faithful.  `Pnp3.ComplexityInterfaces.NP` is an abbreviation for `NP_TM`, and `NP_TM L` requires:

- **TM verifier:** an explicit `Internal.PsubsetPpoly.TM`.
- **Certificate length exponent:** a natural `k`, with certificates of length `certificateLength n k = n^k + k`.
- **Runtime exponent:** a natural `c`, with `M.runTime (n + certificateLength n k) ≤ (n + certificateLength n k)^c + c`.
- **Acceptance equivalence:** for every input length `n` and bitstring `x`, `L n x = true` iff there exists a certificate `w` of the fixed polynomial length such that the TM accepts `concatBitstring x w`.

The current pnp4 local runtime records do **not** connect to this directly.  R1-B2a records facts such as `decode_polynomial_time_in_M`, `parser_polynomial_time_in_M`, and `relation_polynomial_time_in_M` as named `Prop` obligations.  Those fields are useful as an audit checklist, but they do not provide:

- a pnp3 `TM`;
- a compilation path from parser/codec code to a pnp3 `TM`;
- a theorem translating each local runtime `Prop` into the `TM.runTime` inequality required by `NP_TM`;
- a certificate-padding theorem aligning local witness bits with `certificateLength`;
- an accepts-equivalence theorem for `PrefixExtensionLanguage`, especially because the language definition itself uses classical decidability around the semantic predicate.

So the answer is: **no, the existing pnp4 runtime records cannot connect to `NP_TM` directly.**  They can become inputs to a future bridge only after the repository defines what counts as an executable polynomial-time verifier and how such verifiers compile or package into pnp3 TMs.

## 4. Existing reusable infrastructure

The repository already has useful ingredients, but they are not yet a complete pnp4-to-pnp3 polynomial-time bridge.

### Reusable pieces found

- **TM encoding utilities.**  `pnp3/Complexity/PsubsetPpolyInternal/TuringEncoding.lean` defines the internal one-tape TM model used by `NP_TM`, including configurations, bounded `runTime`, `run`, and `accepts`.
- **Turing toolkit modules.**  The `pnp3/Complexity/PsubsetPpolyInternal/TuringToolkit/**` modules provide low-level construction material such as atomic programs, phased programs, row-consistency checks, copying, unary-at-offset routines, encodings, and gate wrappers.
- **Straight-line / circuit simulation infrastructure.**  `StraightLine.lean`, `StraightLineBuilder.lean`, `StraightLineSemantics.lean`, `TreeToStraight.lean`, and `Simulation.lean` provide structured circuit and simulation machinery useful for lower-level Boolean computation arguments.
- **Parser and prefix-language interfaces.**  `PrefixExtensionLanguage.lean` defines `PrefixInput`, `PrefixParser`, `parsePrefixInput`, `PrefixExtendable`, and `PrefixExtensionLanguage`; it also proves semantic lemmas for acceptance, malformed rejection, and parsed-witness acceptance.
- **Contract-expansion audit records.**  `PrefixExtensionLanguageNP.lean` records parser obligations, relation decidability for the tree-MCSP target, and a core budget-progress structure.  `PrefixExtensionLanguageRuntime.lean` adds ambient-length arithmetic and the R1-B2a runtime-budget surface.
- **Circuit evaluators and DAG adapter.**  `C_DAG_Adapter.lean` shows that pnp4 circuit-family views can be aligned with frozen pnp3 DAG semantics without redefining the trust root.

### Missing bridge pieces

- **No general executable-function-to-TM compiler.**  I did not find a reusable theorem saying that an arbitrary parser/codec/evaluator implemented as a Lean function, or as a pnp4 verifier record, compiles to `Internal.PsubsetPpoly.TM` with a polynomial `runTime` bound.
- **No pnp4 polynomial-time verifier class tied to `NP_TM`.**  Existing runtime fields are `Prop` obligations, not a compositional cost semantics.
- **No direct parser-runtime proof object.**  `PrefixParser.parse` is an arbitrary function field.  The repo can state parser obligations, but there is not yet a standard representation of parser code with a machine-cost proof.
- **No complete certificate-padding convention for prefix witnesses.**  R1-B2a proves polynomial boundedness of witness bits in ambient length, but pnp3 `NP_TM` requires fixed certificates of length `m^k + k` for the language input length `m`.
- **No accepts-equivalence bridge for the classical language wrapper.**  `PrefixExtensionLanguage` is noncomputable and classical; an NP proof must verify that a concrete executable verifier accepts exactly the same Boolean language.

## 5. Minimal pnp4 polynomial-time layer proposal

The smallest sensible layer should be **TM-backed first**, not a broad executable compiler.  A compiler from a rich verifier DSL to pnp3 TMs would be valuable, but it is larger than D0 should recommend as the first step.

A minimal interface can be described as follows, in theorem-shape prose rather than implementation code:

```text
PolyTimeVerifierSpec(L) contains:
  - certLen : Nat → Nat
  - certLen exponent k and proof certLen(m) ≤ certificateLength(m,k)
  - verifierTM : Pnp3.Internal.PsubsetPpoly.TM
  - runtime exponent c proving verifierTM.runTime(m + certificateLength(m,k))
      ≤ (m + certificateLength(m,k))^c + c
  - a certificate padding/trim convention from local certLen(m) into
      certificateLength(m,k)
  - verifier correctness:
      L m x = true iff some local certificate accepted by verifierTM,
      equivalently iff some padded pnp3 certificate accepted by verifierTM
```

For pnp4 usability, a companion record may package local verifier obligations before the TM is constructed:

```text
LocalVerifierPlan(L) contains:
  - local certificate length;
  - parser/decode/relation/prefix-agreement checks;
  - local polynomial-time obligations;
  - semantic correctness against L.
```

But `LocalVerifierPlan L` should **not** imply `ComplexityInterfaces.NP L` by itself.  Only a TM-backed `PolyTimeVerifierSpec L`, or a proved compiler from `LocalVerifierPlan L` to such a spec, should imply NP membership.

This two-level design avoids a fake-proof trap:

- local records can remain audit checklists;
- the bridge theorem only fires after a real TM witness and runtime/correctness proofs exist;
- no trust-root definition has to be changed.

## 6. Bridge theorem needed

The bridge theorem shape should be:

```text
PolyTimeVerifierSpec L → Pnp3.ComplexityInterfaces.NP L
```

What must be proved:

1. Extract the verifier TM from the spec.
2. Extract exponents `c` and `k`.
3. Use the runtime field to satisfy the `NP_TM` runtime inequality.
4. Convert the local certificate-existence statement into existence of a pnp3 certificate of length `certificateLength n k`, using padding and trimming lemmas.
5. Use the verifier-correctness field to prove the `L n x = true ↔ exists certificate accepted` equivalence.

This theorem should **not** require trust-root edits.  It can live outside pnp3 core semantics, preferably under a pnp4 infrastructure namespace or a contract-expansion support namespace.  It imports pnp3 definitions read-only and constructs an inhabitant of the existing `ComplexityInterfaces.NP L` abbreviation.  That is compatible with the research constitution because it proves into the frozen target interface instead of redefining it.

The bridge is small if `PolyTimeVerifierSpec` already stores a pnp3 TM and the exact runtime/correctness fields.  It becomes much larger if it also tries to compile arbitrary parser/codec/evaluator descriptions into TMs.

## 7. Cost estimate

**Estimate for the minimal TM-backed formalism:** `2–4 weeks`.

Expected size:

- **2–3 Lean modules** for the initial infrastructure:
  1. a polynomial certificate/padding and verifier-spec module;
  2. a bridge theorem module from the spec to `ComplexityInterfaces.NP`;
  3. optional smoke/audit tests for the public theorem surface.
- **No pnp3 trust-root edits.**
- **No endpoint or source theorem.**

Dependencies:

- `pnp3/Complexity/Interfaces.lean` for `Language`, `certificateLength`, `concatBitstring`, and `NP` / `NP_TM`.
- `pnp3/Complexity/PsubsetPpolyInternal/TuringEncoding.lean` for `TM`, `runTime`, and `accepts`.
- Existing pnp4 contract-expansion modules only as clients, not as dependencies of the abstract bridge unless useful.

Risk:

- **Medium** for the TM-backed bridge itself: the theorem is close to repackaging `NP_TM`, but padding and universe/import details may still take care.
- **High** if the task expands into a general compiler from Lean functions or parser records to TMs.
- **High** if someone tries to make existing `Prop` runtime obligations imply TM runtime without a machine model.

**Estimate for proving `PrefixExtensionLanguage ∈ NP` from real parser/codec code:** likely `multi-month` unless the concrete parser and codec are deliberately tiny and TM-backed from the start.  The current R1-B2a budget is a good checklist, but it is not yet executable evidence.

## 8. Applicability to `PrefixExtensionLanguage`

**Answer:** `no_missing_more`

A minimal TM-backed `PolyTimeVerifierSpec` would be the right target, but the current R1-B2a runtime budget alone is not enough to prove:

```text
PrefixExtensionLanguage ∈ NP
```

The missing items are concrete and important:

1. A concrete verifier TM, or a small executable verifier language plus a compiler to pnp3 TMs.
2. A concrete serialization/parser implementation with a runtime proof in the chosen machine model.
3. A codec decode implementation with runtime proof.
4. A proof that prefix agreement is checked in polynomial time in ambient length.
5. A proof that the relation check, including truth-table lookup and circuit evaluation, is polynomial in ambient length.
6. Certificate padding from `problem.witnessBits input.n` into `certificateLength m k` where `m` is the actual language input length.
7. A semantic equivalence proof against the existing `PrefixExtensionLanguage` Boolean wrapper, including malformed-input rejection.

The ambient-length arithmetic in R1-B2a is still valuable: because `tableLen n ≤ M n`, enumerating `2^n` truth-table positions can plausibly be polynomial in the ambient input length.  However, this arithmetic has to be composed with an actual verifier cost model before it yields `NP` membership.

## 9. R1-C impact

Even if the minimal formalism lands, **R1-C does not immediately become plausible**.

The formalism would make R1-C better scoped: workers would know the exact target for an NP-membership proof and the exact evidence needed.  But R1-C should remain blocked until at least these additional ingredients exist:

- a concrete parser/serialization, not just an abstract `parse` field;
- a concrete codec decode path with size and runtime proofs;
- a verifier implementation or TM-backed package;
- padding/length lemmas aligning local witnesses with pnp3 certificates;
- an accepts-equivalence proof for `PrefixExtensionLanguage`.

So the honest R1-C impact is:

- **Formalism alone:** useful infrastructure, not enough for R1-C.
- **Formalism + executable parser/codec/runtime proofs:** R1-C becomes a well-defined implementation task.
- **Current repository state:** R1-C should remain forbidden/blocked.

## 10. Recommendation

**Recommendation:** `invest_in_formalism`

Recommended next move:

1. Authorise a small infrastructure seed pack for a TM-backed `PolyTimeVerifierSpec` and the bridge theorem to `ComplexityInterfaces.NP`.
2. Explicitly forbid the bridge theorem from accepting opaque runtime `Prop` fields as sufficient evidence.
3. Keep R1-C blocked until a later scoping pass identifies a concrete parser/codec/verifier implementation path.
4. Treat all of this as infrastructure, not as P-vs-NP mainline progress.

Do **not** restart R1-cadence dispatches.  The next useful step is to build the formalism boundary that makes future runtime work auditable.
