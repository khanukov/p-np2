# D0 report — polynomial-time formalism scoping

## 1. Executive verdict

**Verdict:** `GREEN-light_formalism_investment`

This is an infrastructure verdict, not mainline lower-bound progress.  The work would not reduce `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`; it would instead create the missing formal route from local parser/codec/runtime claims to the canonical pnp3 `ComplexityInterfaces.NP` / `NP_TM` interface.

The investment is justified because R1-B2/R1-B2a isolated a real architectural gap: current pnp4 contract-expansion records can name runtime obligations, but they cannot themselves construct the TM verifier required by pnp3 `NP`.  Continuing directly to R1-C would therefore risk treating staged `Prop` labels as if they were executable runtime proofs.

## 2. What formalism is needed

The minimum interface must connect local facts of the following kind:

- `parser_polynomial_time_in_M`;
- `decode_polynomial_time_in_M`;
- `relation_polynomial_time_in_M`;
- `witnessBits_poly_in_M`;
- parser correctness and malformed-input rejection;
- length-convention facts such as `m = M input.n` after successful parsing;

into a pnp3 theorem of the form:

```text
Pnp3.ComplexityInterfaces.NP L
```

The crucial missing object is not another checklist of propositions.  The needed interface must package an actual verifier model that is either already a pnp3 `Internal.PsubsetPpoly.TM` or has a proved compiler into that TM model.  At minimum it should carry:

1. a language `L : Pnp3.ComplexityInterfaces.Language`;
2. a certificate-length schedule and proof that it is polynomial in the ambient input length used by `NP_TM`;
3. a verifier algorithm over the concatenated input/certificate encoding, or a formally compiled TM verifier;
4. a polynomial runtime theorem for the verifier in the same length parameter used by `NP_TM`;
5. a correctness theorem giving both directions of membership versus existence of an accepting certificate.

For `PrefixExtensionLanguage`, the verifier must parse the ambient string, reject malformed inputs, read a full target witness as the certificate, check prefix agreement, decode/evaluate the codec relation, and accept exactly the prefix-extendable inputs.

## 3. Existing pnp3 `NP_TM` analysis

The current canonical pnp3 NP definition is TM-based.  It requires:

- **TM verifier:** an `Internal.PsubsetPpoly.TM`.
- **Certificate length:** pnp3 fixes certificate length to `certificateLength n k = n ^ k + k` for some global exponent `k`.
- **Runtime bound:** for some global exponent `c`, the verifier must satisfy a bound on `M.runTime (n + certificateLength n k)` of the form `(n + certificateLength n k) ^ c + c`.
- **Accepts equivalence:** for every input length `n` and string `x`, `L n x = true` iff there exists a certificate `w` of length `certificateLength n k` such that the TM accepts the concatenated string `concatBitstring x w`.

The current pnp4 local runtime records cannot connect directly to this definition.  Their runtime fields are named `Prop` obligations, not TMs, executable verifiers, or proofs that a verifier can be compiled into the pnp3 TM model.  The arithmetic fields, such as `witnessBits_poly_in_M`, are useful but insufficient: `NP_TM` needs a single verifier machine plus runtime and correctness proofs over the canonical concatenated encoding.

A second mismatch is certificate shape.  `PrefixExtensionLanguage` naturally wants certificates of length `problem.witnessBits input.n`, where `input.n` is recovered by parsing an ambient string of length `m`.  `NP_TM` instead exposes certificates of length `m ^ k + k` when the language input length is `m`.  A bridge must therefore specify padding/truncation or an embedding from the natural full-witness certificate into the pnp3 fixed polynomial certificate length.

## 4. Existing reusable infrastructure

### TM encoding utilities

The repository has a lightweight pnp3 TM model with finite state, binary tape, transition function, and a `runTime` field.  It also defines configurations, stepping, running, and acceptance.  `Complexity.Interfaces` supplies the NP-level concatenation helper for input/certificate strings.

This is sufficient as a target model, but it is not by itself a high-level verifier programming framework.

### Straight-line simulation

The pnp3 internal development contains straight-line circuit infrastructure and a TM-to-circuit simulation route.  That route is useful for `P ⊆ PpolyDAG`-style results and for circuitizing existing TMs.  It does not solve the present problem in the reverse direction: we need to build or compile a verifier algorithm into a pnp3 TM for `NP`, not compile a known TM into nonuniform circuits.

### Parser and circuit evaluators

The pnp4 contract-expansion modules provide semantic parser interfaces, prefix agreement, prefix extendability, malformed-input rejection, and a decidability reduction for the tree-MCSP relation induced by a codec.  These are useful semantic specifications.

However, `PrefixExtensionLanguage` is currently defined through a classical boolean wrapper around a semantic existential predicate.  That definition is fine as a language specification, but it must not be used as the verifier implementation.  The verifier must be an explicit algorithm/TM that checks the same condition.

### Polynomial runtime lemmas

R1-B2a adds honest arithmetic around the ambient length `M`, including the fact that the truth-table component is bounded by the ambient length and a reusable `PolynomiallyBoundedInAmbient` predicate.  These facts are necessary for measuring truth-table enumeration against the encoded input length rather than the internal parameter `n`.

They are not sufficient for NP membership because the actual parser, decoder, truth-table lookup, circuit evaluation, and relation verifier runtime fields remain staged propositions.

### Computability or executable function bridge

I found no reusable bridge that takes a high-level decidable predicate or executable Lean function, proves it polynomial-time, and emits an `Internal.PsubsetPpoly.TM` satisfying `NP_TM`.  The existing Turing toolkit is substantial, but the current contract-expansion records do not point to a generic high-level-to-TM compiler that can discharge `parser_polynomial_time_in_M`, `decode_polynomial_time_in_M`, and `relation_polynomial_time_in_M` as actual machine-cost theorems.

## 5. Minimal pnp4 polynomial-time layer proposal

The smallest plausible layer is a pnp4-side verifier-spec interface, not an edit to pnp3 `NP`.  In pseudocode shape:

```text
PolyTimeVerifierSpec(L):
  certLen(n): natural number
  certLen_poly: certLen(n) is bounded by n^k + k for some k
  verifier: concrete verifier artifact over input bits and certificate bits
  verifier_poly_time: verifier runs in time polynomial in input length plus certificate length
  verifier_correct: L(x) is true iff some certificate accepted by verifier
  compiles_to_pnp3_TM: verifier yields an Internal.PsubsetPpoly.TM with matching semantics and runtime
```

Two design constraints are important:

1. **Do not store runtime as bare `Prop` labels.**  Runtime fields should be tied to a verifier artifact and to a cost model that can be compiled to pnp3 `TM.runTime`.
2. **Do not redefine certificates.**  The bridge may allow natural certificate lengths internally, but the final theorem must pad or embed them into pnp3's `certificateLength n k` convention.

A viable split would be:

- one module for polynomial bounds and certificate padding;
- one module defining `PolyTimeVerifierSpec` and its correctness semantics;
- one module proving the bridge from the spec to pnp3 `NP_TM`;
- one later, separate module instantiating the spec for `PrefixExtensionLanguage` after concrete parser/codec runtime proofs exist.

If the project insists that the verifier artifact must be a fully explicit pnp3 TM from the start, then the interface becomes smaller but the PrefixExtension proof becomes much more laborious.  I recommend allowing a small verified-verifier layer with an explicit compiler theorem into pnp3 TMs.

## 6. Bridge theorem needed

The bridge theorem shape should be:

```text
PolyTimeVerifierSpec L -> Pnp3.ComplexityInterfaces.NP L
```

The theorem must prove:

1. existence of a pnp3 `Internal.PsubsetPpoly.TM` verifier;
2. a global certificate exponent `k` matching pnp3 `certificateLength n k`;
3. a global runtime exponent `c` for the combined input/certificate length;
4. equivalence between `L n x = true` and existence of an accepting certificate under `concatBitstring`.

This does not require trust-root edits.  It can live outside the pnp3 trust root, preferably in pnp4 or a non-trust-root bridge module importing `Complexity.Interfaces`.  The bridge consumes the frozen pnp3 semantics rather than changing them.

The proof will need careful certificate padding.  If the verifier spec has natural certificate length `certLen n`, and `certLen n ≤ certificateLength n k`, the pnp3 certificate can include the natural certificate followed by padding.  Correctness then requires showing that the compiled verifier ignores or validates the padding in a way that preserves the existential equivalence.

## 7. Cost estimate

**Estimate:** `2–4 weeks`

**Lean modules:** approximately 3–5 modules for the generic layer, plus later instantiation modules for concrete prefix-extension work.

Likely module split:

1. polynomial-bound and certificate-padding helpers;
2. verifier-spec interface and semantics;
3. compiler/bridge theorem to `ComplexityInterfaces.NP`;
4. optional adapters for pnp4 contract-expansion runtime budgets;
5. later PrefixExtensionLanguage instantiation once concrete algorithms are available.

**Dependencies:**

- `pnp3/Complexity/Interfaces.lean` for `Language`, `NP`, `NP_TM`, `certificateLength`, and `concatBitstring`;
- `pnp3/Complexity/PsubsetPpolyInternal/TuringEncoding.lean` and Turing toolkit modules for the target machine model;
- pnp4 contract-expansion modules for parser/codec semantics;
- R1-B2a ambient-length arithmetic from `PrefixExtensionLanguageRuntime.lean`.

**Risk:** medium-high.

The main risk is not mathematical asymptotics; the ambient-length convention appears to make truth-table enumeration polynomial in the encoded input length.  The risk is formal engineering: proving that a high-level verifier artifact compiles to the existing pnp3 TM model without introducing fake runtime fields or changing trust-root definitions.

A one-week version is plausible only as another scoping/design pass.  A real bridge theorem to `NP_TM` is more likely 2–4 weeks if the project accepts a narrow verifier language.  A fully general Lean function-to-TM compiler would be multi-month and is not recommended for this seed.

## 8. Applicability to `PrefixExtensionLanguage`

**Answer:** `no_missing_more`

The proposed formalism would be the right kind of layer, but the current R1-B2a runtime budget alone is not enough to prove:

```text
PrefixExtensionLanguage ∈ NP
```

The reason is that R1-B2a still stores parser, decode, truth-table lookup, circuit-evaluation, and relation runtime claims as named propositions.  A `PolyTimeVerifierSpec` bridge can consume actual verifier artifacts and runtime proofs; it cannot manufacture them from inert `Prop` fields.

What remains missing for `PrefixExtensionLanguage` after the generic formalism lands:

1. a concrete parser or verified parser artifact for the prefix serialization;
2. parser soundness, malformed-input rejection, and length-convention proofs;
3. a concrete codec decoder with polynomial runtime in ambient length;
4. a polynomial witness-size proof compatible with pnp3 certificate padding;
5. a polynomial relation verifier for prefix agreement, decode, size check, truth-table lookup/evaluation, and relation checking;
6. a final correctness proof matching `PrefixExtensionLanguage_accepts_iff`, but using the executable verifier rather than the classical language definition as an implementation.

So the formalism is necessary and useful, but current R1-B2a data must be strengthened before it can instantiate the formalism.

## 9. R1-C impact

Even if the formalism lands, R1-C does not immediately become plausible.

A successful formalism would remove one architectural blocker: it would explain what it means to prove `PrefixExtensionLanguage ∈ NP` from local runtime facts.  It would not by itself supply the concrete parser, codec, decoder runtime, certificate padding, or relation-verifier proofs.  R1-C should therefore remain blocked until:

1. the generic `PolyTimeVerifierSpec -> NP` bridge is proved;
2. the R1-B2a prefix-extension runtime budget is upgraded from staged `Prop` labels to concrete verifier artifacts/proofs;
3. the prefix-extension NP-membership theorem is actually obtained without trust-root edits or fake runtime assumptions.

If those land, R1-C can be reconsidered.  Until then, authorising R1-C would be premature.

## 10. Recommendation

**Recommendation:** `invest_in_formalism`

The next step should be a small, explicitly non-mainline infrastructure effort to design and prove the `PolyTimeVerifierSpec -> Pnp3.ComplexityInterfaces.NP` bridge.  Do not resume R1-cadence implementation work until that bridge exists or until a follow-up scoping pass concludes that the bridge is too large for this repository.

Recommended guardrails for the follow-up:

- keep all work outside pnp3 trust-root definitions;
- do not edit `ComplexityInterfaces.NP` or `NP_TM`;
- avoid `True` placeholders for runtime;
- do not expose any source theorem, `gap_from`, `ResearchGapWitness`, endpoint, or P-vs-NP claim;
- treat the work as infrastructure, not mainline lower-bound progress.
