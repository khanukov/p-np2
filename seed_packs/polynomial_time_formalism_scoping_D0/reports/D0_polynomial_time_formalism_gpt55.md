# D0 polynomial-time formalism scoping — gpt55

**Slot:** D0 — polynomial-time formalism scoping  
**Handle:** gpt55  
**Task type:** markdown-only scoping report  
**Scope classification:** infrastructure. This report does not reduce `SearchMCSPWeakLowerBound` or `VerifiedNPDAGLowerBoundSource`, and it does not claim lower-bound or final-route progress.

## 1. Executive verdict

**Verdict:** `GREEN-light_formalism_investment`

A small pnp4-side polynomial-time verifier formalism is justified. The required mathematics is standard: convert a length-indexed verifier specification with polynomial certificate length, polynomial runtime, and semantic correctness into the existing canonical pnp3 `ComplexityInterfaces.NP L`, which is definitionally `NP_TM L`. The work is not a new lower-bound route and should not be called P-vs-NP mainline progress. It is an infrastructure bridge needed before any honest theorem of the form `PrefixExtensionLanguage ∈ NP` can be attempted.

The verdict is green only for the formalism investment, not for R1-C. The retrospective is correct that R1-C remains blocked by the separate self-reduction / PpolyDAG-compatible search-to-decision issue.

## 2. What formalism is needed

The minimum missing interface is a pnp4-side **runtime-faithful NP verifier specification** whose fields are strong enough to construct the pnp3 verifier TM required by `Pnp3.ComplexityInterfaces.NP L`.

The local R1-B2a facts currently have names such as:

- `parser_polynomial_time_in_M`;
- `decode_polynomial_time_in_M`;
- `relation_polynomial_time_in_M`;
- `witnessBits_poly_in_M`.

These names are useful as a checklist, but the first three are still bare `Prop` obligations. To bridge them to `Pnp3.ComplexityInterfaces.NP L`, the repo needs an interface that records more than the assertion that an operation is polynomial time. It must record, or be able to construct, the actual verifier machine and its semantic correctness proof.

Minimum required ingredients:

1. **Language alignment.** A length-indexed Boolean language `L : Pnp3.ComplexityInterfaces.Language`.
2. **Certificate length schedule.** A function `certLen : Nat → Nat`, together with a proof that `certLen n` is bounded by `n^k + k` or can be padded to the existing pnp3 `certificateLength n k` convention.
3. **Verifier implementation object.** Either a pnp3 internal `TM` directly, or a small verified program representation that has a proved compiler to such a `TM`.
4. **Polynomial runtime bound.** A proof that the verifier implementation runs in time polynomial in the total encoded input length `n + certificateLength n k`, matching the quantification in `NP_TM`.
5. **Correctness / accepts equivalence.** A proof that, for every input string `x`, `L n x = true` iff there exists a certificate accepted by the verifier on the concatenation of `x` and the certificate.
6. **Padding / certificate coercion discipline.** If the local witness length is `certLen n` but `NP_TM` wants exactly `certificateLength n k`, the formalism needs a standard pad-and-ignore convention, with proofs that padding preserves verifier semantics and the runtime bound.

Without these fields, local obligations like `parser_polynomial_time_in_M` and `relation_polynomial_time_in_M` cannot honestly discharge `Pnp3.ComplexityInterfaces.NP L`; they remain promises rather than machine-level witnesses.

## 3. Existing pnp3 `NP_TM` analysis

The canonical pnp3 target is `Pnp3.ComplexityInterfaces.NP L`, and `NP` is currently an abbreviation for `NP_TM`. The current `NP_TM` shape requires:

1. **TM verifier.** There must exist a concrete `Internal.PsubsetPpoly.TM` verifier `M`.
2. **Runtime exponent.** There must exist a natural number `c` such that `M.runTime` is bounded by `(totalLength)^c + c` at the relevant total input lengths.
3. **Certificate exponent.** There must exist a natural number `k`, and certificates have the canonical length `certificateLength n k = n^k + k`.
4. **Concatenated input convention.** The verifier reads the input and certificate as one bitstring built by `concatBitstring x w`.
5. **Accepts equivalence.** For every length `n` and input `x`, membership in `L` must be equivalent to existence of a certificate `w` of canonical length accepted by `M`.

The pnp4 local runtime records do **not** connect to this target directly today. R1-B2a records arithmetic facts such as `tableLen_le_M`, `threshold_poly_in_M`, and `witnessBits_poly_in_M`, plus named runtime obligations. It also records real parser-side semantic obligations such as malformed-input rejection and length-convention matching. But it does not provide:

- a concrete pnp3 internal `TM` verifier;
- a compiler from parser/codec/evaluator components to a `TM`;
- a pnp3 `certificateLength n k` padding bridge;
- a theorem converting the local runtime budget into the `NP_TM` accepts equivalence.

Therefore R1-B2a is a correct runtime-budget staging layer, not an NP-membership proof.

## 4. Existing reusable infrastructure

I found reusable pieces, but not a complete local-runtime-to-`NP_TM` bridge.

### 4.1 TM encoding utilities

Reusable: **yes**.

The internal pnp3 `PsubsetPpolyInternal` layer has a concrete deterministic single-tape `TM` structure with finite control, a transition function, and a `runTime` schedule. It also defines configurations, execution for `runTime n` steps, and the Boolean `accepts` predicate. This is exactly the machine object required by `NP_TM`.

Limitation: these utilities are low-level. They are suitable as a target, but they do not by themselves provide a convenient pnp4 algorithm-cost DSL for parsers, decoders, prefix checks, and tree-circuit evaluation.

### 4.2 Straight-line simulation

Reusable: **yes, but directionally different**.

The pnp3 simulation infrastructure can compile or reason about TM runtime into circuit / straight-line artifacts. This is valuable for the existing `P ⊆ P/poly` direction and for validating machine semantics. However, the D0 need is the reverse engineering layer: given a high-level parser/codec/relation algorithm, produce or certify a verifier TM. Existing straight-line simulation is not a general high-level-program-to-TM compiler.

### 4.3 Parser and circuit evaluators

Reusable: **partial**.

The contract-expansion modules define:

- `PrefixInput`, `PrefixParser`, `parsePrefixInput`, `PrefixExtensionLanguage`, and the key parse/witness correctness theorems;
- `TreeCircuitWitnessCodec`, including encode/decode components;
- decidability progress for the codec relation;
- runtime-aware records for parser, codec, relation, truth-table lookup, and ambient-length arithmetic.

This is good semantic scaffolding. The missing part is that the parser and codec are still abstract functions, and their runtime fields are not tied to a machine or executable program representation.

### 4.4 Polynomial runtime lemmas

Reusable: **partial**.

There are polynomial-bound conventions in both pnp3 and pnp4:

- pnp3 `polyTimeDecider` and `NP_TM` use bounds of the shape `n^c + c`;
- R1-B2a defines `PolynomiallyBoundedInAmbient M f` and uses it for thresholds and witness lengths.

These can be reconciled. The missing work is a small library of padding, monotonicity, composition, and ambient-length conversion lemmas sufficient to move from `M(n)`-based statements to total encoded length statements. This is manageable, but it is real Lean work.

### 4.5 Computability or executable-function bridge

Reusable: **not enough today**.

I did not find a pnp4-level interface saying that a parser, decoder, prefix checker, or relation checker is implemented by a verified executable function with a polynomial-cost proof and a compiler to the pnp3 `TM` model. This is the central missing layer. Adding more `Prop` fields with names ending in `_polynomial_time` would not solve it.

## 5. Minimal pnp4 polynomial-time layer proposal

I recommend one small interface family, intentionally narrower than a general verified programming language.

### 5.1 Core interface: verifier spec for NP languages

Define, in a future authorised Lean pack, a pnp4-side record conceptually equivalent to:

- language `L`;
- local certificate length `certLen`;
- proof that `certLen` is polynomially bounded;
- verifier implementation target, preferably the existing pnp3 internal `TM` at first;
- optional adapter from local certificates to the canonical pnp3 certificate length;
- polynomial runtime proof for the verifier on concatenated input/certificate strings;
- correctness theorem: `L n x = true` iff some local/canonical certificate makes the verifier accept.

This can be called something like `PolyTimeVerifierSpec`, but the exact name is less important than the payload discipline: it must contain an implementation object and correctness/runtime proofs, not just a checklist of opaque `Prop` fields.

### 5.2 Avoid overbuilding

Do **not** start with a general monadic cost semantics for all pnp4 code unless the small direct-TM approach fails. For this seed-pack’s target, the smallest useful bridge is enough:

1. direct verifier TM package;
2. padding bridge from local witness length to pnp3 `certificateLength`;
3. theorem from the package to `Pnp3.ComplexityInterfaces.NP L`;
4. one later instantiation attempt for `PrefixExtensionLanguage`.

### 5.3 Optional second layer only if needed

If writing the verifier TM directly becomes too painful, introduce a tiny verified-program layer with only the primitives needed for prefix-extension verification:

- fixed-length bitvector reads and comparisons;
- bounded loops over input length / truth-table length;
- parser combinators for the selected serialization;
- decode of tree-circuit witnesses;
- tree-circuit evaluation;
- existential certificate handling via the NP certificate string.

This second layer should still compile to `Internal.PsubsetPpoly.TM`; otherwise it will not bridge to `NP_TM`.

## 6. Bridge theorem needed

The bridge theorem shape should be:

```text
PolyTimeVerifierSpec L → Pnp3.ComplexityInterfaces.NP L
```

or, expanded against the current abbreviation:

```text
PolyTimeVerifierSpec L → Pnp3.ComplexityInterfaces.NP_TM L
```

What must be proved:

1. Extract the verifier implementation as an `Internal.PsubsetPpoly.TM`.
2. Produce the `c` runtime exponent required by `NP_TM`.
3. Produce the `k` certificate-length exponent required by `NP_TM`.
4. Show that the verifier’s `runTime` at length `n + certificateLength n k` is at most `(n + certificateLength n k)^c + c`.
5. Show the accepts equivalence for every `n` and `x`, using the spec’s correctness theorem plus any padding/ignore-certificate-tail lemmas.

Trust-root assessment:

- This theorem should **not** require trust-root edits.
- It can live outside `pnp3/Complexity/Interfaces.lean`, because it proves a theorem reducing to the existing frozen `NP` / `NP_TM` definition rather than changing that definition.
- If imports are awkward, place the theorem in a pnp4 bridge module that imports `Complexity.Interfaces` and the new pnp4 formalism module.
- Do not alter `ComplexityInterfaces.NP`, `NP_TM`, `certificateLength`, `concatBitstring`, or the pnp3 internal TM semantics.

## 7. Cost estimate

**Estimate:** 2–4 weeks.

Expected module count:

1. **1 module** for polynomial-bound and padding utilities: certificate-length domination, local-to-canonical padding, and ambient-length conversion lemmas.
2. **1 module** for the `PolyTimeVerifierSpec` interface and the bridge theorem to `NP_TM`.
3. **1 module** for a direct proof-of-concept verifier, likely a toy language, to check that the interface is not vacuous.
4. **1–2 modules** for a future `PrefixExtensionLanguage` instantiation, if separately authorised.

Dependencies:

- `Complexity.Interfaces` for `NP_TM`, `certificateLength`, `concatBitstring`, and `NP`;
- `Complexity.PsubsetPpolyInternal.TuringEncoding` for `TM` and `accepts`;
- possibly `Complexity.PsubsetPpolyInternal.TuringToolkit` if direct verifier construction needs reusable machine programs;
- contract-expansion modules only at the instantiation stage, not for the generic bridge theorem.

Risk:

- **Medium engineering risk.** Direct TM construction may be verbose.
- **Low mathematical risk** for the abstract bridge theorem.
- **Medium integration risk** because pnp4 bitvector conventions, pnp3 `Bitstring`, and `PrefixBitVec` may need adapters.
- **High scope-creep risk** if the team tries to solve all verified-programming needs rather than the narrow NP-verifier bridge.

## 8. Applicability to `PrefixExtensionLanguage`

**Answer:** `yes_plausible`

A minimal formalism should be enough to prove `PrefixExtensionLanguage ∈ NP` from an R1-B2a-style runtime budget, but only after the remaining runtime fields are turned into implementation-backed facts.

What is already aligned:

- `PrefixExtensionLanguage` is a Boolean length-indexed language.
- A certificate can be the full target witness extending the prefix.
- `witnessBits_poly_in_M` is the right certificate-size statement measured against ambient length.
- `tableLen_le_M` justifies why truth-table enumeration can be polynomial in the encoded input length.
- Parser-side malformed rejection and length-convention facts are already stated as real quantified obligations.

What remains missing before the formalism can instantiate it:

- concrete or implementation-backed parser runtime;
- implementation-backed decoder runtime;
- implementation-backed tree-circuit evaluation runtime;
- implementation-backed truth-table lookup / relation-check runtime;
- bitvector and padding adapters to pnp3 `Bitstring` and `certificateLength`;
- an actual verifier implementation object, either direct `TM` or compiled from a tiny verified program representation.

So the answer is not that R1-B2a already proves NP membership. It does not. The answer is that the proposed formalism is the right bridge, and R1-B2a’s fields identify the correct local obligations to feed into it once they become real implementation-backed facts.

## 9. R1-C impact

Even if the polynomial-time formalism lands, **R1-C does not become automatically plausible**.

Formalism landing would make the following plausible:

```text
PrefixExtensionLanguage ∈ NP
```

It would not prove the missing R1-C theorem:

```text
PpolyDAG L → BoundedSearchSolver target
```

with the required PpolyDAG-compatible size budget. The retrospective identifies that self-reduction as the separate mathematical blocker. Therefore:

- R1-C should remain closed after this D0 report.
- A future NP-membership theorem would improve architectural hygiene and remove one staged obligation.
- It would not by itself make the contract-expansion route a mainline lower-bound route.
- Opening R1-C immediately after the formalism would risk recreating the wrapper-around-contract failure mode.

Honest R1-C impact: **the formalism removes an engineering blocker, not the mathematical blocker**.

## 10. Recommendation

**Recommendation:** `invest_in_formalism`

Recommended next authorised pack shape:

1. **Not R1-C.** Do not open a self-reduction or endpoint pack.
2. **Authorise a small pnp4 formalism pack** whose only Lean goal is the generic bridge:
   - define the minimal verifier-spec interface;
   - prove `PolyTimeVerifierSpec L → Pnp3.ComplexityInterfaces.NP L`;
   - include a toy instantiation to prevent the interface from being merely decorative.
3. **Keep `PrefixExtensionLanguage_in_NP` for a later pack.** It should depend on the formalism pack and on concrete implementation-backed parser/codec/runtime proofs.
4. **No trust-root edits.** The pack must import and target the existing pnp3 `NP_TM` definition.
5. **No source theorem, no endpoint, no ResearchGapWitness.** This is infrastructure only.

If operator appetite for 2–4 weeks of infrastructure work is low, the fallback is `do_one_more_scoping_pass` focused specifically on direct-TM construction feasibility for prefix parsers and tree-circuit verification. I do not recommend stopping contract expansion solely because of the NP-formalism gap; I recommend stopping R1-cadence and investing only if the operator values a clean, reusable NP bridge independent of R1-C.

## Final structured output

```text
Slot: polynomial-time formalism D0
Handle: gpt55
Branch: main
Outcome: REPORT_LANDED
report path: seed_packs/polynomial_time_formalism_scoping_D0/reports/D0_polynomial_time_formalism_gpt55.md
executive verdict: GREEN-light_formalism_investment
minimum formalism: implementation-backed PolyTimeVerifierSpec-style NP verifier interface with certificate length, polynomial runtime, verifier implementation, correctness, and padding bridge to pnp3 NP_TM
bridge theorem shape: PolyTimeVerifierSpec L → Pnp3.ComplexityInterfaces.NP L
cost estimate: 2–4 weeks, roughly 3–5 Lean modules, medium engineering risk
PrefixExtensionLanguage applicability: yes_plausible
R1-C impact: formalism removes an NP-membership engineering blocker but does not make R1-C plausible because the PpolyDAG-compatible self-reduction remains missing
recommendation: invest_in_formalism
Scope violations: none
```
