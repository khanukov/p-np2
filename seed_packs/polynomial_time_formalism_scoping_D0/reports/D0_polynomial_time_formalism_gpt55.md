# D0 polynomial-time formalism scoping — gpt55

**Slot:** D0 — polynomial-time formalism scoping  
**Handle:** gpt55  
**Branch reviewed:** `main`  
**Task type:** markdown-only scoping report  
**Scope classification:** infrastructure scoping, not P-vs-NP mainline progress

This report is a scoping decision only.  It does not add Lean code, does not
modify pnp3 trust roots, does not introduce a source theorem, does not define a
`gap_from` bridge, does not construct a `ResearchGapWitness`, does not add an
endpoint, does not authorize R1-C, and does not claim P≠NP.

## 1. Executive verdict

**Verdict:** `GREEN-light_formalism_investment`

The repository should invest in a small, honest polynomial-time verifier layer,
but only if the layer is explicitly TM-backed or compiler-backed.  A layer that
merely renames staged fields such as `parser_polynomial_time_in_M` or
`relation_polynomial_time_in_M` as additional opaque `Prop` assumptions would be
scientifically useless and should be rejected.

The green light is narrow:

- build a minimal bridge whose endpoint is exactly the existing pnp3 canonical
  `Pnp3.ComplexityInterfaces.NP L`, i.e. `NP_TM L`;
- keep all definitions outside the frozen pnp3 trust root;
- require executable verifier data and a real runtime proof, or an explicit
  construction of an existing pnp3 TM verifier;
- treat `PrefixExtensionLanguage ∈ NP` as a later theorem, not as a consequence
  of this D0 report and not as a consequence of the current R1-B2a records alone.

## 2. What formalism is needed

The minimum formalism needed is a bridge from local pnp4 verifier components to
the canonical pnp3 language class:

```text
Pnp3.ComplexityInterfaces.NP L
```

For the contract-expansion path, the local facts that need to become usable are
currently shaped like:

- `parser_polynomial_time_in_M`;
- `decode_polynomial_time_in_M`;
- `relation_polynomial_time_in_M`;
- `witnessBits_poly_in_M`.

The formalism must not treat the first three runtime fields as arbitrary
propositions.  It must connect them to a verifier algorithm that consumes the
concatenated input/certificate string used by pnp3 `NP_TM` and has a polynomial
`runTime` bound.  The minimal interface therefore needs four roles:

1. **Language target.** A pnp3 `Language` value `L`.
2. **Certificate schedule.** A certificate-length function, plus a proof that it
   is bounded by the pnp3 `certificateLength n k = n^k + k` convention, or a
   direct choice of such a `k`.
3. **Verifier implementation.** Either an actual `Pnp3.Internal.PsubsetPpoly.TM`
   or a small executable verifier representation with a compiler theorem into
   that TM model.
4. **Correctness and cost.** Proofs that the verifier accepts exactly the
   language instances with some certificate, and that its runtime is polynomial
   in the combined input/certificate length.

A useful layer should make the following implication routine:

```text
honest executable verifier spec for L
  ⟹ Pnp3.ComplexityInterfaces.NP L
```

It should not attempt to prove pnp4 lower bounds or touch `PpolyDAG` semantics.
It is only an NP-membership infrastructure bridge.

## 3. Existing pnp3 `NP_TM` analysis

The canonical target is already present.  In `pnp3/Complexity/Interfaces.lean`,
`NP` is an abbreviation for `NP_TM`.  The `NP_TM` definition requires:

1. **TM verifier.** An `Internal.PsubsetPpoly.TM` verifier `M`.
2. **Runtime exponent.** A polynomial exponent `c` such that the verifier runtime
   on the combined input/certificate length is bounded by
   `(n + certificateLength n k)^c + c`.
3. **Certificate exponent.** A certificate exponent `k`, using the fixed pnp3
   schedule `certificateLength n k = n^k + k`.
4. **Acceptance equivalence.** For every length `n` and input bitstring `x`,
   `L n x = true` iff there exists a certificate bitstring of length
   `certificateLength n k` such that `M` accepts the concatenation of `x` and the
   certificate.

The pnp4 local runtime records do **not** connect to this directly.  R1-B2a
exposes arithmetic bounds such as `tableLen_le_M`, `threshold_poly_in_M`, and
`witnessBits_poly_in_M`, and it names runtime obligations such as
`decode_polynomial_time_in_M`, `parser_polynomial_time_in_M`, and
`relation_polynomial_time_in_M`.  However, those runtime fields are still bare
`Prop` fields; they do not identify a verifier TM, a compiled executable
program, or a theorem relating local parser/codec routines to `TM.accepts`.

So the direct answer is:

```text
Can current pnp4 local runtime records connect to NP_TM directly?  no.
```

They are the right checklist, but not yet an NP proof.

## 4. Existing reusable infrastructure

The repository already has pieces that can support the bridge, but the pieces do
not yet form a high-level pnp4 polynomial-time layer.

### 4.1 TM encoding utilities

The pnp3 internal stack exposes the `Pnp3.Internal.PsubsetPpoly.TM` model used by
`NP_TM`.  It also includes `TuringEncoding` and `TuringToolkit` modules with
compiled program utilities, explicit `runTime` fields, and examples/proofs about
`TM.accepts`.

Useful examples include:

- `TuringToolkit.Foundation`, which packages phased programs into the internal
  TM model and preserves the declared runtime as `runTime`;
- `TuringToolkit.AtomicPrograms`, `BinaryCounter`, `CopyAtOffset`,
  `CombineAtOffset`, and related files, which demonstrate low-level machine
  construction patterns;
- `TuringEncoding`, which is already part of the internal polynomial-time
  machine infrastructure.

This means the repository does not need a new trust-root TM semantics.  It needs
a pnp4-facing adapter layer that targets the existing TM semantics.

### 4.2 Straight-line simulation

`pnp3/Complexity/PsubsetPpolyInternal/Simulation.lean` contains substantial
straight-line and circuit-simulation infrastructure.  The direction is primarily
useful for `P ⊆ P/poly` style compilation: given a TM and runtime, build circuit
objects and prove semantic/runtimes properties.  This is valuable evidence that
the internal TM model is serious, but it is not by itself a high-level compiler
from pnp4 parser/codec functions to a verifier TM.

So straight-line simulation is reusable background infrastructure, not the
missing `PrefixExtensionLanguage ∈ NP` bridge.

### 4.3 Parser and circuit evaluators

Contract-expansion modules provide semantic parser/language definitions and
relation-level codec facts:

- `PrefixExtensionLanguage.lean` defines `PrefixInput`, `PrefixParser`,
  `parsePrefixInput`, `PrefixExtendable`, and the language itself;
- it proves malformed-input rejection and parsed-input acceptance theorems;
- `PrefixExtensionLanguageNP.lean` proves decidability for codec-induced
  relation checks, but explicitly separates decidability from polynomial time;
- `PrefixExtensionLanguageRuntime.lean` adds ambient-length arithmetic and
  runtime-aware records, but keeps runtime fields staged.

These are good semantic targets for a future verifier.  They are not executable
TM implementations yet.

### 4.4 Polynomial runtime lemmas

The repository has many polynomial-bound statements, including pnp3 `runTime`
bounds and pnp4 ambient-length bounds.  What is missing is not arithmetic in
isolation, but compositional runtime accounting that says:

```text
parse + decode + prefix agreement + relation check
  runs in polynomial time in input length plus certificate length
```

and then compiles or identifies that composite verifier with a pnp3 TM.

### 4.5 Computability or executable-function bridge

I did not find a reusable high-level bridge of the following form:

```text
executable Boolean verifier + polynomial cost certificate
  ⟹ Internal.PsubsetPpoly.TM verifier with matching acceptance semantics
```

There are low-level TM construction utilities, but not a general pnp4-facing
computability layer that can consume parser/codec/runtime facts and emit an
`NP_TM` witness.  This is the exact gap D0 should surface.

## 5. Minimal pnp4 polynomial-time layer proposal

The smallest useful layer should be an **honest verifier-spec adapter**, not a
new complexity class and not a replacement for pnp3 `NP_TM`.

A design-level shape is:

```text
PolyTimeVerifierSpec(L)
  certificate length schedule, polynomially bounded by pnp3 certificateLength;
  verifier implementation, either:
    (A) a concrete Internal.PsubsetPpoly.TM, or
    (B) a tiny executable verifier language plus a compiler to that TM;
  polynomial runtime theorem for the implementation;
  acceptance equivalence theorem for L.
```

The safest first version is TM-backed:

```text
PolyTimeVerifierSpec(L)
  k : Nat
  M : Internal.PsubsetPpoly.TM
  runtime_poly : for all n, M.runTime(n + certificateLength n k)
                 is polynomially bounded as NP_TM requires
  verifier_correct : for all n and x,
                 L n x = true iff some certificate makes M accept concat(x,w)
```

This is intentionally close to `NP_TM`.  Its value is not mathematical novelty;
its value is giving pnp4 modules a stable place to assemble verifier packages
without editing the pnp3 trust root.  A second phase may add a higher-level
executable verifier DSL only after the TM-backed adapter lands.

Important constraints:

- Do not define a new alternative `NP`.
- Do not hide runtime in arbitrary `Prop` fields.
- Do not add a theorem saying every decidable relation is polynomial time.
- Do not use noncomputable classical language definitions as executable
  verifiers.
- Make the conversion to pnp3 `NP` a theorem, not a definitional rewrite of the
  trust root.

## 6. Bridge theorem needed

The theorem shape should be:

```text
PolyTimeVerifierSpec L → Pnp3.ComplexityInterfaces.NP L
```

For a TM-backed first version, this theorem is mostly record repackaging into
`NP_TM`.  It must prove or provide:

1. an internal pnp3 TM verifier `M`;
2. certificate exponent `k` matching the pnp3 `certificateLength` convention;
3. runtime exponent `c` with the exact `runTime` inequality required by
   `NP_TM`;
4. the acceptance equivalence between language membership and existence of a
   certificate accepted by `M` on `concatBitstring x w`.

This bridge does **not** require trust-root edits.  It can live outside pnp3
trust roots, for example in a new pnp4 infrastructure module or a non-trust-root
pnp3 adapter module, because it only proves a theorem whose conclusion is the
frozen `ComplexityInterfaces.NP L`.

The bridge also should not import lower-bound endpoints, `ResearchGapWitness`,
source-theorem machinery, or `PpolyDAG` target definitions except as ordinary
read-only dependencies if a later application needs them.

## 7. Cost estimate

**Estimate:** `2–4 weeks` for a narrow TM-backed verifier-spec adapter;
`multi-month` if the project also wants a general executable verifier DSL with
compiler and compositional cost algebra.

### Narrow adapter cost

- **Lean modules:** 2–3 small modules.
  - One module defining the pnp4-facing `PolyTimeVerifierSpec` or equivalent.
  - One module proving `PolyTimeVerifierSpec L → ComplexityInterfaces.NP L`.
  - Optional tests/audit module for the theorem surface.
- **Dependencies:** `pnp3/Complexity/Interfaces.lean`, the internal
  `PsubsetPpoly` TM model, and maybe pnp4 contract-expansion imports for a smoke
  application skeleton.
- **Risk:** low-to-medium.  The bridge theorem is simple if the spec stores a TM
  and exactly the `NP_TM`-shaped proofs.  The main risk is designing the spec too
  abstractly and accidentally reintroducing fake runtime `Prop` fields.

### General compiler layer cost

- **Lean modules:** likely 6+ modules, depending on how much parser/codec
  composition is formalized.
- **Dependencies:** TuringToolkit, parser serialization definitions, codec
  implementation, arithmetic bounds, and compositional runtime lemmas.
- **Risk:** high.  A general compiler from high-level pnp4 functions to the
  internal TM model is useful but much larger than the immediate seed-pack goal.

Recommended investment is the narrow adapter first, with explicit anti-faking
acceptance criteria.

## 8. Applicability to `PrefixExtensionLanguage`

**Answer:** `yes_plausible`

The proposed formalism is plausibly enough to prove:

```text
PrefixExtensionLanguage ∈ NP
```

but not from the current R1-B2a runtime budget alone.  R1-B2a supplies the right
checklist:

- ambient length includes the truth-table component;
- table length is bounded by the ambient length;
- threshold and witness lengths are polynomially bounded in `M`;
- malformed parser rejection and length-convention facts are named;
- parser/decode/evaluation/relation runtime obligations are separated.

A future proof still needs a concrete verifier implementation, or a compiled TM,
that performs:

1. parse the ambient input;
2. reject malformed input;
3. read a full target witness from the certificate;
4. check prefix agreement;
5. decode/check the tree-circuit witness;
6. evaluate or verify the relation within the ambient polynomial bound;
7. prove equivalence with `PrefixExtensionLanguage`.

The current runtime budget fields are not enough because they do not identify
algorithms or TMs.  With the proposed layer and a concrete parser/codec package,
`PrefixExtensionLanguage ∈ NP` becomes a plausible infrastructure theorem.

## 9. R1-C impact

Even if this formalism lands, R1-C does **not** automatically become plausible.

The formalism would solve only one blocker: honest NP membership for the
prefix-extension language.  It would not solve the deeper contract-expansion
blocker of obtaining the lower-bound/source obligation needed for mainline
P-vs-NP progress.  In particular, it would not create:

- `SearchMCSPWeakLowerBound`;
- `VerifiedNPDAGLowerBoundSource`;
- `NP_not_subset_PpolyDAG`;
- any final endpoint.

Therefore:

```text
R1-C impact: improves prerequisites, but R1-C remains not authorised and not
mathematically justified without a separate source/lower-bound breakthrough.
```

A future R1-C-like application should only be considered after:

1. the polynomial-time formalism bridge lands;
2. `PrefixExtensionLanguage ∈ NP` is actually proved for a concrete parser/codec;
3. a separate, explicit source theorem or lower-bound obligation is identified;
4. the operator explicitly authorizes a new pack that is not merely another
   R1-cadence dispatch.

## 10. Recommendation

**Recommendation:** `invest_in_formalism`

Invest in a small TM-backed pnp4 polynomial-time verifier-spec adapter.  Do not
start with a broad compiler or general computability framework.  The next pack,
if authorised, should be tightly scoped to infrastructure:

- define a minimal verifier-spec record outside the pnp3 trust root;
- prove the bridge theorem into `Pnp3.ComplexityInterfaces.NP`;
- add surface/audit tests if the theorem is public;
- include a negative-design note explaining why bare `Prop` runtime placeholders
  are insufficient.

Do not open R1-C as the next step.  The next authorised implementation pack, if
any, should be a polynomial-time formalism adapter pack, not a contract-expansion
lower-bound pack.

## Structured output summary

```text
Outcome: REPORT_LANDED
report path: seed_packs/polynomial_time_formalism_scoping_D0/reports/D0_polynomial_time_formalism_gpt55.md
executive verdict: GREEN-light_formalism_investment
minimum formalism: TM-backed PolyTimeVerifierSpec adapter for pnp3 NP_TM
bridge theorem shape: PolyTimeVerifierSpec L → Pnp3.ComplexityInterfaces.NP L
cost estimate: 2–4 weeks for narrow adapter; multi-month for general compiler/DSL
PrefixExtensionLanguage applicability: yes_plausible
R1-C impact: not automatically plausible; still not authorised without separate lower-bound/source breakthrough
recommendation: invest_in_formalism
```
