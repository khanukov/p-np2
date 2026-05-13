# Review — V2_C_GPT55 / codex55c

## 1. Verdict

**Verdict: `approve_with_changes`.**

The Phase 1 sketch compiles, defines a well-formed structural predicate, and is **not** killed by the fp3b4 support-cardinality-only barrier.  The claimed OR-family non-vacuity is plausible.  However, Phase 2 must treat this as a risky survivor rather than a near-proof: the bounded-size-increment conjunct is only a size recurrence, not an edit-distance or subformula-containment condition, and the false-slice zero-extension leaves a potentially large true-slice surface.  The Phase 2 prompt below therefore makes `NotSupportCardinalityOnly.lean` and the true-slice/payload attack the first priorities.

Scope classification: **Infrastructure / side-track audit review.**  This review does not claim mainline progress toward `P != NP`; it only assesses whether one audit-filter sketch is worth a Phase 2 self-attack.

## 2. NOGO-000007 self-test

**Answer: NO — `ProvenanceFilter_v2_V2_C_GPT55` does not appear to satisfy `IsSupportCardinalityOnly`.**

The predicate is not determined by the profile

```lean
n ↦ (FormulaCircuit.support (w.family n)).card
```

alone.  It asks for a global constant `δ` such that two conditions hold:

1. **Bounded size increment:**
   ```lean
   FormulaCircuit.size (w.family (n + 1)) ≤ FormulaCircuit.size (w.family n) + δ
   ```
   This depends on the full syntactic formula size at adjacent lengths.  The support-cardinality profile forgets gate multiplicity, duplicate occurrences, constants, negations, and the size cost of truth-table syntax.  Two witnesses can have the same support cardinality at every length but radically different size jumps.

2. **Zero-extension identity:**
   ```lean
   FormulaCircuit.eval (w.family (n + 1))
     (fun i => if h : i.val < n then x ⟨i.val, h⟩ else false)
   = FormulaCircuit.eval (w.family n) x
   ```
   This depends on cross-length semantics of the actual formulas.  The support-cardinality profile forgets the Boolean function computed by each formula and forgets how the length-`n` and length-`n+1` functions relate under false-padding.

A concrete Phase 2 route for `¬ IsSupportCardinalityOnly` should exhibit two strict `InPpolyFormula` witnesses with identical support-cardinality functions but different filter membership.  The easiest conceptual pair is: an OR-chain family versus a same-support family that deliberately flips the false-extension recurrence at selected lengths, or a same-support family with unbounded duplicate-gate blowups.  Same support cardinalities do not force either equal size increments or equal false-slice semantics.

Therefore NOGO-000007 does **not** automatically reject the candidate.  Phase 2 must still prove this kernel-checked, because `support_cardinality_barrier` applies immediately if this assessment is wrong.

## 3. Non-vacuity assessment

The sketch names **OR of all input bits** as the honest family.  This is concrete, named, and plausible.

For a standard right-associated formula

```text
OR_n(x_0, …, x_{n-1})
```

we have:

* **Zero-extension:** `OR_{n+1}(x, false) = OR_n(x)` because appending a final false disjunct does not change an OR.
* **Bounded size increment:** a right-associated OR formula adds one new input leaf and one OR gate when the new variable is appended, so a small fixed `δ` such as `2` or `3` should witness
  ```lean
  size (OR_{n+1}) ≤ size (OR_n) + δ.
  ```
* **Strict formula witness:** the family has linear size, so it is easily polynomially bounded.

I recommend keeping OR rather than replacing it by parity.  Parity is also natural but requires building XOR from `not/and/or`, making the zero-extension proof use XOR-with-false lemmas.  OR is simpler and matches the sketch.

## 4. Five-paragraph review

### (i) Excludes NOGO-000001

The prose is directionally sound: `OverbroadUniformProvenance` by itself does not enforce any adjacent-length semantic compatibility or bounded growth discipline.  V2-C is strictly more structured than the overbroad shape because it inspects `w.family`, `FormulaCircuit.size`, and `FormulaCircuit.eval` across lengths.

Phase 2 must be careful not to state an impossible theorem that every overbroad-uniform witness is rejected; `OverbroadUniformProvenance` is a broad provenance assumption, not a single canonical witness term.  The useful theorem should target the concrete hardwiring/singleton witness shape underlying NOGO-000001, or a precise witness extracted by the existing NOGO-000001 route.  If no canonical witness term is available, Phase 2 should state a local exclusion lemma for the fixed-slice hardwiring record used by the falsifiability probe rather than a vague theorem over all `hOverbroad` assumptions.

### (ii) Excludes NOGO-000004/000005

The prefix-AND discussion is plausible and uses semantic structure beyond support counting.  At lengths where `logWidthNat` increases from `k` to `k+1`, the new prefix-AND formula requires the newly included prefix coordinate to be true.  Under V2-C's zero-extension map, that coordinate is an old coordinate of `x` rather than merely the appended final coordinate, and there are assignments where the old prefix-AND is true but the new one becomes false when the freshly included coordinate is false.  This should violate the zero-extension identity.

Phase 2 should avoid relying solely on size increments here: prefix-AND has constant-size increments over many steps and small jumps at width increases.  The robust obstruction is the false-extension semantic failure at width-increase lengths.

### (iii) Excludes NOGO-000006

The sketch's high-level claim is plausible for the specific fp3b2 arbitrary all-essential `ttFormula` family.  When `widthFn` increases, the renamed truth-table formula at length `n+1` depends essentially on a fresh prefix coordinate that the previous length ignored.  The false-padding map only sets the final ambient coordinate to `false`; it does not erase this fresh prefix coordinate.  All-essentiality should therefore produce two old inputs with the same old payload value but different new payload value, contradicting zero-extension.

The size-jump sentence needs tightening.  The current predicate only bounds `size (family (n+1)) - size (family n)`; it does **not** require an edit script or require `family n` to occur syntactically inside `family (n+1)`.  Consequently, Phase 2 should make the zero-extension/all-essential argument primary.  The bounded-size argument may still help against payload injection, but it should not be presented as if it were a syntactic incremental-edit condition.

### (iv) Non-vacuity

OR of all inputs is a good non-vacuity target.  It satisfies the false-extension identity exactly and admits a linear-size formula with constant growth.  Phase 2 should define a concrete `orAll` formula family, prove its size recurrence, package it as an `InPpolyFormula`, and prove `V2_C_GPT55_admits_orAll`.

### (v) Self-attack

The self-attack paragraph identifies the right danger: the predicate fixes only the `newBit = false` slice.  An adversary may try to hide payload on the `newBit = true` slice while preserving all false-slice identities.  The bounded-size-increment conjunct blocks the most naive version that inserts a fresh logarithmic truth table from scratch at every length, but it does not by itself prove that all accumulated true-slice payloads are harmless.  Since the recurrence is semantic plus size-based, not edit-distance-based, Phase 2 must explicitly test whether a recursively accumulated hardwiring family can maintain `O(1)` size increments and still encode a log-width payload over time.

This is the main reason for `approve_with_changes` rather than plain `approve`.

## 5. Phase 2 readiness checklist

Phase 2 must produce only review-approved Lean artifacts under:

```text
pnp3/Magnification/AuditRoutes/ProvenanceFilterV2/V2_C_GPT55/
```

Required files and theorem surfaces:

1. `Filter.lean` defining/re-exporting `ProvenanceFilter_v2_V2_C_GPT55`.
2. `NotSupportCardinalityOnly.lean` proving:
   ```lean
   theorem ProvenanceFilter_v2_V2_C_GPT55_not_support_cardinality_only :
       ¬ Pnp3.Magnification.AuditRoutes.SupportCardinalityBarrier.IsSupportCardinalityOnly
           @ProvenanceFilter_v2_V2_C_GPT55
   ```
3. `ExcludesOverbroad.lean` proving a precise NOGO-000001 hardwiring exclusion, preferably against the fixed-slice witness used by the existing probe.
4. `ExcludesPrefixAnd.lean` proving:
   ```lean
   theorem excludes_prefixAnd_V2_C_GPT55 :
       ¬ ProvenanceFilter_v2_V2_C_GPT55
           Pnp3.Magnification.AuditRoutes.LogWidthAdversary.adversaryWitness_v_natlog2
   ```
   If the project exposes the fp3b1 witness only through a different namespace alias, use that exact imported identifier and keep this theorem name.
5. `ExcludesArbitraryPayload.lean` proving:
   ```lean
   theorem excludes_arbitrary_payload_V2_C_GPT55
       (F : Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.PayloadFamily)
       (hF : Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT.AllEssentialPayload F) :
       ¬ ProvenanceFilter_v2_V2_C_GPT55
           (Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT
             .adversaryWitness_v_arbpayload F hF)
   ```
6. `NonVacuity.lean` defining `orAll` / `orAll_witness` and proving:
   ```lean
   theorem V2_C_GPT55_admits_orAll :
       ProvenanceFilter_v2_V2_C_GPT55 orAll_witness
   ```
7. `Survivor.lean` composing the above as:
   ```lean
   theorem ProvenanceFilter_v2_V2_C_GPT55_survives_known_obstructions :
       True
   ```
   or a stronger structured conjunction if the involved theorem types can be packaged cleanly without introducing axioms or typeclass-payload shortcuts.

Phase 2 must also update `lakefile.lean` for new modules, run `lake build PnP3 Pnp4`, run `./scripts/check.sh`, avoid `sorry`/`admit`, avoid JSONL edits until the Phase 2 contract explicitly asks for append-only attempt logging, and must not touch trust root, candidates, source theorems, `gap_from`, accepted-filter promotion, or Wave 1 activation.

## 6. Risks for Phase 2

* **True-slice payload risk:** zero-extension only controls `(x, false)`.  Payload on `(x, true)` may accumulate over lengths; Phase 2 must either exclude it or report a structured failure.
* **Size recurrence is not edit distance:** `size (n+1) ≤ size n + δ` does not mean `family (n+1)` was obtained from `family n` by a bounded local edit.
* **NOGO-000001 theorem-shape risk:** an overbroad provenance assumption may not determine a unique witness.  Target the concrete fixed-slice witness or state a precise local lemma.
* **All-essential proof burden:** excluding arbitrary payload should rely on all-essentiality at width-increase lengths and must handle the fact that the fresh log-width coordinate is not the final ambient coordinate.
* **Kernel plumbing risk:** OR non-vacuity is simple mathematically but still needs careful `Fin` casts for the zero-extension identity.
* **Vacuity/circularity risk:** do not strengthen the filter in Phase 2 to exclude everything, and do not add opaque provenance/certification fields.
