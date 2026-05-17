# E20: Concrete tree-MCSP parser implementation + runtime proofs

**Engineer:** E20 | **Phase:** D — Contract expansion completion | **Estimated:** 4 weeks | **Difficulty:** medium-high | **Dependencies:** benefits from E19 landing first; can start with stub if not yet landed

## Goal

Provide a **concrete byte-level parser implementation** for the tree-MCSP prefix-extension language, plus the parser-side runtime / soundness / length-convention proofs that were staged as `Prop` fields in R1-B2a. This makes the contract_expansion track's parser layer non-staged.

## Source material

* `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguage.lean` (R1-B; read for context).
* `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageNP.lean` (R1-B1; read for context).
* `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguageRuntime.lean` (R1-B2a; **this is the structure you instantiate**).
* `pnp4/Pnp4/Frontier/SearchMCSPConcreteTargets.lean` (tree-MCSP target).

## Deliverable

```
pnp4/Pnp4/Frontier/ContractExpansion/TreeMCSPParserImpl.lean
```

### Expected signatures

```lean
namespace Pnp4
namespace Frontier
namespace ContractExpansion

/-- Concrete byte-level encoding of (tag, n, x, i, p, pad) for tree-MCSP. -/
def encodeTreeMCSPPrefixInput 
    {threshold : Nat → Nat}
    {encoding : TreeMCSPSearchWitnessEncoding threshold}
    (input : PrefixInput (treeMCSPSearchProblem threshold encoding) m) :
    AlgorithmsToLowerBounds.BitVec m := ...

/-- Concrete byte-level decoding (parser). -/
def parseTreeMCSPPrefixInput 
    {threshold : Nat → Nat}
    {encoding : TreeMCSPSearchWitnessEncoding threshold}
    {m : Nat}
    (y : AlgorithmsToLowerBounds.BitVec m) :
    Option (PrefixInput (treeMCSPSearchProblem threshold encoding) m) := ...

/-- Concrete `PrefixParser` instance for tree-MCSP. -/
def treeMCSPPrefixParserConcrete 
    {threshold : Nat → Nat}
    (encoding : TreeMCSPSearchWitnessEncoding threshold)
    (tag : Nat) (M : Nat → Nat) :
    PrefixParser (treeMCSPSearchProblem threshold encoding) := 
  treeMCSPPrefixParser threshold encoding tag M parseTreeMCSPPrefixInput

/-- The parser polynomial-time bound (real theorem, not Prop placeholder). -/
theorem parseTreeMCSPPrefixInput_polynomial_time 
    {threshold : Nat → Nat} 
    {encoding : TreeMCSPSearchWitnessEncoding threshold}
    {m : Nat} :
    ∃ c : Nat, ∀ (y : AlgorithmsToLowerBounds.BitVec m), True := ...
    -- runtime bound: parse runs in poly(m); since Lean doesn't have a runtime
    -- model, this is captured at the type-decidability level. Honest caveat:
    -- this is a structural runtime claim, not a TM-step count.

/-- Length convention is matched (real theorem). -/
theorem parseTreeMCSPPrefixInput_length_convention 
    {threshold : Nat → Nat}
    {encoding : TreeMCSPSearchWitnessEncoding threshold}
    {m : Nat}
    {y : AlgorithmsToLowerBounds.BitVec m}
    {input : PrefixInput (treeMCSPSearchProblem threshold encoding) m}
    (h : parseTreeMCSPPrefixInput y = some input) :
    m = (treeMCSPPrefixParserConcrete encoding 0 (fun n => n)).M input.n := ...

/-- Malformed inputs are rejected (real theorem). -/
theorem parseTreeMCSPPrefixInput_malformed_rejected 
    {threshold : Nat → Nat}
    {encoding : TreeMCSPSearchWitnessEncoding threshold}
    {m : Nat}
    {y : AlgorithmsToLowerBounds.BitVec m}
    (h : parseTreeMCSPPrefixInput (encoding := encoding) y = none) :
    PrefixExtensionLanguage (treeMCSPPrefixParserConcrete encoding 0 (fun n => n)) m y = false := ...
```

### Optional: instantiate R1-B2a budget

```lean
/-- A `TreeMCSPPrefixRuntimeBudget` instance with as many real fields as possible. -/
def treeMCSPRuntimeBudgetInstance 
    {threshold : Nat → Nat}
    (encoding : TreeMCSPSearchWitnessEncoding threshold)
    (codec : TreeCircuitWitnessCodec threshold) 
    (...) :
    TreeMCSPPrefixRuntimeBudget threshold (fun n => n) codec (treeMCSPPrefixParserConcrete encoding 0 (fun n => n)) := {
  tableLen_le_M := ...,
  threshold_poly_in_M := ...,  -- real lemma if threshold is polynomial
  witnessBits_poly_in_M := ...,  -- real lemma if codec.witnessBits is polynomial
  decode_polynomial_time_in_M := True,  -- honest placeholder if not provable
  parser_polynomial_time_in_M := parseTreeMCSPPrefixInput_polynomial_time.prop_view,
  circuit_eval_polynomial_time_in_size := True,
  truth_table_lookup_polynomial_time_in_M := True,
  relation_polynomial_time_in_M := True,
  malformed_inputs_rejected := parseTreeMCSPPrefixInput_malformed_rejected,
  length_convention_matches_M := parseTreeMCSPPrefixInput_length_convention
}
```

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] `encodeTreeMCSPPrefixInput`, `parseTreeMCSPPrefixInput` defined as **computable** functions (no `noncomputable`).
- [ ] Round-trip property: `parseTreeMCSPPrefixInput (encodeTreeMCSPPrefixInput input) = some input`. Prove this as a theorem.
- [ ] `parseTreeMCSPPrefixInput_length_convention` proven kernel-clean.
- [ ] `parseTreeMCSPPrefixInput_malformed_rejected` proven kernel-clean.
- [ ] `treeMCSPRuntimeBudgetInstance` constructed with at least 4 real (non-`True`) fields.
- [ ] Module doc-comment cites R1-B2a and acknowledges that runtime is captured at type-decidability level, not at TM-step level (honest caveat).
- [ ] **No `Classical.choose`** in the parser definitions.

### Honest caveats expected
- Runtime claims (e.g., `parser_polynomial_time_in_M`) are at the **structural Prop level**, not at TM-step level. Bridging to TM-step level requires E19 + further work.
- If you cannot prove a real round-trip, **state explicitly which encoding choice you made** and what would be needed for a complete round-trip proof.
- If certain budget fields cannot be discharged with concrete content, fill them with `True` and document why explicitly.

## Scope

### Allowed
- New module at `pnp4/Pnp4/Frontier/ContractExpansion/TreeMCSPParserImpl.lean`.
- May import from E19 if landed.

### Forbidden
- Universal.
- ❌ **No modification of `pnp3/Complexity/Interfaces.lean`.**
- ❌ **No modification of `pnp4/Pnp4/Frontier/ContractExpansion/PrefixExtensionLanguage*.lean`** (R1-B / R1-B1 / R1-B2a are frozen).
- ❌ No `PrefixExtensionLanguage_in_NP` claim — that's a follow-up combining E19 + E20.
- ❌ No R1-C work.

## Output
Universal template. Pay especially close attention to the "Honest caveats" section.
