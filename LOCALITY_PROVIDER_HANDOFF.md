# Handoff: What Must Be Proved To Close The Remaining Conditional Gap

## 1. Goal (single blocking item)
Current pipeline is already refactored so that the final claim can be obtained from a **provider hypothesis** and no longer needs to mention the axiom directly.

The remaining blocker is to replace the default axiomatic provider with a constructive theorem.

Concretely, you must deliver a proof of:

```lean
Pnp3.Magnification.StructuredLocalityProviderPartial
```

defined in:
- `pnp3/Magnification/Facts_Magnification_Partial.lean:41`

If this is proven constructively and used as default provider, the conditional surface caused by `ppoly_circuit_locality` can be removed.

---

## 2. Minimal Lean context (exact definitions)

### 2.1 Locality target over Partial MCSP language
File: `pnp3/Magnification/Facts_Magnification_Partial.lean:33`

```lean
def LanguageLocalityPartial (p : GapPartialMCSPParams) : Prop :=
  ∃ (alive : Finset (Fin (Models.partialInputLen p))),
    alive.card ≤ Models.partialInputLen p / 4 ∧
    ∀ x y : Core.BitVec (Models.partialInputLen p),
      (∀ i ∈ alive, x i = y i) →
        gapPartialMCSP_Language p (Models.partialInputLen p) x =
        gapPartialMCSP_Language p (Models.partialInputLen p) y
```

### 2.2 Provider statement to prove
File: `pnp3/Magnification/Facts_Magnification_Partial.lean:41`

```lean
def StructuredLocalityProviderPartial : Prop :=
  ∀ (p : GapPartialMCSPParams),
    ComplexityInterfaces.PpolyStructured (gapPartialMCSP_Language p) →
      LanguageLocalityPartial p
```

### 2.3 Current default provider (axiomatic)
File: `pnp3/Magnification/LocalityProvider_Partial.lean:14`

```lean
noncomputable def defaultStructuredLocalityProviderPartial :
    StructuredLocalityProviderPartial := by
  intro p hPpolyStructured
  exact
    ThirdPartyFacts.ppolyStructured_circuit_locality
      (Models.gapPartialMCSP_Language p) hPpolyStructured (Models.partialInputLen p)
```

This is what must be replaced.

---

## 3. Where your result plugs into the proof pipeline

### 3.1 Provider-based (axiom-clean signature) route already exists
- `pnp3/Magnification/Facts_Magnification_Partial.lean:245`
  `OPS_trigger_general_contra_structured_with_provider_partial`
- `pnp3/Magnification/Facts_Magnification_Partial.lean:...`
  `OPS_trigger_formulas_contra_structured_with_provider_partial`
- `pnp3/Magnification/Facts_Magnification_Partial.lean:...`
  `OPS_trigger_formulas_partial_of_provider`
- `pnp3/Magnification/Bridge_to_Magnification_Partial.lean:27`
  `NP_not_subset_Ppoly_from_partial_formulas (hProvider : StructuredLocalityProviderPartial)`
- `pnp3/Magnification/Bridge_to_Magnification_Partial.lean:43`
  `P_ne_NP_from_partial_formulas (hProvider : StructuredLocalityProviderPartial)`
- `pnp3/Magnification/FinalResult.lean:74`
  `P_ne_NP_final_with_provider (hProvider : StructuredLocalityProviderPartial)`

So once provider is constructive, this whole chain becomes constructive.

### 3.2 Currently conditional default route
- `..._default` theorems still use `defaultStructuredLocalityProviderPartial`.

---

## 4. Exactly what external team should return

Return one of these (A preferred):

1. **A. Constructive theorem implementation**
   - A file/module proving `StructuredLocalityProviderPartial`.
   - Then redefine `defaultStructuredLocalityProviderPartial` to use that theorem.

2. **B. Stronger direct theorem**
   - A constructive replacement for
     `ThirdPartyFacts.ppolyStructured_circuit_locality`
     in `pnp3/ThirdPartyFacts/PpolyFormula.lean`.
   - Then `defaultStructuredLocalityProviderPartial` can remain thin.

Either A or B is sufficient.

---

## 5. Strong acceptance criteria (must all pass)

1. Build passes:
```bash
bash scripts/check.sh
```

2. Unconditional gate passes:
```bash
UNCONDITIONAL=1 bash scripts/check.sh
```

3. Axiom audit no longer reports `ppoly_circuit_locality` on final path:
- `Pnp3.Magnification.P_ne_NP_final`
- `Pnp3.Magnification.P_ne_NP_from_partial_formulas_default`

4. `pnp3/ThirdPartyFacts/PpolyFormula.lean` has no `axiom ppoly_circuit_locality` (or is out of active path and inventory = 0).

---

## 6. Helpful existing scaffolding (already prepared)

- Structured P/poly interface and equivalence:
  - `Facts/PsubsetPpoly/Proof/Complexity/Interfaces.lean`
  - `InPpolyStructured`, `PpolyStructured`, `ppoly_iff_ppolyStructured`
- Bridge-level provider abstraction:
  - `pnp3/Magnification/Facts_Magnification_Partial.lean`
  - `pnp3/Magnification/LocalityProvider_Partial.lean`
- Demo for carrier-specific locality pattern:
  - `pnp3/Tests/StructuredLocalityDemo.lean`

---

## 7. Practical guidance for theorem shape

If full general provider is too broad at first, prove a carrier-specific locality theorem in the form:

```lean
theorem carrier_locality
  (p : GapPartialMCSPParams)
  (w : Facts.PsubsetPpoly.Complexity.InPpolyStructured (Models.gapPartialMCSP_Language p))
  (hExtra : ...structural conditions on w...) :
  Pnp3.Magnification.StructuredFamilyLocalityPartial p w
```

Then combine with:
- `language_locality_of_structuredFamilyLocality`
- `generalCircuitSolver_of_structuredWitness_partial`

to bootstrap towards full provider.

---

## 8. Current status snapshot

- Provider-parametric final theorem exists and is axiom-clean in signature:
  - `pnp3/Magnification/FinalResult.lean:74` (`P_ne_NP_final_with_provider`)
- Default final theorem still depends on `ppoly_circuit_locality`:
  - `pnp3/Magnification/FinalResult.lean:68` (`P_ne_NP_final`)
  - `pnp3/ThirdPartyFacts/PpolyFormula.lean:63` (axiom)

So the project is technically “one theorem family away” from removing this conditional edge.
