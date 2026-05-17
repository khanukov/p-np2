# E04: CHOPRS 2020 oracle-gate model

**Engineer:** E04 | **Phase:** A | **Estimated:** 2 weeks | **Difficulty:** medium | **Dependencies:** none

---

## Goal

Formalize the **oracle-gate circuit model** from Chen-Hirahara-Oliveira-Pich-Rajgopal-Santhanam (CHOPRS) ITCS 2020 ("Beyond Natural Proofs: Hardness Magnification and Locality"). This is the model where circuits have small fan-in oracle gates; the formalization underpins the locality-barrier theorem (E05) and the magnification-vs-locality link (E06).

---

## Source material

* **Paper:** Chen, Hirahara, Oliveira, Pich, Rajgopal, Santhanam, "Beyond Natural Proofs: Hardness Magnification and Locality", ITCS 2020.
* **Verifiable identifier:** arXiv:1911.08297; DOI 10.4230/LIPIcs.ITCS.2020.70.
* **Specific definition:** §1.2 / §2 oracle-augmented circuits with small fan-in.

---

## Deliverable

```
pnp4/Pnp4/Literature/CHOPRS2020/OracleGateModel.lean
```

### Expected signatures

```lean
namespace Pnp4
namespace Literature
namespace CHOPRS2020

/-- A single oracle gate: takes `fanin` input wires and produces one output bit
    according to an abstract function (the "oracle"). -/
structure OracleGate (n fanin : Nat) where
  inputs : Fin fanin → Fin n
  oracle : (Fin fanin → Bool) → Bool

/-- An oracle-augmented circuit: a circuit class with a fixed bound on oracle
    fan-in. -/
structure OracleAugmentedCircuit (n localFanin : Nat) where
  -- Underlying circuit is left abstract; the locality structure is the key.
  numOracleGates : Nat
  gates : Fin numOracleGates → OracleGate n localFanin
  -- Combiner: how the outputs of oracle gates combine to compute the function.
  combine : (Fin numOracleGates → Bool) → Bool

/-- Evaluate the circuit on an input. -/
def OracleAugmentedCircuit.eval {n localFanin : Nat}
    (C : OracleAugmentedCircuit n localFanin) 
    (x : AlgorithmsToLowerBounds.BitVec n) : Bool :=
  C.combine (fun i =>
    let g := C.gates i
    g.oracle (fun k => x (g.inputs k)))

/-- An `(s, t)`-locality bound: at most `s` oracle gates, each of fan-in ≤ `t`. -/
structure LocalityBound (s t : Nat) where
  -- Marker type; t is the local fan-in bound, s is the gate count.
```

### Lemmas to prove

```lean
/-- An oracle-augmented circuit with no oracle gates is constant. -/
theorem OracleAugmentedCircuit.eval_no_gates 
    {n localFanin : Nat} (C : OracleAugmentedCircuit n localFanin)
    (h : C.numOracleGates = 0) (x : AlgorithmsToLowerBounds.BitVec n) :
    C.eval x = C.combine (fun i => absurd i (by rw [h]; exact Fin.elim0))

/-- Fan-in scaling: if `localFanin₁ ≤ localFanin₂`, an `OracleAugmentedCircuit n localFanin₁`
    embeds into `OracleAugmentedCircuit n localFanin₂`. -/
theorem OracleAugmentedCircuit.fanin_monotone 
    {n localFanin₁ localFanin₂ : Nat} (h : localFanin₁ ≤ localFanin₂)
    (C : OracleAugmentedCircuit n localFanin₁) :
    ∃ C' : OracleAugmentedCircuit n localFanin₂, ∀ x, C'.eval x = C.eval x
```

---

## Acceptance criteria

### Universal
(see COMMON §4)

### Task-specific
- [ ] `OracleGate`, `OracleAugmentedCircuit` structures defined.
- [ ] `OracleAugmentedCircuit.eval` defined as a real function (computable; no `Classical`).
- [ ] `LocalityBound` marker structure defined.
- [ ] Two theorems proven kernel-clean (`eval_no_gates`, `fanin_monotone`).
- [ ] **No `Classical.choose`** in core definitions.
- [ ] Module doc-comment cites CHOPRS 2020 §1.2 explicitly.

### Verification
```bash
rg "^structure OracleGate" pnp4/Pnp4/Literature/CHOPRS2020/
rg "^structure OracleAugmentedCircuit" pnp4/Pnp4/Literature/CHOPRS2020/
rg "^def OracleAugmentedCircuit.eval" pnp4/Pnp4/Literature/CHOPRS2020/
```

---

## Scope

### Allowed
- New module at `pnp4/Pnp4/Literature/CHOPRS2020/OracleGateModel.lean`.
- Standard universal items.

### Forbidden
- Universal (COMMON §3).
- ❌ No commitment to a specific underlying circuit class (`PpolyDAG`, `AC0`, etc.) — keep oracle model abstract.
- ❌ No claim about magnification or locality consequences (those are E05/E06).

---

## Notes

- The oracle is an abstract function `(Fin fanin → Bool) → Bool`. Lean compiles fine with this; runtime is irrelevant since we're formalizing the model definition.
- `LocalityBound` is a marker for type signatures; it doesn't carry runtime data.
- If you need to interoperate with pnp4's `CircuitFamilyClass`, define an adapter function but do **not** modify `BasicCircuitClasses.lean`.

---

## Output

Universal template.
