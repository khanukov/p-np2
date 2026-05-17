# E05: CHOPRS 2020 locality barrier statement

**Engineer:** E05 | **Phase:** A | **Estimated:** 2 weeks | **Difficulty:** medium | **Dependencies:** can run in parallel with E04; if E04 lands first, import its `OracleAugmentedCircuit`

---

## Goal

Formalize the **statement** of the CHOPRS 2020 locality barrier as a Lean typed surface: *"target problems admit efficient circuits with small fan-in oracle gates, but lower-bound methods extend to such oracle-augmented circuits"*. This means: any natural lower-bound proof against `P/poly` (or a subclass) would also rule out small oracle-augmented circuits — which is impossible if such circuits exist for the target.

---

## Source material

* **Paper:** CHOPRS, ITCS 2020, arXiv:1911.08297.
* **Specific theorem:** §1 / §3 locality theorem: for natural proof methods M, if M proves L ∉ AC0 (say), then M also proves L ∉ AC0[OracleGate(small-fanin)], contradicting the existence of such oracle-augmented circuits for many `L`.

---

## Deliverable

```
pnp4/Pnp4/Literature/CHOPRS2020/LocalityBarrierStatement.lean
```

### Expected signatures

```lean
namespace Pnp4
namespace Literature
namespace CHOPRS2020

/-- Abstract "lower-bound proof method M": maps a language to a possible proof
    of non-membership in a circuit class. -/
structure LowerBoundProofMethod (C : Pnp4.AlgorithmsToLowerBounds.CircuitFamilyClass) where
  ruleOut : Pnp4.AlgorithmsToLowerBounds.BitVecLanguage → Prop
  -- The method ruling out C-membership: when M.ruleOut L holds, M asserts L ∉ C.

/-- Locality preservation: M extends to oracle-augmented circuits with bounded fan-in. -/
structure LocalityPreserving 
    (C : Pnp4.AlgorithmsToLowerBounds.CircuitFamilyClass)
    (M : LowerBoundProofMethod C) where
  extendsToOracleAugmented : 
    ∀ (n localFanin : Nat) (L : Pnp4.AlgorithmsToLowerBounds.BitVecLanguage),
      M.ruleOut L → -- M proves L ∉ C
      ∀ (_oracle_class : Type), True 
      -- placeholder: M's proof extends to circuits with oracle gates of fan-in ≤ localFanin

/-- The locality barrier: when M is locality-preserving, M cannot rule out languages
    that have small oracle-augmented circuits. -/
structure LocalityBarrier 
    (C : Pnp4.AlgorithmsToLowerBounds.CircuitFamilyClass)
    (M : LowerBoundProofMethod C) where
  preservesLocality : LocalityPreserving C M
  hasOracleAugmentedCircuit : 
    Pnp4.AlgorithmsToLowerBounds.BitVecLanguage → Prop
  obstruction : 
    ∀ L, hasOracleAugmentedCircuit L → ¬ M.ruleOut L
```

### Lemmas to prove

```lean
/-- A locality-preserving method ruling out `L` would rule out any `L'` with the same
    oracle-augmented circuit complexity. -/
theorem LocalityBarrier.transfer 
    {C : Pnp4.AlgorithmsToLowerBounds.CircuitFamilyClass}
    {M : LowerBoundProofMethod C}
    (B : LocalityBarrier C M) :
    ∀ L L', B.hasOracleAugmentedCircuit L → B.hasOracleAugmentedCircuit L' →
      M.ruleOut L → M.ruleOut L' → False

/-- The barrier interface is non-vacuous: there exist methods and languages
    where the obstruction structure is inhabitable. -/
theorem LocalityBarrier.nonVacuous_marker : True
```

---

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] `LowerBoundProofMethod` and `LocalityPreserving` structures defined.
- [ ] `LocalityBarrier` structure with `preservesLocality`, `hasOracleAugmentedCircuit`, `obstruction` fields.
- [ ] `transfer` theorem proven (it's basically an immediate consequence — if both `M.ruleOut L` and `B.obstruction L`, contradiction).
- [ ] `nonVacuous_marker` is just `True` — placeholder for future concrete inhabitations.
- [ ] Module doc-comment cites CHOPRS 2020 §1 + §3 explicitly.
- [ ] **No claim** that any specific method is locality-preserving or any specific language has oracle-augmented circuits — those are properties, not claims of this module.

### Verification
```bash
rg "^structure LowerBoundProofMethod" pnp4/Pnp4/Literature/CHOPRS2020/
rg "^structure LocalityBarrier" pnp4/Pnp4/Literature/CHOPRS2020/
rg "^theorem LocalityBarrier.transfer" pnp4/Pnp4/Literature/CHOPRS2020/
```

---

## Scope

### Allowed
- New module at `pnp4/Pnp4/Literature/CHOPRS2020/LocalityBarrierStatement.lean`.
- May import E04's `OracleAugmentedCircuit` if it has landed.
- Standard universal items.

### Forbidden
- Universal (COMMON §3).
- ❌ No claim that Razborov-Rudich is locality-preserving (that's E14).
- ❌ No claim that any specific lower-bound method falls under this barrier.
- ❌ No magnification-vs-locality theorem (that's E06).

---

## Notes

- The structure is intentionally abstract. CHOPRS's actual theorem requires a specific notion of "natural" proof method; this Lean surface lets future work plug in any concrete `M`.
- `extendsToOracleAugmented` is a `Prop` (placeholder); a future task may make this a real `Decidable` predicate.
- 2-week estimate assumes ~3 days reading CHOPRS §1-3, ~5 days Lean, ~2 days proving, ~2 days polish.

---

## Output

Universal template.
