# E06: CHOPRS 2020 magnification-vs-locality link

**Engineer:** E06 | **Phase:** A | **Estimated:** 2 weeks | **Difficulty:** high | **Dependencies:** can run in parallel with E04/E05

## Goal

Formalize the **statement** of CHOPRS 2020's central magnification-vs-locality theorem as a Lean typed surface: *"if magnification holds for target T and locality barrier holds for method M, then M cannot prove T's lower bound"*.

## Source material

* CHOPRS, ITCS 2020, arXiv:1911.08297.
* Specific theorem: §4 / §5 — magnification chains through locality.

## Deliverable

```
pnp4/Pnp4/Literature/CHOPRS2020/MagnificationLocalityLink.lean
```

### Expected signatures

```lean
namespace Pnp4
namespace Literature
namespace CHOPRS2020

/-- "Magnification" abstractly: weak lower bound implies strong lower bound. -/
structure MagnificationStatement (C : Pnp4.AlgorithmsToLowerBounds.CircuitFamilyClass) where
  weakBoundFamily : Pnp4.AlgorithmsToLowerBounds.BitVecLanguage → Prop
  strongBoundFamily : Pnp4.AlgorithmsToLowerBounds.BitVecLanguage → Prop
  magnifies : ∀ L, weakBoundFamily L → strongBoundFamily L

/-- The CHOPRS theorem statement: locality preservation + magnification ⇒ method
    cannot prove weak bound either. -/
theorem CHOPRS_MagnificationLocality
    {C : Pnp4.AlgorithmsToLowerBounds.CircuitFamilyClass}
    (M : LowerBoundProofMethod C)
    (B : LocalityBarrier C M)
    (mag : MagnificationStatement C)
    (L : Pnp4.AlgorithmsToLowerBounds.BitVecLanguage)
    (hL_weak : mag.weakBoundFamily L)
    (hL_oracleCircuit : B.hasOracleAugmentedCircuit L) :
    ¬ M.ruleOut L :=
  fun h => B.obstruction L hL_oracleCircuit h
```

### Lemmas to prove

- `CHOPRS_MagnificationLocality` proven (it's a one-liner once the structures align).
- One smoke `#check` showing the theorem type-checks against E04/E05 imports.

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] `MagnificationStatement` structure defined.
- [ ] `CHOPRS_MagnificationLocality` theorem proven.
- [ ] Module doc-comment cites CHOPRS §4-5.

## Scope

### Allowed
- `pnp4/Pnp4/Literature/CHOPRS2020/MagnificationLocalityLink.lean`.
- Imports from E04, E05 if landed.

### Forbidden
- Universal (COMMON §3).
- ❌ No claim that magnification holds for any specific `C` or `L`.

## Output
Universal template.
