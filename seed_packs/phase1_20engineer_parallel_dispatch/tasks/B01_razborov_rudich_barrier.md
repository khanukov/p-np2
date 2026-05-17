# B01: Razborov-Rudich natural proofs barrier — pnp4 extension

**Engineer:** B01 | **Phase:** 3 — Barriers | **Estimated:** 3 weeks | **Difficulty:** high

## Goal

Extend the minimal `pnp3/Barrier/NaturalProofs.lean` interface with a pnp4-side **kernel-checked formalization** of the Razborov-Rudich natural proofs barrier: constructive + large + useful triad, PRG-based adversary witness, formal statement that natural proofs useful against P/poly contradict one-way function existence.

**Do not modify `pnp3/Barrier/NaturalProofs.lean`.** All new content under `pnp4/Pnp4/Barriers/RazborovRudich/`.

## Source material

* Razborov, Rudich, "Natural Proofs", JCSS 1997. DOI: 10.1006/jcss.1997.1494.
* Carmosino, Impagliazzo, Kabanets, Kolokolova, "Learning Algorithms from Natural Proofs", CCC 2016.

## Deliverable

```
pnp4/Pnp4/Barriers/RazborovRudich/Triad.lean
pnp4/Pnp4/Barriers/RazborovRudich/PRGAdversary.lean
pnp4/Pnp4/Barriers/RazborovRudich/BarrierStatement.lean
```

### Expected signatures (Triad.lean)

```lean
namespace Pnp4
namespace Barriers
namespace RazborovRudich

def BooleanProperty (n : Nat) : Type :=
  ((Fin n → Bool) → Bool) → Prop

structure NaturalProperty (n : Nat) (P : BooleanProperty n) where
  constructive : Prop
  large : Prop
  usefulAgainstPpoly : Prop
```

### Expected signatures (PRGAdversary.lean)

```lean
structure PRGAdversary (n : Nat) where
  seedLength : Nat
  outputLength : Nat → Nat
  distinguishingClaim : Prop
```

### Expected signatures (BarrierStatement.lean)

```lean
structure RazborovRudichBarrier (n : Nat) where
  oneWayFunctionsExist : Prop
  barrierTheorem : ∀ P : BooleanProperty n, NaturalProperty n P → ¬ oneWayFunctionsExist

/-- Bridge from pnp3 minimal interface to pnp4 extension. -/
def RazborovRudichBarrier.toPnp3 (n : Nat) (B : RazborovRudichBarrier n) 
    (L : Pnp3.ComplexityInterfaces.Language) : 
    Pnp3.Barrier.NaturalProofConditions L := ...
```

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] Three modules at exact paths.
- [ ] `NaturalProperty`, `PRGAdversary`, `RazborovRudichBarrier` structures.
- [ ] Bridge `toPnp3` shows pnp4 extension subsumes pnp3 minimal interface.
- [ ] At least two theorems proven kernel-clean (e.g., `barrierTheorem` consequence + structure composition).
- [ ] Doc-comments cite RR 1997 + CIKK 2016.
- [ ] **Pnp3/Barrier/NaturalProofs.lean unchanged** (verified via `git diff`).

## Scope

### Allowed
- New modules under `pnp4/Pnp4/Barriers/RazborovRudich/`.

### Forbidden
- Universal.
- ❌ Editing `pnp3/Barrier/NaturalProofs.lean`.

## Output
Universal template.
