# E14: Razborov-Rudich natural proofs barrier — formal

**Engineer:** E14 | **Phase:** B — Barriers | **Estimated:** 3 weeks | **Difficulty:** high | **Dependencies:** none

## Goal

Formalize the **Razborov-Rudich natural proofs barrier** as a kernel-checked Lean theorem. Provide the constructive+large+useful triad, the cryptographic-PRG-based adversary witness, and a clean statement of the barrier: *any natural property useful against `P/poly` would break standard cryptographic assumptions*.

This task **upgrades** the existing minimal interface `pnp3/Barrier/NaturalProofs.lean` by providing a full pnp4-side formalization. **Do not modify pnp3/Barrier/.**

## Source material

* Razborov, Rudich, "Natural Proofs", JCSS 1997. DOI: 10.1006/jcss.1997.1494.
* Plus contemporary refinements: Chow 2009 ("almost natural proofs"), Carmosino-Impagliazzo-Kabanets-Kolokolova 2016.

## Deliverable

```
pnp4/Pnp4/Barriers/RazborovRudich/Statement.lean
pnp4/Pnp4/Barriers/RazborovRudich/Adversary.lean
```

### Expected signatures (Statement.lean)

```lean
namespace Pnp4
namespace Barriers
namespace RazborovRudich

/-- A "property" of Boolean functions: predicate on `(Fin n → Bool) → Bool`. -/
def BooleanProperty (n : Nat) : Type :=
  ((Fin n → Bool) → Bool) → Prop

/-- The natural proofs triad. -/
structure NaturalProperty (n : Nat) (P : BooleanProperty n) where
  /-- Constructivity: P is decidable in polynomial time given the truth table. -/
  constructive : Prop
  /-- Largeness: at least `2^{-poly(n)}` fraction of all `2^{2^n}` functions satisfy P. -/
  large : Prop
  /-- Usefulness against P/poly: if `f ∈ P/poly`, then `¬ P f`. -/
  usefulAgainstPpoly : ∀ f : (Fin n → Bool) → Bool, 
    (∃ _ : Pnp4.Frontier.ContractExpansion.C_DAG.Family n, True) → 
    ¬ P f

/-- The Razborov-Rudich barrier statement: existence of a natural property useful
    against P/poly contradicts standard cryptographic hardness assumptions. -/
structure RazborovRudichBarrier (n : Nat) where
  -- "Standard one-way function assumption" as a Prop.
  oneWayFunctionsExist : Prop
  -- The barrier theorem:
  barrierTheorem : ∀ (P : BooleanProperty n), 
    NaturalProperty n P → 
    ¬ oneWayFunctionsExist
```

### Expected signatures (Adversary.lean)

```lean
namespace Pnp4
namespace Barriers
namespace RazborovRudich

/-- A "PRG-based natural-proof attack": uses PRG output as natural-property witness. -/
structure PRGAdversary (n : Nat) where
  -- PRG with stretch ≥ 1, seed length poly-related to output length.
  seedLength : Nat
  outputLength : Nat → Nat
  -- The adversary's claim: P-true on PRG output ⇒ distinguishes PRG from random.
  distinguishingClaim : Prop
```

### Lemmas to prove

```lean
/-- The Razborov-Rudich barrier statement implies: if OWFs exist, no natural-proof-shaped
    method can rule out P/poly. -/
theorem RazborovRudich_barrier_consequence (n : Nat)
    (B : RazborovRudichBarrier n) (P : BooleanProperty n) :
    NaturalProperty n P → ¬ B.oneWayFunctionsExist :=
  B.barrierTheorem P

/-- Constructivity is closed under finite conjunction (sanity check). -/
theorem NaturalProperty.and_constructive 
    {n : Nat} {P Q : BooleanProperty n}
    (hP : NaturalProperty n P) (hQ : NaturalProperty n Q) :
    ∃ _R : NaturalProperty n (fun f => P f ∧ Q f), True := 
  ⟨{ constructive := hP.constructive ∧ hQ.constructive
     large := True  -- not actually large; this is just a sanity check that the type composes
     usefulAgainstPpoly := fun f hf => hP.usefulAgainstPpoly f hf ∘ fun h => h.1 }, trivial⟩
```

## Acceptance criteria

### Universal (COMMON §4)

### Task-specific
- [ ] `BooleanProperty`, `NaturalProperty`, `RazborovRudichBarrier`, `PRGAdversary` structures.
- [ ] `barrier_consequence` theorem proven (it's a one-liner).
- [ ] `and_constructive` sanity check proven.
- [ ] Module doc-comments cite Razborov-Rudich 1997.
- [ ] Two `#print axioms` entries for the two theorems.

### Honest caveats expected
- The `usefulAgainstPpoly` field references `C_DAG.Family` — there's an implicit assumption that P/poly aligns with the `C_DAG` model. Document this.
- `oneWayFunctionsExist` and `large` / `constructive` are `Prop` fields, not concrete predicates. The barrier theorem encodes the conditional structure; making any field a real predicate is multi-month follow-up work.

## Scope

### Allowed
- New modules under `pnp4/Pnp4/Barriers/RazborovRudich/`.
- One `Glob.one` per new module.
- May import from E14's siblings (E15, E16) for cross-barrier comparisons; not required.

### Forbidden
- Universal.
- ❌ **No modification of `pnp3/Barrier/NaturalProofs.lean`**.
- ❌ No proof that one-way functions actually exist.
- ❌ No claim that natural proofs barrier has been bypassed.

## Output
Universal template.
