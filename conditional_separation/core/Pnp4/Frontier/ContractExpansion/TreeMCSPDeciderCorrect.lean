import Pnp4.Frontier.ContractExpansion.TreeMCSPGreedyExtendable

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-!
# `CorrectNextBitDecider` from a real prefix-extension decider

Block 8b of the downstream decision→search extraction.

Block 8a (#1504) proved the greedy extendability invariant *under* the abstract
hypothesis `CorrectNextBitDecider`.  This file **discharges** that hypothesis from a
concrete assumption that is actually about the prefix-extension *language*: if `dec`
decides `PrefixExtensionLanguage` at the parser's ambient length `treeMCSPPrefixM
codec n`, then it is a correct next-bit decider.

The bridge is the true-extension query round-trip (Block 4 / #1504):
the query `prefixStateQueryValue codec n (i+1) hi x (Fin.snoc p true)` *parses* back
to the canonical prefix-input for `(i+1, p ++ true)`, whose
`PrefixExtendableInput` is exactly `WitnessPrefixExtendable … (Fin.snoc p true)`
(Block 7.5).  So the language's verdict on the encoded `p ++ true` is precisely the
next-bit extendability `CorrectNextBitDecider` needs.

Scope discipline — decider-correctness bridge only:

* the decider's language-correctness is still an **explicit hypothesis**;
* **no** `BoundedSearchSolver`, **no** full `solves` conclusion;
* **no** `PpolyDAG`/`InPpolyDAG` bridge, endpoint, or `P ≠ NP` consequence.
-/

variable {threshold : Nat → Nat}

/-- `dec` decides the prefix-extension language at the parser's ambient length: at
every query string it agrees with `PrefixExtensionLanguage`. -/
def DecidesPrefixExtensionLanguage
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n)) : Prop :=
  ∀ y : PrefixBitVec (treeMCSPPrefixM codec n),
    C_DAG.eval dec y
      = PrefixExtensionLanguage (treeMCSPConcretePrefixParser threshold codec)
          (treeMCSPPrefixM codec n) y

/--
**Discharge of `CorrectNextBitDecider`.**  A decider for the prefix-extension
language is a correct next-bit decider: run on the encoded `p ++ true` query it
answers exactly whether `p ++ true` is extendable.

The forward/backward directions both go through the query parser round-trip
(`parse_prefixStateQueryValue`) and `prefixExtendableInput_iff_witnessPrefixExtendable`.
-/
theorem correctNextBitDecider_of_decidesLanguage
    (codec : TreeCircuitWitnessCodec threshold)
    (n : Nat)
    (dec : C_DAG.Family (treeMCSPPrefixM codec n))
    (x : PrefixBitVec (Pnp3.Models.Partial.tableLen n))
    (hdec : DecidesPrefixExtensionLanguage codec n dec) :
    CorrectNextBitDecider codec n x dec := by
  intro i hi p
  rw [hdec (prefixStateQueryValue codec n (i + 1) hi x (Fin.snoc p true)),
      PrefixExtensionLanguage_accepts_iff]
  constructor
  · rintro ⟨input, hparse, hext⟩
    have hpeq : parsePrefixInput (treeMCSPConcretePrefixParser threshold codec)
          (prefixStateQueryValue codec n (i + 1) hi x (Fin.snoc p true))
          = some (CanonicalRawTreeMCSPPrefixFields.toPrefixInput codec
              (prefixStateFields codec n (i + 1) hi x (Fin.snoc p true))) :=
      parse_prefixStateQueryValue codec n (i + 1) hi x (Fin.snoc p true)
    rw [hpeq] at hparse
    obtain rfl := Option.some.inj hparse.symm
    exact (prefixExtendableInput_iff_witnessPrefixExtendable _).mp hext
  · intro hwit
    exact ⟨_, parse_prefixStateQueryValue codec n (i + 1) hi x (Fin.snoc p true),
      (prefixExtendableInput_iff_witnessPrefixExtendable _).mpr hwit⟩

end ContractExpansion
end Frontier
end Pnp4
