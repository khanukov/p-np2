import Complexity.Interfaces
import Mathlib.Tactic

/-!
# Arbitrary log-width truth-table payload: all-essential predicate

Slot T1 for `seed_packs/fp3b2_arbitrary_logwidth_tt_payload/`.

This file is intentionally small and audit-only.  It introduces the local
Boolean-cube operation needed by the arbitrary-payload route: flipping one input
coordinate of a `Bitstring k`.  The predicate `AllEssential f` then says that
no coordinate is semantically dummy for `f`: every coordinate has some witness
input on which flipping that coordinate changes the output.

No lower-bound endpoint, bridge, provenance filter, source theorem, or final
P-vs-NP statement is introduced here.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace ArbitraryLogWidthTT

open Pnp3.ComplexityInterfaces

/--
Flip the `i`-th coordinate of a fixed-length bitstring and leave all other
coordinates unchanged.

A `Bitstring k` is definitionally a function `Fin k → Bool`, so the operation is
just `Function.update` at coordinate `i` with the negated old bit value.  Keeping
this operation named makes later support/diversity statements independent of the
particular update primitive used by Lean's library.
-/
def flipBit {k : Nat} (x : Bitstring k) (i : Fin k) : Bitstring k :=
  Function.update x i (! x i)

/-- The flipped coordinate is exactly negated. -/
@[simp] theorem flipBit_at {k : Nat} (x : Bitstring k) (i : Fin k) :
    flipBit x i i = ! x i := by
  simp [flipBit]

/-- Coordinates different from the flipped coordinate are preserved. -/
@[simp] theorem flipBit_ne {k : Nat} (x : Bitstring k) {i j : Fin k}
    (h : j ≠ i) :
    flipBit x i j = x j := by
  simp [flipBit, h]

/--
Every input coordinate is essential for `f`.

Equivalently, for each coordinate `i`, there is a witness input `x` such that
flipping only `i` changes the value of the Boolean function.  This is the local
predicate needed by later slots for arbitrary truth-table payloads.
-/
def AllEssential {k : Nat} (f : Bitstring k → Bool) : Prop :=
  ∀ i : Fin k, ∃ x : Bitstring k, f x ≠ f (flipBit x i)

/--
Smoke test: on one input bit, the identity function is all-essential.

The witness for the unique coordinate is the all-false bitstring; after flipping
that coordinate, the identity output changes from `false` to `true`.
-/
theorem allEssential_one_identity :
    AllEssential (fun x : Bitstring 1 => x ⟨0, by decide⟩) := by
  intro i
  fin_cases i
  refine ⟨fun _ => false, ?_⟩
  simp [flipBit]

end ArbitraryLogWidthTT
end AuditRoutes
end Magnification
end Pnp3
