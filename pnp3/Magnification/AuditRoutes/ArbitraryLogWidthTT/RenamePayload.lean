import Magnification.AuditRoutes.LogWidthAdversary.RenameSupport

/-!
# Arbitrary log-width truth-table payloads: rename support transport

This module is slot T3 of
`seed_packs/fp3b2_arbitrary_logwidth_tt_payload/`.  It packages the canonical
order-preserving embedding from a `k`-variable payload alphabet into an
`n`-variable ambient alphabet, and transports support-cardinality facts through
`FormulaCircuit.rename` along that embedding.

Progress category: infrastructure.  The lemmas below are syntactic
plumbing for the arbitrary-payload audit route; they do not introduce a new
lower-bound source obligation, endpoint, or trust root.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace ArbitraryLogWidthTT

open ComplexityInterfaces
open Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe

/--
The canonical inclusion of the first `k` input coordinates into an ambient
`n`-coordinate alphabet, available whenever `k ≤ n`.

At the value level this map is just the identity on natural-number indices.
The proof field is transported across `h : k ≤ n`, so a value known to be less
than `k` is also known to be less than `n`.
-/
def embed {k n : Nat} (h : k ≤ n) : Fin k → Fin n :=
  fun i => ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩

/--
The canonical prefix embedding is injective.

Since `embed h` does not change the underlying natural-number value, equality
after embedding immediately gives equality of `Fin` values back in the source.
-/
theorem embed_injective {k n : Nat} (h : k ≤ n) :
    Function.Injective (embed h) := by
  intro i j hij
  apply Fin.ext
  exact congrArg (fun x : Fin n => x.val) hij

/--
Renaming a payload formula along the canonical embedding preserves a known
source support cardinality.

This theorem deliberately separates the source-support fact from how it was
obtained.  Downstream slots may instantiate `hc` with a truth-table-formula
support theorem from `AllEssential`, while this T3 module only needs the
already-proved S5 syntactic transport lemma for injective renamings.
-/
theorem renamed_support_card_from_source_card
    {k n : Nat} (h : k ≤ n)
    (c : FormulaCircuit k)
    (hc : (FormulaCircuit.support c).card = k) :
    (FormulaCircuit.support
      (FormulaCircuit.rename (embed h) c)).card = k := by
  rw [Pnp3.Magnification.AuditRoutes.LogWidthAdversary.rename_support_card
    (embed h) (embed_injective h) c]
  exact hc

end ArbitraryLogWidthTT
end AuditRoutes
end Magnification
end Pnp3
