import Magnification.AuditRoutes.ArbitraryLogWidthTT.TTFormulaSupport
import Magnification.AuditRoutes.ArbitraryLogWidthTT.RenamePayload
import Magnification.AuditRoutes.LogWidthAdversary.Width_NatLog2

/-!
# Arbitrary log-width truth-table payload: parameterized family

Slot T4 for `seed_packs/fp3b2_arbitrary_logwidth_tt_payload/`.

This module packages the arbitrary all-essential payloads from T1, the
truth-table support theorem from T2, and the injective rename transport from T3
into a length-indexed family.  The family uses the same logarithmic window as
the earlier Nat.log2 log-width route:

`widthFn n = Nat.log2 (n + 1)`.

Progress category: side-track audit formalization.  The definitions below are
restricted formula/support plumbing for the arbitrary-payload audit route.  They
do not introduce a lower-bound endpoint, a source theorem, a provenance filter,
or any bridge to a final P-vs-NP statement.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace ArbitraryLogWidthTT

open Pnp3.ComplexityInterfaces
open Pnp3.Tests.FormulaSupportBoundsFalsifiabilityProbe

/--
The logarithmic payload width used by this arbitrary-payload family.

This is intentionally definitionally the Nat.log2 width from the existing
log-width adversary path, so downstream slots can share the established
arithmetic lemma `widthFn_le` without maintaining a second proof.
-/
def widthFn (n : Nat) : Nat :=
  Nat.log2 (n + 1)

/-- The logarithmic payload window fits into the ambient `n` inputs. -/
theorem widthFn_le (n : Nat) : widthFn n ≤ n := by
  simpa [widthFn] using
    Pnp3.Magnification.AuditRoutes.LogWidthAdversary.logWidth_le n

/--
A length-indexed family of arbitrary Boolean payloads on the logarithmic window.
-/
def PayloadFamily : Type :=
  ∀ n : Nat, Bitstring (widthFn n) → Bool

/-- Every member of the payload family depends on all of its own coordinates. -/
def AllEssentialPayload (F : PayloadFamily) : Prop :=
  ∀ n : Nat, AllEssential (F n)

/--
Embed the `n`-th logarithmic truth-table payload into the first `widthFn n`
coordinates of an `n`-variable formula.

The construction is purely syntactic: first build the exact truth-table formula
for the payload `F n`, then rename its leaves along the canonical prefix
embedding supplied by T3.
-/
def adversaryFamily_v_arbpayload
    (F : PayloadFamily) (n : Nat) : FormulaCircuit n :=
  FormulaCircuit.rename
    (embed (widthFn_le n))
    (ttFormula (F n))

/--
The language computed by the arbitrary-payload adversary family.

At each input length `n`, membership is evaluation of the corresponding renamed
truth-table formula on the length-`n` input.
-/
def adversaryLanguage_v_arbpayload
    (F : PayloadFamily) : Pnp3.ComplexityInterfaces.Language :=
  fun n x => FormulaCircuit.eval (adversaryFamily_v_arbpayload F n) x

/--
All-essential arbitrary payloads keep exactly `widthFn n` support coordinates
after embedding into the ambient length `n`.

The proof composes the T2 support-cardinality theorem for truth-table formulas
with the T3 cardinality transport theorem for injective canonical renamings.
-/
theorem adversaryFamily_v_arbpayload_support_card
    (F : PayloadFamily)
    (hF : AllEssentialPayload F)
    (n : Nat) :
    (FormulaCircuit.support
      (adversaryFamily_v_arbpayload F n)).card = widthFn n := by
  unfold adversaryFamily_v_arbpayload
  exact renamed_support_card_from_source_card
    (widthFn_le n)
    (ttFormula (F n))
    (ttFormula_support_card_of_allEssential (hF n))

end ArbitraryLogWidthTT
end AuditRoutes
end Magnification
end Pnp3
