import Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_codexd3a.AntiCollapsePrime
import Magnification.AuditRoutes.DistinguisherMatrixProvenance.V_codexd3c.Sharpness
import Mathlib.Tactic

/-!
# D6: sharp read-budget threshold for the payload-anchor family

This module is the synthesis step of the sparse-distinguisher-matrix audit
(Atserias–Müller style magnification, arXiv 2503.24061).  It combines the two
sides already proved for the concrete D3′ payload-anchor YES/far-NO relation:

* **lower bound** — `V_codexd3a.andPayload_no_sparse_fingerprintSeparation`: if
  `m * k + ρ ≤ widthFn n`, no `m`-row `k`-sparse matrix separates at radius `1`
  (it leaves `≥ ρ` payload coordinates unread, which an adversary flips);
* **upper bound** — `V_codexd3c.payloadIdentity_separates_payloadYes_farNo`: the
  full payload-identity matrix (`m = widthFn n`, `k = 1`) does separate at
  radius `1`.

The capstone `payload_separation_budget_sharp` reads off the consequence: for
`ρ = 1` the minimal read budget `m * k` needed to separate this family is
**exactly** `widthFn n` — necessary and achievable.

**Honest verdict — what this does and does not mean.**

For *this* family the read budget is forced to scale with the payload window
`widthFn n`: there is **no bounded-budget separator** (a strict no-go for the
"sidestep locality with a constant-budget distinguisher" hope on this family).

But this is **not** a barrier sidestep and **not** evidence toward one.  The
payload-anchor family localizes its YES/NO difference *inside* the readable
payload window by construction, so paying a budget equal to the window width is
just "reading where the difference lives".  Combined with D4/D5 (separation
power is bounded by the read footprint, and locality composes), the lesson is:
a genuine barrier sidestep would require a family whose hardness is **not**
confined to any small readable window — which is precisely the open lower-bound
problem this audit cannot manufacture.

Progress classification: side-track audit formalization (sharp read-budget
characterization for the D3′ toy family).  It introduces no source theorem,
provenance-filter promotion, `PpolyDAG` bridge, or `P ≠ NP` endpoint, and claims
no lower bound against a real hard family.
-/

namespace Pnp3
namespace Magnification
namespace AuditRoutes
namespace DistinguisherMatrixProvenance
namespace V_locality_d6

open ComplexityInterfaces
open Pnp3.Magnification.AuditRoutes.ArbitraryLogWidthTT
open V_gpt55
open V_codexd3a
open V_codexd3c

/--
**Necessary read budget.**

If an `m`-row `k`-sparse fingerprint matrix separates the payload-anchor
YES/far-NO relation (farness `ρ ≥ 1`) at radius `1`, then its read budget must
exceed the slack window: `widthFn n < m * k + ρ`.  This is the contrapositive of
the D3′-A anti-collapse theorem.
-/
theorem payload_separation_requires_budget
    {m n k ρ : Nat} (hρ : 1 ≤ ρ)
    (D : BoolMatrix m n) (hSparse : SparseDistinguisherMatrix m n k D)
    (hSep : FingerprintSeparation D (payloadYesSet n) (payloadFarNoSet n ρ) 1) :
    widthFn n < m * k + ρ := by
  by_contra h
  push_neg at h
  exact andPayload_no_sparse_fingerprintSeparation m n k ρ hρ h ⟨D, hSparse, hSep⟩

/--
At the minimal farness `ρ = 1`, any separating `m`-row `k`-sparse matrix must
read a budget of at least the full payload window: `widthFn n ≤ m * k`.
-/
theorem payload_separation_requires_full_window
    {m n k : Nat}
    (D : BoolMatrix m n) (hSparse : SparseDistinguisherMatrix m n k D)
    (hSep : FingerprintSeparation D (payloadYesSet n) (payloadFarNoSet n 1) 1) :
    widthFn n ≤ m * k := by
  have h := payload_separation_requires_budget (m := m) (n := n) (k := k) (ρ := 1)
    le_rfl D hSparse hSep
  omega

/--
**Achievable read budget.**

The payload-identity matrix is `1`-sparse with `widthFn n` rows (read budget
`widthFn n`) and separates the payload-anchor YES/far-NO relation at radius `1`
for every positive farness.
-/
theorem payload_separation_achievable_at_width (n ρ : Nat) (hρ : 1 ≤ ρ) :
    ∃ D : BoolMatrix (widthFn n) n,
      SparseDistinguisherMatrix (widthFn n) n 1 D ∧
      FingerprintSeparation D (payloadYesSet n) (payloadFarNoSet n ρ) 1 :=
  ⟨payloadIdentityMatrix n, payloadIdentityMatrix_sparse n,
    payloadIdentity_separates_payloadYes_farNo n ρ hρ⟩

/--
**Sharp threshold (the D6 capstone).**

For the payload-anchor family at minimal farness `ρ = 1`:

* (achievable) there is a `1`-sparse, `widthFn n`-row matrix separating at
  radius `1`, i.e. read budget `widthFn n` suffices; and
* (necessary) every separating `m`-row `k`-sparse matrix has `widthFn n ≤ m * k`.

Hence the minimal separating read budget for this family is exactly the payload
window width `widthFn n`.  The budget is forced to scale with the instance, so
no constant-budget distinguisher separates this family — a strict no-go that is,
however, expected: the family's YES/NO difference lives entirely inside the read
window (see the module header for why this is not a locality-barrier sidestep).
-/
theorem payload_separation_budget_sharp (n : Nat) :
    (∃ D : BoolMatrix (widthFn n) n,
        SparseDistinguisherMatrix (widthFn n) n 1 D ∧
        FingerprintSeparation D (payloadYesSet n) (payloadFarNoSet n 1) 1) ∧
    (∀ {m k : Nat} (D : BoolMatrix m n),
        SparseDistinguisherMatrix m n k D →
        FingerprintSeparation D (payloadYesSet n) (payloadFarNoSet n 1) 1 →
        widthFn n ≤ m * k) := by
  refine ⟨payload_separation_achievable_at_width n 1 le_rfl, ?_⟩
  intro m k D hSparse hSep
  exact payload_separation_requires_full_window D hSparse hSep

end V_locality_d6
end DistinguisherMatrixProvenance
end AuditRoutes
end Magnification
end Pnp3
