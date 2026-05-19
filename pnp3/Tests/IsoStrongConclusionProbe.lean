import Complexity.Interfaces
import Models.Model_PartialMCSP
import Magnification.CanonicalAsymptoticTrackData
import Magnification.FinalResultMainline
import LowerBounds.AsymptoticDAGBarrierTheorems
import LowerBounds.AsymptoticDAGBarrierInterfaces
import LowerBounds.MCSPGapLocality
import «pnp3».Tests.GlobalHInDagContractProbe

/-!
# Iso-strong conclusion L0 probe (canonical track)

This file is intentionally local to `pnp3/Tests/` and does **not** alter any
mainline endpoint.  We attempt the recommended Direction N first; in this L0
session we land a structured **partial** result that cleanly exposes the exact
canonical arithmetic obligations produced by `IsoStrongFamilyEventually`.

The key extraction is: from `IsoStrongFamilyEventually` at the canonical family,
we can derive (for sufficiently large slices) the strict slack inequality
`m + 2 < 2^(2^m - κ m β)`.

This is the precise bridge needed by the proposed pigeonhole contradiction
(`m+2` YES-side cap vs. subcube cardinality above `m+2`).
-/

namespace Pnp3
namespace Tests
namespace IsoStrongConclusionProbe

open ComplexityInterfaces
open Models
open Magnification
open LowerBounds
open GlobalHInDagContractProbe

/-- Finite canonical index type for size-1 candidate circuits over `n` variables. -/
inductive Size1Candidate (n : Nat)
  | const : Bool → Size1Candidate n
  | input : Fin n → Size1Candidate n

namespace Size1Candidate

instance (n : Nat) : Fintype (Size1Candidate n) :=
  Fintype.ofFinite _

@[simp] lemma card_size1Candidate (n : Nat) :
    Fintype.card (Size1Candidate n) = n + 2 := by
  classical
  -- `Bool ⊕ Fin n` has cardinality `2 + n`, and `Size1Candidate n` is equivalent to it.
  let e : Size1Candidate n ≃ (Bool ⊕ Fin n) :=
    { toFun := fun c =>
        match c with
        | .const b => Sum.inl b
        | .input i => Sum.inr i
      invFun := fun s =>
        match s with
        | Sum.inl b => .const b
        | Sum.inr i => .input i
      left_inv := by intro c; cases c <;> rfl
      right_inv := by intro s; cases s <;> rfl }
  calc
    Fintype.card (Size1Candidate n)
        = Fintype.card (Bool ⊕ Fin n) := Fintype.card_congr e
    _ = Fintype.card Bool + Fintype.card (Fin n) := Fintype.card_sum
    _ = 2 + n := by simp
    _ = n + 2 := by omega

end Size1Candidate

/-- Shorthand for the canonical eventual gap-slice family. -/
private def F : GapSliceFamilyEventually :=
  eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym

@[simp] lemma F_Mof (n : Nat) : F.Mof n (F.Tof n (0 : Rat)) = n + 2 := by
  simp [F, eventualGapSliceFamily_of_asymptotic]

/--
From iso-strong on the canonical family, extract the eventual strict slack shape
for any admissible `β`: `m + 2 < 2^(2^m - κ m β)`.

This is the arithmetic target required by the Direction N pigeonhole plan.
-/
theorem canonical_isoStrong_implies_eventual_strict_slack
    (W : GlobalAsymptoticDAGWitness canonicalAsymptoticHAsym)
    (hIso :
      IsoStrongFamilyEventually
        (eventualGapSliceFamily_of_asymptotic canonicalAsymptoticHAsym)
        (globalWitness_to_hInDag W)) :
    ∃ β0 : Rat, 0 < β0 ∧
      ∃ κ : Nat → Rat → Nat,
        ∃ nIso : Rat → Nat,
          ∀ m : Nat, ∀ β : Rat,
            0 < β → β < β0 →
            m ≥ max F.N0 (nIso β) →
              m + 2 < 2 ^ (2 ^ m - κ m β) := by
  rcases hIso with ⟨β0, hβ0, κ, nIso, _hForce, hSlack⟩
  refine ⟨β0, hβ0, κ, nIso, ?_⟩
  intro m β hβPos hβLt hm
  -- Canonical `Mof` is exactly `m+2`, canonical `tableLen` is exactly `2^m`.
  have hRaw := hSlack m β hβPos hβLt hm
  simpa [F, eventualGapSliceFamily_of_asymptotic] using hRaw

/--
L0 status lemma:
we have not (in this bounded session) completed a full Direction N contradiction.
The missing ingredient is a kernel-level pigeonhole lemma converting the strict
slack inequality into an explicit counterexample `z` to the forcing clause.
-/
theorem isoStrong_conclusion_L0_status : True := by
  trivial

end IsoStrongConclusionProbe
end Tests
end Pnp3
