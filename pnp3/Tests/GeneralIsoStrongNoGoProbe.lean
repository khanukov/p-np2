import Models.Model_PartialMCSP
import LowerBounds.AsymptoticDAGBarrierTheorems
import LowerBounds.AsymptoticDAGBarrierInterfaces
import LowerBounds.MCSPGapLocality
import Tests.CircuitCountTraceBoundProbe

/-!
# General iso-strong no-go probe (L1, session 1)

L1 staging probe consuming the counting bricks landed in
`pnp3/Tests/CircuitCountTraceBoundProbe.lean` and lifting two further
generalisation lemmas towards `isoStrong_conclusion_negative_general`.

This file is intentionally local to `pnp3/Tests/` and does not modify
endpoints, specs, or trust-root surfaces.  No `axiom` / `opaque` /
`sorry` / `admit` / `native_decide` are introduced.  The remaining
generalised contradiction assembly is staged for a follow-up L1
session (`open_general_isoStrong_no_go_L1_session_2`).

## What this session lands

1. `exists_label_not_in_trace_image_of_card_lt` — the parameter-agnostic
   finite-image pigeonhole step: any sub-family `S ⊆ (α → Bool)` of
   cardinality strictly below `2 ^ |α|` misses some Boolean labeling.
   This is the generic replacement for the canonical L1 session 1
   pigeonhole `exists_trace_not_size1_of_card_lt`.

2. `slack_for_D_of_isoStrong_slack_general` — converts iso-strong
   slack on the `(tableLen, κ)` axis into the `D.card` form needed by
   the diagonal step, by composing `F.hIndex` / `F.hM` / `F.hT` to
   line up `F.Mof n (F.Tof n β)` with
   `circuitCountBound (F.paramsOf n β).n ((F.paramsOf n β).sNO - 1)`,
   then weakening the exponent via `Nat.sub_le_sub_left` and
   `Nat.pow_le_pow_right`.  This is the generic replacement for the
   canonical L1 session 4 `slack_for_D_of_isoStrong_slack`.

## What remains for L1 session 2

- A general not-YES bridge `exists_valid_agreeing_not_yes_under_general_slack`
  replacing the canonical size-1 `is_consistent_diagonal_table_implies_label_trace`
  consistency lemma.
- Final assembly into `isoStrong_conclusion_negative_general` over an
  arbitrary `GapSliceFamilyEventually`.
-/

namespace Pnp3
namespace Tests
namespace GeneralIsoStrongNoGoProbe

open Models
open LowerBounds

/--
Finite-image pigeonhole: any `S : Finset (α → Bool)` of cardinality strictly
below `2 ^ |α|` misses some Boolean labeling `label : α → Bool`.

Parameter-agnostic replacement for the canonical
`exists_trace_not_size1_of_card_lt` (L1 session 1) — operates on an
arbitrary finite trace image, not specifically the size-1 candidate
trace family.
-/
theorem exists_label_not_in_trace_image_of_card_lt
    {α : Type} [Fintype α] [DecidableEq (α → Bool)]
    (S : Finset (α → Bool))
    (h : S.card < 2 ^ Fintype.card α) :
    ∃ label : α → Bool, label ∉ S := by
  classical
  have hCardU : (Finset.univ : Finset (α → Bool)).card = 2 ^ Fintype.card α := by
    simp [Fintype.card_bool]
  have hLt : S.card < (Finset.univ : Finset (α → Bool)).card := by
    simpa [hCardU] using h
  by_contra hNo
  have hAll : ∀ label : α → Bool, label ∈ S := by
    intro label
    by_contra hNotMem
    exact hNo ⟨label, hNotMem⟩
  have hEq : S = (Finset.univ : Finset (α → Bool)) := by
    ext label
    constructor
    · intro _; simp
    · intro _; exact hAll label
  have hNotLt : ¬ S.card < (Finset.univ : Finset (α → Bool)).card := by
    simp [hEq]
  exact hNotLt hLt

/--
Convert iso-strong slack from the `(tableLen, κ)` axis to the `D.card`
form needed by the diagonal step at a general
`GapSliceFamilyEventually`.

Composition:
- `F.hIndex` aligns `(F.paramsOf n β).n` with `n` for `n ≥ F.N0`;
- `F.hM` rewrites `F.Mof n T` to `circuitCountBound n T`;
- `F.hT` rewrites `F.Tof n β` to `(F.paramsOf n β).sNO - 1`;
- monotonicity of `Nat.sub` and `Nat.pow` weakens the `κv` exponent
  to the `D.card` exponent via `D.card ≤ κv`.

Parameter-agnostic replacement for the canonical L1 session 4
`slack_for_D_of_isoStrong_slack`.
-/
theorem slack_for_D_of_isoStrong_slack_general
    (F : GapSliceFamilyEventually)
    (n : Nat) (β : Rat)
    (hn : F.N0 ≤ n)
    (D : Finset (Fin (GapSliceFamilyEventually.tableLen F n β)))
    (κv : Nat)
    (hDcard : D.card ≤ κv)
    (hRawSlack :
      F.Mof n (F.Tof n β) <
        2 ^ (GapSliceFamilyEventually.tableLen F n β - κv)) :
    circuitCountBound (F.paramsOf n β).n ((F.paramsOf n β).sNO - 1) <
      2 ^ (Partial.tableLen (F.paramsOf n β).n - D.card) := by
  have hRaw' :
      circuitCountBound (F.paramsOf n β).n ((F.paramsOf n β).sNO - 1)
        < 2 ^ (GapSliceFamilyEventually.tableLen F n β - κv) := by
    have hIdx : (F.paramsOf n β).n = n := F.hIndex n hn β
    have hM := F.hM n hn ((F.paramsOf n β).sNO - 1)
    have hT := F.hT n hn β
    simpa [hIdx, hM, hT] using hRawSlack
  have hExpLe : GapSliceFamilyEventually.tableLen F n β - κv ≤
      GapSliceFamilyEventually.tableLen F n β - D.card :=
    Nat.sub_le_sub_left hDcard _
  have hPowLe : 2 ^ (GapSliceFamilyEventually.tableLen F n β - κv) ≤
      2 ^ (GapSliceFamilyEventually.tableLen F n β - D.card) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hExpLe
  have hLt' := lt_of_lt_of_le hRaw' hPowLe
  simpa [GapSliceFamilyEventually.tableLen] using hLt'

end GeneralIsoStrongNoGoProbe
end Tests
end Pnp3
