import Models.Model_PartialMCSP
import LowerBounds.AsymptoticDAGBarrierTheorems
import LowerBounds.AsymptoticDAGBarrierInterfaces
import LowerBounds.MCSPGapLocality
import Tests.CircuitCountTraceBoundProbe

namespace Pnp3
namespace Tests
namespace GeneralIsoStrongNoGoProbe

open Models
open LowerBounds

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
  have : ¬ S.card < (Finset.univ : Finset (α → Bool)).card := by
    simpa [hEq]
  exact this hLt

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
