import Pnp4.Frontier.ContractExpansion.TreeMCSPCorridorInputStep

/-!
# The settle-decrement keystone — D2t-5b (Block A4b): `DriveState.step`'s decrement branch on tape

The settling arm with a top frame `(tag, rem)`, `rem ≥ 2`, decrements: `⟨toks, out, (tag, rem) ::
ctrl', val, true⟩ → ⟨toks, out, (tag, rem − 1) :: ctrl', val, false⟩`.  On tape this is a **single
bounded rewrite of the top-frame region**: the old frame (rightmost, at `fb = ctrlBase +
|encodeCtrlStackR ctrl'|`) is overwritten by the decremented frame, and the one leftover cell (the
new frame is one shorter) is zeroed — both effected by one `writeBlockTape` whose block is the new
frame padded with a trailing `false` (`getD` past the block's end is `false` automatically).

`corridorInv_decStep` re-establishes `driverCorridorInv` for the stepped state: the control window is
the codec cons with the decremented frame; the corridor right of the (shrunk) content absorbs the
leftover zero; every other region is untouched.

**Progress classification (AGENTS.md): Infrastructure** — a tape-level invariant-preservation
keystone over the verified codecs; builds no machine and proves no separation.  Standard `[propext,
Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- Frame lengths: the decremented frame is exactly one cell shorter. -/
theorem encodeCtrlFrameR_dec_length (tag : ITag) (rem : Nat) (hrem : 2 ≤ rem) :
    (encodeCtrlFrameR (tag, rem - 1)).length + 1 = (encodeCtrlFrameR (tag, rem)).length := by
  rw [encodeCtrlFrameR_length, encodeCtrlFrameR_length]
  omega

/-- **The settle-decrement keystone.**  For a settling state with top frame `(tag, rem)`, `rem ≥ 2`,
overwriting the top-frame region with the decremented frame (plus the one-cell zero pad) yields the
invariant for the stepped state `⟨toks, out, (tag, rem − 1) :: ctrl', val, false⟩`. -/
theorem corridorInv_decStep {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (tag : ITag) (rem : Nat) (hrem : 2 ≤ rem)
    (toks : List (PreToken n)) (out : List (SLGate n)) (ctrl' : List (ITag × Nat))
    (val : List Nat) (tape : Fin L → Bool)
    (hinv : driverCorridorInv width h_width z tape
      (⟨toks, out, (tag, rem) :: ctrl', val, true⟩ : DriveState n)) :
    driverCorridorInv width h_width z
      (writeBlockTape tape (z.ctrlBase + (encodeCtrlStackR ctrl').length)
        (encodeCtrlFrameR (tag, rem - 1) ++ [false]))
      (⟨toks, out, (tag, rem - 1) :: ctrl', val, false⟩ : DriveState n) := by
  obtain ⟨hwf, hcert, hcfit, hmark, hcorr, hout, hofit, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hctrl, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hwf
  replace hcert : windowSpells tape
      (z.certEnd - (encodePreorder width h_width toks).length)
      (encodePreorder width h_width toks) := hcert
  replace hcfit : z.certBase + (encodePreorder width h_width toks).length ≤ z.certEnd := hcfit
  replace hmark : ∀ p : Fin L,
      (p : Nat) = z.certEnd - (encodePreorder width h_width toks).length - 1 →
      tape p = true := hmark
  replace hcorr : ∀ p : Fin L,
      z.ctrlBase + (encodeCtrlStackR ((tag, rem) :: ctrl')).length ≤ (p : Nat) →
      (p : Nat) < z.certEnd - (encodePreorder width h_width toks).length - 1 →
      tape p = false := hcorr
  replace hout : windowSpells tape (z.workBase - 1 - out.length)
      (unaryField out.length ++ encodeGateRecordStream out) := hout
  replace hofit : z.outBase + out.length + 1 ≤ z.workBase := hofit
  replace hFM : ∀ p : Fin L,
      (p : Nat) = z.workBase + (encodeGateRecordStream out).length → tape p = true := hFM
  replace hffit : z.workBase + (encodeGateRecordStream out).length + 1 ≤ z.workEnd := hffit
  replace hfzeros : ∀ p : Fin L,
      z.workBase + (encodeGateRecordStream out).length + 1 ≤ (p : Nat) →
      (p : Nat) < z.valBase → tape p = false := hfzeros
  replace hval : windowSpells tape z.valBase (encodeNatStackR val) := hval
  replace hvfit : z.valBase + (encodeNatStackR val).length ≤ z.valEnd := hvfit
  replace hvzeros : ∀ p : Fin L, z.valBase + (encodeNatStackR val).length ≤ (p : Nat) →
      (p : Nat) < z.ctrlBase → tape p = false := hvzeros
  replace hctrl : windowSpells tape z.ctrlBase (encodeCtrlStackR ((tag, rem) :: ctrl')) := hctrl
  replace hcfit2 : z.ctrlBase + (encodeCtrlStackR ((tag, rem) :: ctrl')).length
      ≤ z.ctrlEnd := hcfit2
  replace hvalid : ValidCertTokens toks := hvalid
  replace hcoh : True → val ≠ [] := fun _ => hcoh rfl
  -- Lengths and the rewrite block.
  have holdlen : (encodeCtrlStackR ((tag, rem) :: ctrl')).length
      = (encodeCtrlStackR ctrl').length + (encodeCtrlFrameR (tag, rem)).length := by
    rw [encodeCtrlStackR_cons, List.length_append]
  have hnewlen : (encodeCtrlStackR ((tag, rem - 1) :: ctrl')).length
      = (encodeCtrlStackR ctrl').length + (encodeCtrlFrameR (tag, rem - 1)).length := by
    rw [encodeCtrlStackR_cons, List.length_append]
  have hdec := encodeCtrlFrameR_dec_length tag rem hrem
  have hblocklen : (encodeCtrlFrameR (tag, rem - 1) ++ [false]).length
      = (encodeCtrlFrameR (tag, rem)).length := by
    rw [List.length_append, List.length_singleton]; omega
  -- The rewrite zone [fb, fb + |old frame|) lies inside [ctrlBase, ctrl-old-end] ⊆ [ctrlBase, ctrlEnd].
  have hzone : z.ctrlBase + (encodeCtrlStackR ctrl').length
      + (encodeCtrlFrameR (tag, rem - 1) ++ [false]).length ≤ z.ctrlEnd := by
    rw [hblocklen]; omega
  -- Off-zone transport: the rewrite touches only [fb, fb + |old frame|).
  have hoff_below : ∀ q : Fin L, (q : Nat) < z.ctrlBase + (encodeCtrlStackR ctrl').length →
      writeBlockTape tape (z.ctrlBase + (encodeCtrlStackR ctrl').length)
        (encodeCtrlFrameR (tag, rem - 1) ++ [false]) q = tape q :=
    fun q hq => writeBlockTape_below tape _ _ q hq
  have hoff_above : ∀ q : Fin L,
      z.ctrlBase + (encodeCtrlStackR ((tag, rem) :: ctrl')).length ≤ (q : Nat) →
      writeBlockTape tape (z.ctrlBase + (encodeCtrlStackR ctrl').length)
        (encodeCtrlFrameR (tag, rem - 1) ++ [false]) q = tape q := by
    intro q hq
    apply writeBlockTape_above
    rw [hblocklen]; omega
  dsimp only [driverCorridorInv]
  refine ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  -- 1. cert suffix (untouched: cert region right of ctrlEnd).
  · refine windowSpells_congr _ _ _ _ hcert (fun q hlo hhi => ?_)
    exact hoff_above q (by omega)
  -- 2. cert fit.
  · exact hcfit
  -- 3. marker (untouched).
  · intro p hp
    rw [hoff_above p (by omega)]
    exact hmark p hp
  -- 4. consumed/dead corridor: old corridor + the leftover zero cell.
  · intro p hlo hhi
    rw [hnewlen] at hlo
    by_cases hzero : (p : Nat) < z.ctrlBase + (encodeCtrlStackR ((tag, rem) :: ctrl')).length
    · -- p is the leftover pad cell inside the rewrite zone: the block's getD there is false.
      unfold writeBlockTape
      rw [if_pos ⟨by omega, by rw [hblocklen]; omega⟩]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      have : (p : Nat) - (z.ctrlBase + (encodeCtrlStackR ctrl').length)
          - (encodeCtrlFrameR (tag, rem - 1)).length = 0 := by omega
      rw [this]
      rfl
    · rw [hoff_above p (by omega)]
      exact hcorr p (by omega) hhi
  -- 5. output window (untouched).
  · refine windowSpells_congr _ _ _ _ hout (fun q hlo hhi => ?_)
    apply hoff_below
    rw [List.length_append, unaryField_length] at hhi
    omega
  -- 6. output left fit.
  · exact hofit
  -- 7. frontier marker (untouched).
  · intro p hp
    rw [hoff_below p (by omega)]
    exact hFM p hp
  -- 8. frontier fit.
  · exact hffit
  -- 9. FM→val corridor (untouched).
  · intro p hlo hhi
    rw [hoff_below p (by omega)]
    exact hfzeros p hlo hhi
  -- 10. value window (untouched).
  · refine windowSpells_congr _ _ _ _ hval (fun q hlo hhi => ?_)
    apply hoff_below
    have := hvfit
    omega
  -- 11. value fit.
  · exact hvfit
  -- 12. val→ctrl corridor (untouched).
  · intro p hlo hhi
    rw [hoff_below p (by omega)]
    exact hvzeros p hlo hhi
  -- 13. control window: the prefix is untouched; the frame cells come from the written block.
  · rw [encodeCtrlStackR_cons]
    have hpre := windowSpells_append_left tape z.ctrlBase _ _
      (by rw [← encodeCtrlStackR_cons]; exact hctrl)
    refine ⟨by
      rw [List.length_append]
      have := hctrl.1
      rw [holdlen] at this
      omega, fun q hlo hhi => ?_⟩
    rw [List.length_append] at hhi
    by_cases hq : (q : Nat) < z.ctrlBase + (encodeCtrlStackR ctrl').length
    · -- old prefix, untouched
      rw [hoff_below q hq, List.getD_append _ _ _ _ (by omega)]
      exact hpre.2 q hlo (by omega)
    · -- the new frame's cells: from the written block
      unfold writeBlockTape
      rw [if_pos ⟨by omega, by rw [hblocklen]; omega⟩,
        List.getD_append_right (encodeCtrlStackR ctrl') _ _ _ (by omega),
        List.getD_append _ _ _ _ (by omega)]
      congr 1
      omega
  -- 14. control fit.
  · rw [hnewlen]
    omega
  -- 15. validity.
  · exact hvalid
  -- 16. settling coherence (now reading).
  · intro hs; cases hs

end ContractExpansion
end Frontier
end Pnp4
