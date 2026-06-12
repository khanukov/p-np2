import Pnp4.Frontier.ContractExpansion.TreeMCSPCorridorConstStep

/-!
# The input-leaf keystone — D2t-5b (Block A4a, part 2): `DriveState.step`'s `input` branch on tape

The `input i` arm is the `const` arm with a `(3 + width)`-cell token (tag `[0,0,0]` plus the binary
index `encodeFin width i`) and the record `unaryField 0 ++ unaryField i.val`.  This module
generalises the composed transformer over the **token length** (`leafStepTape … tlen …`, off-factory
re-proven verbatim) and instantiates the keystone: `corridorInv_inputStep` re-establishes
`driverCorridorInv` for the stepped state `⟨toks', out ++ [input i], ctrl, out.length :: val, true⟩`.

**Progress classification (AGENTS.md): Infrastructure** — a tape-level invariant-preservation
keystone over the verified codecs; builds no machine and proves no separation.  Standard `[propext,
Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- The leaf-arm tape transformer, generic over the consumed token's length `tlen`: value push
(inner), output emit (middle), cursor-marker update (outer). -/
def leafStepTape {L : Nat} (tape : Fin L → Bool) (cur tlen vtop fm : Nat)
    (ventry rec : List Bool) : Fin L → Bool :=
  cursorStepTape (emitTape (writeBlockTape tape vtop ventry) fm rec) cur tlen

/-- Off all three regions, `leafStepTape` is the identity. -/
theorem leafStepTape_eq_id {L : Nat} (tape : Fin L → Bool) (cur tlen vtop fm : Nat)
    (ventry rec : List Bool) (q : Fin L)
    (hc1 : (q : Nat) ≠ cur + tlen - 1)
    (hc2 : ¬ (cur - 1 ≤ (q : Nat) ∧ (q : Nat) < cur + tlen - 1))
    (he2 : ¬ (fm ≤ (q : Nat) ∧ (q : Nat) < fm + rec.length))
    (he3 : (q : Nat) ≠ fm + rec.length)
    (hw : ¬ (vtop ≤ (q : Nat) ∧ (q : Nat) < vtop + ventry.length)) :
    leafStepTape tape cur tlen vtop fm ventry rec q = tape q := by
  unfold leafStepTape
  rw [cursorStepTape_off _ _ _ q hc1 hc2, emitTape_off _ _ _ q he2 he3]
  unfold writeBlockTape
  rw [if_neg hw]

/-- On the cursor area, `leafStepTape` is `cursorStepTape` of the original tape. -/
theorem leafStepTape_eq_cursor {L : Nat} (tape : Fin L → Bool) (cur tlen vtop fm : Nat)
    (ventry rec : List Bool) (q : Fin L)
    (he2 : ¬ (fm ≤ (q : Nat) ∧ (q : Nat) < fm + rec.length))
    (he3 : (q : Nat) ≠ fm + rec.length)
    (hw : ¬ (vtop ≤ (q : Nat) ∧ (q : Nat) < vtop + ventry.length)) :
    leafStepTape tape cur tlen vtop fm ventry rec q = cursorStepTape tape cur tlen q := by
  unfold leafStepTape cursorStepTape
  by_cases hq1 : (q : Nat) = cur + tlen - 1
  · rw [if_pos hq1, if_pos hq1]
  · rw [if_neg hq1, if_neg hq1]
    by_cases hq2 : cur - 1 ≤ (q : Nat) ∧ (q : Nat) < cur + tlen - 1
    · rw [if_pos hq2, if_pos hq2]
    · rw [if_neg hq2, if_neg hq2, emitTape_off _ _ _ q he2 he3]
      unfold writeBlockTape
      rw [if_neg hw]

/-- On the output region, `leafStepTape` is `emitTape` of the original tape. -/
theorem leafStepTape_eq_emit {L : Nat} (tape : Fin L → Bool) (cur tlen vtop fm : Nat)
    (ventry rec : List Bool) (q : Fin L)
    (hc1 : (q : Nat) ≠ cur + tlen - 1)
    (hc2 : ¬ (cur - 1 ≤ (q : Nat) ∧ (q : Nat) < cur + tlen - 1))
    (hw : ¬ (vtop ≤ (q : Nat) ∧ (q : Nat) < vtop + ventry.length)) :
    leafStepTape tape cur tlen vtop fm ventry rec q = emitTape tape fm rec q := by
  unfold leafStepTape
  rw [cursorStepTape_off _ _ _ q hc1 hc2]
  unfold emitTape
  by_cases hq2 : fm ≤ (q : Nat) ∧ (q : Nat) < fm + rec.length
  · rw [if_pos hq2, if_pos hq2]
  · rw [if_neg hq2, if_neg hq2]
    by_cases hq3 : (q : Nat) = fm + rec.length
    · rw [if_pos hq3, if_pos hq3]
    · rw [if_neg hq3, if_neg hq3]
      unfold writeBlockTape
      rw [if_neg hw]

/-- On the value block, `leafStepTape` is `writeBlockTape` of the original tape. -/
theorem leafStepTape_eq_write {L : Nat} (tape : Fin L → Bool) (cur tlen vtop fm : Nat)
    (ventry rec : List Bool) (q : Fin L)
    (hc1 : (q : Nat) ≠ cur + tlen - 1)
    (hc2 : ¬ (cur - 1 ≤ (q : Nat) ∧ (q : Nat) < cur + tlen - 1))
    (he2 : ¬ (fm ≤ (q : Nat) ∧ (q : Nat) < fm + rec.length))
    (he3 : (q : Nat) ≠ fm + rec.length) :
    leafStepTape tape cur tlen vtop fm ventry rec q = writeBlockTape tape vtop ventry q := by
  unfold leafStepTape
  rw [cursorStepTape_off _ _ _ q hc1 hc2, emitTape_off _ _ _ q he2 he3]

/-- **The input-leaf keystone.**  For a reading state whose next token is `leaf (input i)` (tail
nonempty), with output, value-zone and shadow-count capacity, `leafStepTape` (token length
`3 + width`) followed by the **shadow-count tick** re-establishes `driverCorridorInv` for the
stepped state. -/
theorem corridorInv_inputStep {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (i : Fin n) (toks' : List (PreToken n)) (out : List (SLGate n))
    (ctrl : List (ITag × Nat)) (val : List Nat) (tape : Fin L → Bool)
    (hinv : driverCorridorInv width h_width z tape
      (⟨PreToken.leaf (SLGate.input i) :: toks', out, ctrl, val, false⟩ : DriveState n))
    (htoks : toks' ≠ [])
    (hwcap : z.workBase + (encodeGateRecordStream out).length
        + (encodeGateRecord (SLGate.input i : SLGate n)).length + 1 ≤ z.workEnd)
    (hvcap : z.valBase + (encodeNatStackR val).length + (out.length + 3) ≤ z.valEnd)
    (hscap : z.shwBase + out.length + 2 ≤ z.shwEnd) :
    driverCorridorInv width h_width z
      (writeBlockTape
        (leafStepTape tape
          (z.certEnd - (encodePreorder width h_width
            (PreToken.leaf (SLGate.input i) :: toks')).length)
          (3 + width)
          (z.valBase + (encodeNatStackR val).length)
          (z.workBase + (encodeGateRecordStream out).length)
          (encodeNatEntryR out.length)
          (encodeGateRecord (SLGate.input i : SLGate n)))
        (z.shwBase + out.length + 1) [true])
      (⟨toks', out ++ [SLGate.input i], ctrl, out.length :: val, true⟩ : DriveState n) := by
  obtain ⟨hwf, hcert, hcfit, hmark, hcorr, hout, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrl, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwf
  replace hcert : windowSpells tape
      (z.certEnd - (encodePreorder width h_width (PreToken.leaf (SLGate.input i) :: toks')).length)
      (encodePreorder width h_width (PreToken.leaf (SLGate.input i) :: toks')) := hcert
  replace hcfit : z.certBase
      + (encodePreorder width h_width (PreToken.leaf (SLGate.input i) :: toks')).length
        ≤ z.certEnd := hcfit
  replace hcorr : ∀ p : Fin L, z.ctrlBase + (encodeCtrlStackR ctrl).length ≤ (p : Nat) →
      (p : Nat) < z.certEnd
        - (encodePreorder width h_width (PreToken.leaf (SLGate.input i) :: toks')).length - 1 →
      tape p = false := hcorr
  replace hout : windowSpells tape (z.workBase - 1 - z.outCount)
      (unaryField z.outCount ++ encodeGateRecordStream out) := hout
  replace hffit : z.workBase + (encodeGateRecordStream out).length + 1 ≤ z.workEnd := hffit
  replace hfzeros : ∀ p : Fin L,
      z.workBase + (encodeGateRecordStream out).length + 1 ≤ (p : Nat) →
      (p : Nat) < z.valBase → tape p = false := hfzeros
  replace hval : windowSpells tape z.valBase (encodeNatStackR val) := hval
  replace hvfit : z.valBase + (encodeNatStackR val).length ≤ z.valEnd := hvfit
  replace hvzeros : ∀ p : Fin L, z.valBase + (encodeNatStackR val).length ≤ (p : Nat) →
      (p : Nat) < z.shwBase → tape p = false := hvzeros
  replace hshw : windowSpells tape z.shwBase (List.replicate (out.length + 1) true) := hshw
  replace hsfit : z.shwBase + out.length + 1 ≤ z.shwEnd := hsfit
  replace hszeros : ∀ p : Fin L, z.shwBase + out.length + 1 ≤ (p : Nat) →
      (p : Nat) < z.ctrlBase → tape p = false := hszeros
  replace hctrl : windowSpells tape z.ctrlBase (encodeCtrlStackR ctrl) := hctrl
  replace hcfit2 : z.ctrlBase + (encodeCtrlStackR ctrl).length ≤ z.ctrlEnd := hcfit2
  replace hvalid : ValidCertTokens (PreToken.leaf (SLGate.input i) :: toks') := hvalid
  -- Length facts.
  have hreclen : (encodeGateRecord (SLGate.input i : SLGate n)).length = i.val + 2 := by
    show (unaryField 0 ++ unaryField i.val).length = i.val + 2
    rw [List.length_append, unaryField_length, unaryField_length]
    omega
  have hventrylen : (encodeNatEntryR out.length).length = out.length + 3 :=
    encodeNatEntryR_length out.length
  have htagW : (encodePreToken width h_width (PreToken.leaf (SLGate.input i))).length
      = 3 + width := by
    show ([false, false, false]
      ++ encodeFin width ⟨i.val, lt_of_lt_of_le i.isLt h_width⟩).length = 3 + width
    rw [List.length_append, encodeFin_length]
    rfl
  have htail1 : 1 ≤ (encodePreorder width h_width toks').length := by
    have hv : ValidCertTokens toks' := fun t ht => hvalid t (List.mem_cons_of_mem _ ht)
    have := validCertTokens_length_le width h_width hv
    have : 1 ≤ toks'.length := by cases toks' with
      | nil => exact absurd rfl htoks
      | cons a l => simp only [List.length_cons]; omega
    omega
  have hlenc : (encodePreorder width h_width (PreToken.leaf (SLGate.input i) :: toks')).length
      = (3 + width) + (encodePreorder width h_width toks').length := by
    rw [encodePreorder_cons, List.length_append, htagW]
  have hrecstream := encodeGateRecordStream_snoc out (SLGate.input i : SLGate n)
  have hlen1 : (out ++ [(SLGate.input i : SLGate n)]).length = out.length + 1 := by simp
  have hstreamlen : (encodeGateRecordStream (out ++ [(SLGate.input i : SLGate n)])).length
      = (encodeGateRecordStream out).length + (i.val + 2) := by
    rw [hrecstream, List.length_append, hreclen]
  have hsepcur : z.ctrlEnd + 2 < z.certEnd
      - (encodePreorder width h_width (PreToken.leaf (SLGate.input i) :: toks')).length := by
    omega
  have hreccap : z.workBase + (encodeGateRecordStream out).length + (i.val + 2) + 1
      ≤ z.workEnd := by
    rw [hreclen] at hwcap; omega
  -- The shadow-count tick peels: below / above the single written cell.
  have htickB : ∀ (T : Fin L → Bool) (q : Fin L), (q : Nat) < z.shwBase + out.length + 1 →
      writeBlockTape T (z.shwBase + out.length + 1) [true] q = T q :=
    fun T q hq => writeBlockTape_below T _ _ q hq
  have htickA : ∀ (T : Fin L → Bool) (q : Fin L), z.shwBase + out.length + 2 ≤ (q : Nat) →
      writeBlockTape T (z.shwBase + out.length + 1) [true] q = T q := by
    intro T q hq
    apply writeBlockTape_above
    simp only [List.length_singleton]
    omega
  dsimp only [driverCorridorInv]
  refine ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- 1. cert suffix window.
  · obtain ⟨hc1, _, _, _⟩ := cursorStepTape_cert width h_width tape z.certEnd
      (z.ctrlBase + (encodeCtrlStackR ctrl).length) (3 + width) (PreToken.leaf (SLGate.input i))
      toks' htagW (by omega) (by omega) hcert (by omega) hcorr
    rw [show z.certEnd - (encodePreorder width h_width toks').length
        = z.certEnd - (encodePreorder width h_width
            (PreToken.leaf (SLGate.input i) :: toks')).length + (3 + width) from by omega]
    refine windowSpells_congr _ _ _ _ hc1 (fun q hlo hhi => ?_)
    rw [htickA _ q (by omega),
      leafStepTape_eq_cursor tape _ _ _ _ _ _ q
      (by rw [hreclen]; omega) (by rw [hreclen]; omega)
      (by rw [hventrylen]; omega)]
  -- 2. cert fit.
  · omega
  -- 3. new marker.
  · intro p hp
    rw [show (z.certEnd - (encodePreorder width h_width toks').length) - 1
        = z.certEnd - (encodePreorder width h_width
            (PreToken.leaf (SLGate.input i) :: toks')).length + (3 + width) - 1 from by omega] at hp
    rw [htickA _ p (by omega),
      leafStepTape_eq_cursor tape _ _ _ _ _ _ p
      (by rw [hreclen]; omega) (by rw [hreclen]; omega)
      (by rw [hventrylen]; omega)]
    unfold cursorStepTape
    rw [if_pos hp]
  -- 4. consumed/dead corridor.
  · intro p hlo hhi
    rw [show (z.certEnd - (encodePreorder width h_width toks').length) - 1
        = z.certEnd - (encodePreorder width h_width
            (PreToken.leaf (SLGate.input i) :: toks')).length + (3 + width) - 1 from by omega]
      at hhi
    rw [htickA _ p (by omega),
      leafStepTape_eq_cursor tape _ _ _ _ _ _ p
      (by rw [hreclen]; omega) (by rw [hreclen]; omega)
      (by rw [hventrylen]; omega)]
    unfold cursorStepTape
    rw [if_neg (by omega)]
    by_cases hband : z.certEnd - (encodePreorder width h_width
        (PreToken.leaf (SLGate.input i) :: toks')).length - 1 ≤ (p : Nat)
      ∧ (p : Nat) < z.certEnd - (encodePreorder width h_width
        (PreToken.leaf (SLGate.input i) :: toks')).length + (3 + width) - 1
    · rw [if_pos hband]
    · rw [if_neg hband]
      exact hcorr p hlo (by omega)
  -- 5. output window (the static prefix + the appended record).
  · have hemit := emitTape_output_window tape (z.workBase - 1 - z.outCount) z.outCount out
      (SLGate.input i : SLGate n) hout
      (by
        rw [List.length_append, unaryField_length, hreclen]
        have := hval.1
        omega)
    have hocfm : z.workBase - 1 - z.outCount
        + (unaryField z.outCount ++ encodeGateRecordStream out).length
        = z.workBase + (encodeGateRecordStream out).length := by
      rw [List.length_append, unaryField_length]; omega
    rw [hocfm] at hemit
    refine windowSpells_congr _ _ _ _ hemit (fun q hlo hhi => ?_)
    rw [htickB _ q (by rw [List.length_append, unaryField_length, hstreamlen] at hhi; omega),
      leafStepTape_eq_emit tape _ _ _ _ _ _ q
      (by rw [List.length_append, unaryField_length, hstreamlen] at hhi; omega)
      (by rw [List.length_append, unaryField_length, hstreamlen] at hhi; omega)
      (by rw [List.length_append, unaryField_length, hstreamlen] at hhi
          rw [hventrylen]; omega)]
  -- 6. new frontier marker.
  · intro p hp
    rw [hstreamlen] at hp
    rw [htickB _ p (by omega),
      leafStepTape_eq_emit tape _ _ _ _ _ _ p
      (by omega) (by omega) (by rw [hventrylen]; omega)]
    exact emitTape_FM tape _ _ p (by rw [hreclen]; omega)
  -- 7. frontier fit.
  · rw [hstreamlen]
    omega
  -- 9. FM→val dead corridor.
  · intro p hlo hhi
    rw [hstreamlen] at hlo
    rw [htickB _ p (by omega),
      leafStepTape_eq_id tape _ _ _ _ _ _ p
      (by omega) (by omega) (by rw [hreclen]; omega) (by rw [hreclen]; omega)
      (by rw [hventrylen]; omega)]
    exact hfzeros p (by omega) hhi
  -- 10. value window.
  · have hvw := valPush_window tape z.valBase out.length val hval
      (by rw [encodeNatEntryR_length]; omega)
    refine windowSpells_congr _ _ _ _ hvw (fun q hlo hhi => ?_)
    rw [encodeNatStackR_cons, List.length_append, encodeNatEntryR_length] at hhi
    rw [htickB _ q (by omega),
      leafStepTape_eq_write tape _ _ _ _ _ _ q
      (by omega) (by omega) (by rw [hreclen]; omega) (by rw [hreclen]; omega)]
  -- 11. value fit.
  · rw [encodeNatStackR_cons, List.length_append, encodeNatEntryR_length]
    omega
  -- 12. val→SHW dead corridor.
  · intro p hlo hhi
    rw [encodeNatStackR_cons, List.length_append, encodeNatEntryR_length] at hlo
    rw [htickB _ p (by omega),
      leafStepTape_eq_id tape _ _ _ _ _ _ p
      (by omega) (by omega) (by rw [hreclen]; omega) (by rw [hreclen]; omega)
      (by rw [hventrylen]; omega)]
    exact hvzeros p (by omega) hhi
  -- 12a. SHW window: the tick appends one `1` to the spelled `1`-block.
  · rw [hlen1, show List.replicate (out.length + 1 + 1) true
        = List.replicate (out.length + 1) true ++ [true] from List.replicate_succ' ..]
    have hshw' : windowSpells
        (leafStepTape tape
          (z.certEnd - (encodePreorder width h_width
            (PreToken.leaf (SLGate.input i) :: toks')).length)
          (3 + width)
          (z.valBase + (encodeNatStackR val).length)
          (z.workBase + (encodeGateRecordStream out).length)
          (encodeNatEntryR out.length)
          (encodeGateRecord (SLGate.input i : SLGate n)))
        z.shwBase (List.replicate (out.length + 1) true) := by
      refine windowSpells_congr _ _ _ _ hshw (fun q hlo hhi => ?_)
      rw [List.length_replicate] at hhi
      rw [leafStepTape_eq_id tape _ _ _ _ _ _ q
        (by omega) (by omega) (by rw [hreclen]; omega) (by rw [hreclen]; omega)
        (by rw [hventrylen]; omega)]
    have happ := windowSpells_writeAppend _ z.shwBase (List.replicate (out.length + 1) true)
      [true] hshw' (by rw [List.length_replicate, List.length_singleton]; omega)
    rw [List.length_replicate,
      show z.shwBase + (out.length + 1) = z.shwBase + out.length + 1 from by omega] at happ
    exact happ
  -- 12b. SHW fit (one tick of room).
  · rw [hlen1]
    omega
  -- 12c. SHW→ctrl dead corridor (right of the ticked cell).
  · intro p hlo hhi
    rw [hlen1] at hlo
    rw [htickA _ p (by omega),
      leafStepTape_eq_id tape _ _ _ _ _ _ p
      (by omega) (by omega) (by rw [hreclen]; omega) (by rw [hreclen]; omega)
      (by rw [hventrylen]; omega)]
    exact hszeros p (by omega) hhi
  -- 13. control window (untouched).
  · refine windowSpells_congr _ _ _ _ hctrl (fun q hlo hhi => ?_)
    have hq : (q : Nat) < z.ctrlEnd := by have := hctrl.1; omega
    rw [htickA _ q (by omega),
      leafStepTape_eq_id tape _ _ _ _ _ _ q
      (by omega) (by omega) (by rw [hreclen]; omega) (by rw [hreclen]; omega)
      (by rw [hventrylen]; omega)]
  -- 14. control fit.
  · exact hcfit2
  -- 15. validity.
  · exact fun t ht => hvalid t (List.mem_cons_of_mem _ ht)
  -- 16. settling coherence.
  · intro _; exact List.cons_ne_nil _ _

end ContractExpansion
end Frontier
end Pnp4
