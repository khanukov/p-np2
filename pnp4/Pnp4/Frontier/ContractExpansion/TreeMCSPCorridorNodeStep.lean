import Pnp4.Frontier.ContractExpansion.TreeMCSPCorridorDispatch

/-!
# The node-arm keystone — D2t-5b (Block A4a): the invariant is re-established

The node arm's six machine legs (dispatch ▸ step-left ▸ erase/replant ▸ scan ▸ step-right ▸ frame
push ▸ scan-back) change the tape in exactly two places: the **cursor area** (the consumed token's
three tag cells and the old marker are zeroed, the new marker is planted on the last consumed cell)
and the **control zone's right end** (the pushed frame).  `nodeStepTape` is that explicit
transformer; this module proves the **keystone**: applying it to a tape satisfying
`driverCorridorInv` for a reading state with next token `node tag` yields a tape satisfying
`driverCorridorInv` for the **stepped** abstract state `⟨toks', out, (tag, arity) :: ctrl, val,
false⟩` — i.e. the on-tape node arm realises `DriveState.step`'s node branch, invariant preserved.
(The machine-assembly layer then only has to show the composite's final tape *equals*
`nodeStepTape`, leg by leg — each leg's run lemma already gives its exact tape map.)

**Progress classification (AGENTS.md): Infrastructure** — a tape-level invariant-preservation
keystone, proven against the verified codecs; builds no machine and proves no separation.  Standard
`[propext, Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- The node arm's tape transformer: plant the new marker on the token's last tag cell
(`cursor + 2`), zero the cells `[cursor − 1, cursor + 2)` (the old marker and the first two tag
cells), and write the frame at the control zone's right end (`[fbase, fbase + |frame|)`). -/
def nodeStepTape {L : Nat} (tape : Fin L → Bool) (cursor fbase : Nat) (frame : List Bool)
    (q : Fin L) : Bool :=
  if (q : Nat) = cursor + 2 then true
  else if cursor - 1 ≤ (q : Nat) ∧ (q : Nat) < cursor + 2 then false
  else if fbase ≤ (q : Nat) ∧ (q : Nat) < fbase + frame.length then
    frame.getD ((q : Nat) - fbase) false
  else tape q

/-- **The node-arm keystone.**  For a reading state with next token `node tag` (tail nonempty — the
node's child follows) and room for the frame in the control zone, the transformed tape satisfies the
invariant for the stepped state `⟨toks', out, (tag, tag.arity) :: ctrl, val, false⟩`. -/
theorem corridorInv_nodeStep {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (tag : ITag) (toks' : List (PreToken n)) (out : List (SLGate n))
    (ctrl : List (ITag × Nat)) (val : List Nat) (tape : Fin L → Bool)
    (hinv : driverCorridorInv width h_width z tape
      (⟨PreToken.node tag :: toks', out, ctrl, val, false⟩ : DriveState n))
    (htoks : toks' ≠ [])
    (hcap : z.ctrlBase + (encodeCtrlStackR ctrl).length
        + (encodeCtrlFrameR (tag, tag.arity)).length ≤ z.ctrlEnd) :
    driverCorridorInv width h_width z
      (nodeStepTape tape
        (z.certEnd - (encodePreorder width h_width (PreToken.node tag :: toks')).length)
        (z.ctrlBase + (encodeCtrlStackR ctrl).length)
        (encodeCtrlFrameR (tag, tag.arity)))
      (⟨toks', out, (tag, tag.arity) :: ctrl, val, false⟩ : DriveState n) := by
  obtain ⟨hwf, hcert, hcfit, hM, hczeros, hout, hofit, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrl, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hwf
  replace hcert : windowSpells tape
      (z.certEnd - (encodePreorder width h_width (PreToken.node tag :: toks')).length)
      (encodePreorder width h_width (PreToken.node tag :: toks')) := hcert
  replace hcfit : z.certBase
      + (encodePreorder width h_width (PreToken.node tag :: toks')).length ≤ z.certEnd := hcfit
  replace hvalid : ValidCertTokens (PreToken.node tag :: toks') := hvalid
  replace hM : ∀ p : Fin L,
      (p : Nat) = z.certEnd
        - (encodePreorder width h_width (PreToken.node tag :: toks')).length - 1 →
      tape p = true := hM
  replace hczeros : ∀ p : Fin L,
      z.ctrlBase + (encodeCtrlStackR ctrl).length ≤ (p : Nat) →
      (p : Nat) < z.certEnd
        - (encodePreorder width h_width (PreToken.node tag :: toks')).length - 1 →
      tape p = false := hczeros
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
  replace hvzeros : ∀ p : Fin L,
      z.valBase + (encodeNatStackR val).length ≤ (p : Nat) →
      (p : Nat) < z.shwBase → tape p = false := hvzeros
  replace hshw : windowSpells tape z.shwBase (List.replicate (out.length + 1) true) := hshw
  replace hsfit : z.shwBase + out.length + 1 ≤ z.shwEnd := hsfit
  replace hszeros : ∀ p : Fin L, z.shwBase + out.length + 1 ≤ (p : Nat) →
      (p : Nat) < z.ctrlBase → tape p = false := hszeros
  replace hctrl : windowSpells tape z.ctrlBase (encodeCtrlStackR ctrl) := hctrl
  replace hcfit2 : z.ctrlBase + (encodeCtrlStackR ctrl).length ≤ z.ctrlEnd := hcfit2
  -- Notation: the old cursor, the encoded lengths, the frame base.
  set cur := z.certEnd - (encodePreorder width h_width (PreToken.node tag :: toks')).length with hcur
  set fb := z.ctrlBase + (encodeCtrlStackR ctrl).length with hfb
  set fr := encodeCtrlFrameR (tag, tag.arity) with hfr
  -- The token's three tag cells: encodePreorder (node :: toks') = tagbits ++ encodePreorder toks'.
  have hbits : encodePreorder width h_width (PreToken.node tag :: toks')
      = encodePreToken width h_width (PreToken.node tag)
        ++ encodePreorder width h_width toks' := encodePreorder_cons width h_width _ _
  have htag3 : (encodePreToken width h_width (PreToken.node tag)).length = 3 := by
    cases tag <;> rfl
  have htail1 : 1 ≤ (encodePreorder width h_width toks').length := by
    have hv : ValidCertTokens toks' := fun t ht => hvalid t (List.mem_cons_of_mem _ ht)
    have := validCertTokens_length_le width h_width hv
    have : 1 ≤ toks'.length := by
      cases toks' with
      | nil => exact absurd rfl htoks
      | cons a l => simp
    omega
  have hlenc : (encodePreorder width h_width (PreToken.node tag :: toks')).length
      = 3 + (encodePreorder width h_width toks').length := by
    rw [hbits, List.length_append, htag3]
  have hfit := hcert.1
  -- Geometry of the cursor area.
  have hcur3 : cur + 3 + (encodePreorder width h_width toks').length = z.certEnd := by
    rw [hcur]; omega
  have hcurB : z.certBase ≤ cur := by rw [hcur]; omega
  -- The frame region sits strictly left of the marker area.
  have hfrlen : fr.length = tag.arity + tag.tagCode + 5 := by
    rw [hfr, encodeCtrlFrameR_length]
  have hfrR : fb + fr.length ≤ z.ctrlEnd := by rw [hfb, hfr]; exact hcap
  have hsep : fb + fr.length < cur - 1 := by
    have : z.ctrlEnd + 2 < z.certBase := h9
    omega
  dsimp only [driverCorridorInv]
  refine ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- 1. The certificate suffix window at the new cursor (cur + 3), untouched by the update.
  · have hsuf := windowSpells_append_right tape cur _ _ (by rw [← hbits]; exact hcert)
    rw [htag3] at hsuf
    rw [show z.certEnd - (encodePreorder width h_width toks').length = cur + 3 from by omega]
    obtain ⟨hsf, hsc⟩ := hsuf
    refine ⟨hsf, fun q hlo hhi => ?_⟩
    rw [← hsc q hlo hhi]
    show nodeStepTape tape cur fb fr q = tape q
    unfold nodeStepTape
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  -- 2. The certificate fit at the new cursor.
  · omega
  -- 3. The new marker at (new cursor) − 1 = cur + 2.
  · intro p hp
    rw [show z.certEnd - (encodePreorder width h_width toks').length - 1 = cur + 2 from by omega]
      at hp
    show nodeStepTape tape cur fb fr p = true
    unfold nodeStepTape
    rw [if_pos hp]
  -- 4. The consumed/dead corridor up to the new marker: grown ctrl content, erased cells, old zeros.
  · intro p hp1 hp2
    rw [show z.certEnd - (encodePreorder width h_width toks').length - 1 = cur + 2 from by omega]
      at hp2
    rw [encodeCtrlStackR_cons, List.length_append, ← hfr] at hp1
    show nodeStepTape tape cur fb fr p = false
    unfold nodeStepTape
    rw [if_neg (by omega : ¬((p : Nat) = cur + 2))]
    by_cases herase : cur - 1 ≤ (p : Nat) ∧ (p : Nat) < cur + 2
    · rw [if_pos herase]
    · rw [if_neg herase,
        if_neg (by omega : ¬(fb ≤ (p : Nat) ∧ (p : Nat) < fb + fr.length))]
      exact hczeros p (by omega) (by rw [hcur]; omega)
  -- 5. The output window, untouched.
  · refine ⟨hout.1, fun q hlo hhi => ?_⟩
    have := hout.2 q hlo hhi
    rw [← this]
    show nodeStepTape tape cur fb fr q = tape q
    unfold nodeStepTape
    have hlist : (unaryField out.length ++ encodeGateRecordStream out).length
        = out.length + 1 + (encodeGateRecordStream out).length := by
      rw [List.length_append, unaryField_length]
    rw [hlist] at hhi
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  -- 6. The output left fit.
  · exact hofit
  -- 7. The frontier marker, untouched.
  · intro p hp
    have := hFM p hp
    rw [← this]
    show nodeStepTape tape cur fb fr p = tape p
    unfold nodeStepTape
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  -- 8. The frontier fit.
  · exact hffit
  -- 9. The FM→val dead corridor, untouched.
  · intro p hp1 hp2
    have := hfzeros p hp1 hp2
    rw [← this]
    show nodeStepTape tape cur fb fr p = tape p
    unfold nodeStepTape
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  -- 10. The value window, untouched.
  · refine ⟨hval.1, fun q hlo hhi => ?_⟩
    have := hval.2 q hlo hhi
    rw [← this]
    show nodeStepTape tape cur fb fr q = tape q
    unfold nodeStepTape
    have hvE : z.valBase + (encodeNatStackR val).length ≤ z.valEnd := hvfit
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  -- 11. The value fit.
  · exact hvfit
  -- 12. The val→SHW dead corridor (val unchanged; the frame sits inside the ctrl zone).
  · intro p hp1 hp2
    have := hvzeros p hp1 hp2
    rw [← this]
    show nodeStepTape tape cur fb fr p = tape p
    unfold nodeStepTape
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  -- 12a. The SHW window (untouched; no emit on the node branch).
  · refine ⟨hshw.1, fun q hlo hhi => ?_⟩
    have hq := hshw.2 q hlo hhi
    rw [List.length_replicate] at hhi
    rw [← hq]
    show nodeStepTape tape cur fb fr q = tape q
    unfold nodeStepTape
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  -- 12b. The SHW fit (out unchanged).
  · exact hsfit
  -- 12c. The SHW→ctrl dead corridor (the frame sits inside the ctrl zone, right of it).
  · intro p hp1 hp2
    have := hszeros p hp1 hp2
    rw [← this]
    show nodeStepTape tape cur fb fr p = tape p
    unfold nodeStepTape
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  -- 13. The control window: the old content untouched, the frame written — the codec cons.
  · rw [encodeCtrlStackR_cons, ← hfr]
    refine ⟨by
      rw [List.length_append]
      have := hctrl.1
      omega, fun q hlo hhi => ?_⟩
    rw [List.length_append] at hhi
    by_cases hq : (q : Nat) < fb
    · -- old content
      rw [List.getD_append _ _ _ _ (by rw [hfb] at hq; omega)]
      rw [← hctrl.2 q hlo (by rw [hfb] at hq; omega)]
      show nodeStepTape tape cur fb fr q = tape q
      unfold nodeStepTape
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · -- the frame cells
      show nodeStepTape tape cur fb fr q
          = (encodeCtrlStackR ctrl ++ fr).getD ((q : Nat) - z.ctrlBase) false
      unfold nodeStepTape
      rw [if_neg (by omega), if_neg (by omega),
        if_pos (⟨by omega, by omega⟩ : fb ≤ (q : Nat) ∧ (q : Nat) < fb + fr.length),
        List.getD_append_right _ _ _ _ (by omega)]
      congr 1
      omega
  -- 14. The control fit (the capacity hypothesis).
  · rw [encodeCtrlStackR_cons, List.length_append, ← hfr]
    omega
  -- 15. Validity of the tail.
  · exact fun t ht => hvalid t (List.mem_cons_of_mem _ ht)
  -- 16. Settling coherence (still reading).
  · intro hs; cases hs

end ContractExpansion
end Frontier
end Pnp4
