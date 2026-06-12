import Pnp4.Frontier.ContractExpansion.TreeMCSPNodeIterProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPCorridorNodeStep

/-!
# The node iteration, end to end (tnot) — D2t-5b (Block A5m-5, run)

The node arm run on the U-stack machine: for a reading state whose next token is `node tnot`, from
the read home `nodeIterProgram` steps onto the cursor, reads the tag (`certTrie`, ftf), walks back,
rewrites the marker block (the old marker and the first two tag cells zeroed, the new marker planted
on the last tag cell), hops down to the control top (the stack's right end — the base sentinel when
the stack is empty), pushes the `(tnot, 1)` frame at the first free cell, and scans home onto the
**new** marker — ending at the home-read out with the tape **exactly `corridorInv_nodeStep`'s
transformer `nodeStepTape`**.  The `tand`/`tor` runs mirror this one.

**Progress classification (AGENTS.md): Infrastructure** — a staging machine's end-to-end run;
proves no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.  **No
`P ≠ NP` claim.** -/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- The node arm's two block writes — the marker block from the old marker, then the frame at the
control zone's first free cell — compose to exactly `nodeStepTape` (the zones are disjoint: the
frame ends strictly below the old marker). -/
theorem writeMarkFrame_eq_nodeStepTape {L : Nat} (tape : Fin L → Bool) (cur fbase : Nat)
    (frame : List Bool) (hcur : 1 ≤ cur) (hdisj : fbase + frame.length < cur) :
    writeBlockTape (writeBlockTape tape (cur - 1) nodeMarkBlock) fbase frame
      = nodeStepTape tape cur fbase frame := by
  funext q
  simp only [writeBlockTape, nodeStepTape, nodeMarkBlock_length]
  by_cases hf : fbase ≤ (q : Nat) ∧ (q : Nat) < fbase + frame.length
  · rw [if_pos hf, if_neg (show ¬ (q : Nat) = cur + 2 from by omega), if_neg (by omega),
      if_pos hf]
  · rw [if_neg hf]
    by_cases hm : cur - 1 ≤ (q : Nat) ∧ (q : Nat) < (cur - 1) + 4
    · rw [if_pos hm]
      by_cases hq2 : (q : Nat) = cur + 2
      · rw [if_pos hq2, show (q : Nat) - (cur - 1) = 3 from by omega]
        rfl
      · rw [if_neg hq2,
          if_pos (show cur - 1 ≤ (q : Nat) ∧ (q : Nat) < cur + 2 from by omega)]
        have h3 : (q : Nat) - (cur - 1) = 0 ∨ (q : Nat) - (cur - 1) = 1
            ∨ (q : Nat) - (cur - 1) = 2 := by omega
        rcases h3 with h | h | h <;> rw [h] <;> rfl
    · rw [if_neg hm, if_neg (show ¬ (q : Nat) = cur + 2 from by omega), if_neg (by omega),
        if_neg hf]

/-- **The node iteration (tnot), end to end.**  For a reading state whose next token is `node tnot`
(child following, frame room available), from the read home, `nodeIterProgram` reaches the home-read
out (phase `114`) with the head on the **new** marker (the stepped state's home) and the tape
exactly `corridorInv_nodeStep`'s transformer, within `2 · certEnd + 40` steps. -/
theorem nodeIter_run_tnot {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (st : DriveState n) (toks' : List (PreToken n))
    (c0 : Configuration (M := nodeIterProgram.toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z c0.tape st)
    (htoks : st.toks = PreToken.node ITag.tnot :: toks')
    (htoks' : toks' ≠ [])
    (hcap : z.ctrlBase + (encodeCtrlStackR st.ctrl).length
        + (encodeCtrlFrameR (ITag.tnot, ITag.tnot.arity)).length ≤ z.ctrlEnd)
    (hphase : (c0.state.fst : Nat) = 0)
    (hhead : (c0.head : Nat) = z.certEnd - (encodePreorder width h_width st.toks).length - 1) :
    ∃ T : Nat, T ≤ 2 * z.certEnd + 40
      ∧ (((TM.runConfig (M := nodeIterProgram.toPhased.toTM) c0 T).state).fst : Nat) = 114
      ∧ ((TM.runConfig (M := nodeIterProgram.toPhased.toTM) c0 T).head : Nat)
          = z.certEnd - (encodePreorder width h_width toks').length - 1
      ∧ (TM.runConfig (M := nodeIterProgram.toPhased.toTM) c0 T).tape
          = nodeStepTape c0.tape
              (z.certEnd - (encodePreorder width h_width st.toks).length)
              (z.ctrlBase + (encodeCtrlStackR st.ctrl).length)
              (encodeCtrlFrameR (ITag.tnot, ITag.tnot.arity)) := by
  obtain ⟨hwf, hcert, hcfit, hmark, hcorr, hout, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrlw, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwf
  replace hcert : windowSpells c0.tape
      (z.certEnd - (encodePreorder width h_width st.toks).length)
      (encodePreorder width h_width st.toks) := hcert
  replace hcfit : z.certBase + (encodePreorder width h_width st.toks).length ≤ z.certEnd := hcfit
  replace hmark : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = z.certEnd - (encodePreorder width h_width st.toks).length - 1 →
      c0.tape p = true := hmark
  replace hcorr : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      z.ctrlBase + (encodeCtrlStackR st.ctrl).length ≤ (p : Nat) →
      (p : Nat) < z.certEnd - (encodePreorder width h_width st.toks).length - 1 →
      c0.tape p = false := hcorr
  replace hctrlw : windowSpells c0.tape z.ctrlBase (encodeCtrlStackR st.ctrl) := hctrlw
  replace hcfit2 : z.ctrlBase + (encodeCtrlStackR st.ctrl).length ≤ z.ctrlEnd := hcfit2
  replace hvalid : ValidCertTokens st.toks := hvalid
  rw [htoks] at hcert hcfit hmark hcorr hvalid hhead ⊢
  -- Geometry: the cursor, the tag bits, the tail room, the control top.
  have hbits : encodePreorder width h_width (PreToken.node ITag.tnot :: toks')
      = [false, true, false] ++ encodePreorder width h_width toks' := by
    rw [encodePreorder_cons]
    rfl
  have henc_len : (encodePreorder width h_width (PreToken.node ITag.tnot :: toks')).length
      = 3 + (encodePreorder width h_width toks').length := by
    rw [hbits, List.length_append]
    rfl
  have htail : 1 ≤ (encodePreorder width h_width toks').length := by
    obtain ⟨t, ts, rfl⟩ := List.exists_cons_of_ne_nil htoks'
    have hvt : ValidCertToken t := hvalid t (List.mem_cons_of_mem _ List.mem_cons_self)
    have h1t := validCertToken_one_le_length width h_width hvt
    rw [encodePreorder_cons, List.length_append]
    omega
  set CUR := z.certEnd - (encodePreorder width h_width (PreToken.node ITag.tnot :: toks')).length
    with hCUR
  have hlen1 : 1 ≤ (encodeCtrlStackR st.ctrl).length := by
    unfold encodeCtrlStackR
    simp
  have hcap6 : z.ctrlBase + (encodeCtrlStackR st.ctrl).length + 6 ≤ z.ctrlEnd := by
    have := hcap
    simp only [encodeCtrlFrameR_length, ITag.arity, ITag.tagCode] at this
    omega
  set ctop := z.ctrlBase + (encodeCtrlStackR st.ctrl).length - 1 with hctop
  -- The cert window's tag cells, the marker, the control top.
  have hcell0 : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = CUR → c0.tape p = false := by
    intro p hp
    have := windowSpells_cell c0.tape _ _ hcert 0 (by omega) p (by omega)
    rw [this, hbits]
    rfl
  have hcell1 : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = CUR + 1 → c0.tape p = true := by
    intro p hp
    have := windowSpells_cell c0.tape _ _ hcert 1 (by omega) p (by omega)
    rw [this, hbits]
    rfl
  have hcell2 : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = CUR + 2 → c0.tape p = false := by
    intro p hp
    have := windowSpells_cell c0.tape _ _ hcert 2 (by omega) p (by omega)
    rw [this, hbits]
    rfl
  have htop : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = ctop → c0.tape p = true := by
    intro p hp
    have hcell := windowSpells_cell c0.tape z.ctrlBase (encodeCtrlStackR st.ctrl) hctrlw
      ((encodeCtrlStackR st.ctrl).length - 1) (by omega) p (by omega)
    rw [hcell]
    have hlast := encodeCtrlStackR_getLast_true st.ctrl
    rw [List.getLast?_eq_getElem?] at hlast
    rw [List.getD_eq_getElem?_getD, hlast]
    rfl
  -- Leg 1 (phases 0–1 → 2): step right onto the cursor.
  obtain ⟨hp1, hh1, ht1⟩ := nodeIter_region_stepRight.run_stepRight_hop c0 hphase (by omega)
  set c1 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c0 2 with hc1
  -- Leg 2 (phases 2–13 → 14): the tag trie, not verdict (ftf), landing past the tag.
  obtain ⟨hp2, hh2, ht2⟩ := nodeIter_region_certTrie.run_certTrie_not_hop
    (by rfl) (by rfl) (by rfl) (by rfl) c1 hp1 (by omega)
    (by rw [ht1]; exact hcell0 c1.head (by omega))
    (fun p hp => by rw [ht1]; exact hcell1 p (by omega))
    (fun p hp => by rw [ht1]; exact hcell2 p (by omega))
  set c2 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c1 4 with hc2
  -- Legs 3–6 (phases 14–21 → 22): four steps left, back onto the old marker.
  obtain ⟨hp3, hh3, ht3⟩ := nodeIter_region_Not_sL1.run_stepLeft_hop c2 hp2 (by omega)
  set c3 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c2 2 with hc3
  obtain ⟨hp4, hh4, ht4⟩ := nodeIter_region_Not_sL2.run_stepLeft_hop c3 hp3 (by omega)
  set c4 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c3 2 with hc4
  obtain ⟨hp5, hh5, ht5⟩ := nodeIter_region_Not_sL3.run_stepLeft_hop c4 hp4 (by omega)
  set c5 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c4 2 with hc5
  obtain ⟨hp6, hh6, ht6⟩ := nodeIter_region_Not_sL4.run_stepLeft_hop c5 hp5 (by omega)
  set c6 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c5 2 with hc6
  have hh6' : (c6.head : Nat) = CUR - 1 := by omega
  -- Leg 7 (phases 22–26 → 27): the marker-block rewrite from the old marker.
  obtain ⟨hp7, hh7, ht7⟩ := nodeIter_region_Not_mark.run_writeBits_hop c6 hp6
    (by simp only [nodeMarkBlock_length]; omega)
  set c7 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c6
    (nodeMarkBlock.length + 1) with hc7
  have ht7' : c7.tape = writeBlockTape c0.tape (CUR - 1) nodeMarkBlock := by
    rw [ht7, ht6, ht5, ht4, ht3, ht2, ht1, hh6']
  have hh7' : (c7.head : Nat) = CUR + 3 := by
    rw [hh7, hh6']
    simp only [nodeMarkBlock_length]
    omega
  -- The rewritten cursor area: zeros on [CUR − 1, CUR + 2), the new marker at CUR + 2.
  have h7low : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) < CUR - 1 → c7.tape p = c0.tape p := by
    intro p hp
    rw [ht7']
    exact writeBlockTape_below _ _ _ p hp
  have h7mark : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      CUR - 1 ≤ (p : Nat) → (p : Nat) < CUR + 2 → c7.tape p = false := by
    intro p hlo hhi
    rw [ht7']
    unfold writeBlockTape
    rw [if_pos (by simp only [nodeMarkBlock_length]; omega)]
    have h3 : (p : Nat) - (CUR - 1) = 0 ∨ (p : Nat) - (CUR - 1) = 1
        ∨ (p : Nat) - (CUR - 1) = 2 := by omega
    rcases h3 with h | h | h <;> rw [h] <;> rfl
  have h7anchor : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = CUR + 2 → c7.tape p = true := by
    intro p hp
    rw [ht7']
    unfold writeBlockTape
    rw [if_pos (by simp only [nodeMarkBlock_length]; omega),
      show (p : Nat) - (CUR - 1) = 3 from by omega]
    rfl
  -- Legs 8–9 (phases 27–30 → 31): two steps left off the new marker.
  obtain ⟨hp8, hh8, ht8⟩ := nodeIter_region_Not_sL5.run_stepLeft_hop c7 hp7 (by omega)
  set c8 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c7 2 with hc8
  obtain ⟨hp9, hh9, ht9⟩ := nodeIter_region_Not_sL6.run_stepLeft_hop c8 hp8 (by omega)
  set c9 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c8 2 with hc9
  -- Leg 10 (phases 31–32 → 33): scan left onto the control top.
  obtain ⟨hp10, hh10, ht10⟩ := nodeIter_region_Not_scanL.run_scanLeft_hop c9 hp9 ctop
    (by omega)
    (fun p hlo hhi => by
      rw [ht9, ht8]
      by_cases hp : (p : Nat) < CUR - 1
      · rw [h7low p hp]
        exact hcorr p (by omega) (by omega)
      · exact h7mark p (by omega) (by omega))
    (fun p hp => by
      rw [ht9, ht8, h7low p (by omega)]
      exact htop p hp)
  set c10 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c9
    (((c9.head : Nat) - ctop) + 2) with hc10
  -- Leg 11 (phases 33–34 → 35): step right onto the first free control cell.
  obtain ⟨hp11, hh11, ht11⟩ := nodeIter_region_Not_sR.run_stepRight_hop c10 hp10 (by omega)
  set c11 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c10 2 with hc11
  have hh11' : (c11.head : Nat) = z.ctrlBase + (encodeCtrlStackR st.ctrl).length := by omega
  -- Leg 12 (phases 35–41 → 112): the frame push at the control zone's right end.
  obtain ⟨hp12, hh12, ht12⟩ := nodeIter_region_Not_frame.run_writeBits_hop c11 hp11
    (by
      simp only [nodeFrame_length, ITag.arity, ITag.tagCode]
      omega)
  set c12 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c11
    ((nodeFrame ITag.tnot).length + 1) with hc12
  have hh12' : (c12.head : Nat) = z.ctrlBase + (encodeCtrlStackR st.ctrl).length + 6 := by
    rw [hh12, hh11']
    simp only [nodeFrame_length, ITag.arity, ITag.tagCode]
  have ht12' : c12.tape = nodeStepTape c0.tape CUR
      (z.ctrlBase + (encodeCtrlStackR st.ctrl).length)
      (encodeCtrlFrameR (ITag.tnot, ITag.tnot.arity)) := by
    rw [ht12, ht11, ht10, ht9, ht8, hh11', ht7']
    exact writeMarkFrame_eq_nodeStepTape c0.tape CUR
      (z.ctrlBase + (encodeCtrlStackR st.ctrl).length) (nodeFrame ITag.tnot) (by omega)
      (by simp only [nodeFrame_length, ITag.arity, ITag.tagCode]; omega)
  -- The transformed tape off the two written zones, for the return scan.
  have h12low : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      z.ctrlBase + (encodeCtrlStackR st.ctrl).length + 6 ≤ (p : Nat) →
      (p : Nat) < CUR - 1 → c12.tape p = false := by
    intro p hlo hhi
    rw [ht12']
    unfold nodeStepTape
    rw [if_neg (by omega), if_neg (by omega),
      if_neg (by
        simp only [encodeCtrlFrameR_length, ITag.arity, ITag.tagCode]
        omega)]
    exact hcorr p (by omega) (by omega)
  have h12mark : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      CUR - 1 ≤ (p : Nat) → (p : Nat) < CUR + 2 → c12.tape p = false := by
    intro p hlo hhi
    rw [ht12']
    unfold nodeStepTape
    rw [if_neg (by omega), if_pos ⟨hlo, hhi⟩]
  have h12anchor : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = CUR + 2 → c12.tape p = true := by
    intro p hp
    rw [ht12']
    unfold nodeStepTape
    rw [if_pos hp]
  -- Leg 13 (phases 112–113 → 114): scan right home onto the new marker.
  obtain ⟨hp13, hh13, ht13⟩ := nodeIter_region_scanRight.run_scanRight_hop c12 hp12
    ((CUR + 2) - (c12.head : Nat))
    (by omega)
    (fun p hlo hhi => by
      by_cases hp : (p : Nat) < CUR - 1
      · exact h12low p (by omega) hp
      · exact h12mark p (by omega) (by omega))
    (fun p hp => h12anchor p (by omega))
  -- Assemble the chain (right-nested junctions; each split is one controlled rewrite).
  have hfinal : TM.runConfig (M := nodeIterProgram.toPhased.toTM) c0
      (2 + (4 + (2 + (2 + (2 + (2 + ((nodeMarkBlock.length + 1) + (2 + (2
        + ((((c9.head : Nat) - ctop) + 2) + (2 + (((nodeFrame ITag.tnot).length + 1)
          + (((CUR + 2) - (c12.head : Nat)) + 2)))))))))))))
      = TM.runConfig (M := nodeIterProgram.toPhased.toTM) c12
          (((CUR + 2) - (c12.head : Nat)) + 2) := by
    rw [TM.runConfig_add, ← hc1]
    rw [TM.runConfig_add, ← hc2]
    rw [TM.runConfig_add, ← hc3]
    rw [TM.runConfig_add, ← hc4]
    rw [TM.runConfig_add, ← hc5]
    rw [TM.runConfig_add, ← hc6]
    rw [TM.runConfig_add, ← hc7]
    rw [TM.runConfig_add, ← hc8]
    rw [TM.runConfig_add, ← hc9]
    rw [TM.runConfig_add, ← hc10]
    rw [TM.runConfig_add, ← hc11]
    rw [TM.runConfig_add, ← hc12]
  refine ⟨2 + (4 + (2 + (2 + (2 + (2 + ((nodeMarkBlock.length + 1) + (2 + (2
      + ((((c9.head : Nat) - ctop) + 2) + (2 + (((nodeFrame ITag.tnot).length + 1)
        + (((CUR + 2) - (c12.head : Nat)) + 2)))))))))))),
    by
      simp only [nodeMarkBlock_length, nodeFrame_length, ITag.arity, ITag.tagCode]
      omega, ?_, ?_, ?_⟩
  · rw [hfinal, hp13]
  · rw [hfinal]
    omega
  · rw [hfinal, ht13]
    exact ht12'

/-- **The node iteration (tand), end to end** — the `tand` mirror of `nodeIter_run_tand`. -/
theorem nodeIter_run_tand {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (st : DriveState n) (toks' : List (PreToken n))
    (c0 : Configuration (M := nodeIterProgram.toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z c0.tape st)
    (htoks : st.toks = PreToken.node ITag.tand :: toks')
    (htoks' : toks' ≠ [])
    (hcap : z.ctrlBase + (encodeCtrlStackR st.ctrl).length
        + (encodeCtrlFrameR (ITag.tand, ITag.tand.arity)).length ≤ z.ctrlEnd)
    (hphase : (c0.state.fst : Nat) = 0)
    (hhead : (c0.head : Nat) = z.certEnd - (encodePreorder width h_width st.toks).length - 1) :
    ∃ T : Nat, T ≤ 2 * z.certEnd + 40
      ∧ (((TM.runConfig (M := nodeIterProgram.toPhased.toTM) c0 T).state).fst : Nat) = 114
      ∧ ((TM.runConfig (M := nodeIterProgram.toPhased.toTM) c0 T).head : Nat)
          = z.certEnd - (encodePreorder width h_width toks').length - 1
      ∧ (TM.runConfig (M := nodeIterProgram.toPhased.toTM) c0 T).tape
          = nodeStepTape c0.tape
              (z.certEnd - (encodePreorder width h_width st.toks).length)
              (z.ctrlBase + (encodeCtrlStackR st.ctrl).length)
              (encodeCtrlFrameR (ITag.tand, ITag.tand.arity)) := by
  obtain ⟨hwf, hcert, hcfit, hmark, hcorr, hout, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrlw, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwf
  replace hcert : windowSpells c0.tape
      (z.certEnd - (encodePreorder width h_width st.toks).length)
      (encodePreorder width h_width st.toks) := hcert
  replace hcfit : z.certBase + (encodePreorder width h_width st.toks).length ≤ z.certEnd := hcfit
  replace hmark : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = z.certEnd - (encodePreorder width h_width st.toks).length - 1 →
      c0.tape p = true := hmark
  replace hcorr : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      z.ctrlBase + (encodeCtrlStackR st.ctrl).length ≤ (p : Nat) →
      (p : Nat) < z.certEnd - (encodePreorder width h_width st.toks).length - 1 →
      c0.tape p = false := hcorr
  replace hctrlw : windowSpells c0.tape z.ctrlBase (encodeCtrlStackR st.ctrl) := hctrlw
  replace hcfit2 : z.ctrlBase + (encodeCtrlStackR st.ctrl).length ≤ z.ctrlEnd := hcfit2
  replace hvalid : ValidCertTokens st.toks := hvalid
  rw [htoks] at hcert hcfit hmark hcorr hvalid hhead ⊢
  -- Geometry: the cursor, the tag bits, the tail room, the control top.
  have hbits : encodePreorder width h_width (PreToken.node ITag.tand :: toks')
      = [false, true, true] ++ encodePreorder width h_width toks' := by
    rw [encodePreorder_cons]
    rfl
  have henc_len : (encodePreorder width h_width (PreToken.node ITag.tand :: toks')).length
      = 3 + (encodePreorder width h_width toks').length := by
    rw [hbits, List.length_append]
    rfl
  have htail : 1 ≤ (encodePreorder width h_width toks').length := by
    obtain ⟨t, ts, rfl⟩ := List.exists_cons_of_ne_nil htoks'
    have hvt : ValidCertToken t := hvalid t (List.mem_cons_of_mem _ List.mem_cons_self)
    have h1t := validCertToken_one_le_length width h_width hvt
    rw [encodePreorder_cons, List.length_append]
    omega
  set CUR := z.certEnd - (encodePreorder width h_width (PreToken.node ITag.tand :: toks')).length
    with hCUR
  have hlen1 : 1 ≤ (encodeCtrlStackR st.ctrl).length := by
    unfold encodeCtrlStackR
    simp
  have hcap8 : z.ctrlBase + (encodeCtrlStackR st.ctrl).length + 8 ≤ z.ctrlEnd := by
    have := hcap
    simp only [encodeCtrlFrameR_length, ITag.arity, ITag.tagCode] at this
    omega
  set ctop := z.ctrlBase + (encodeCtrlStackR st.ctrl).length - 1 with hctop
  -- The cert window's tag cells, the marker, the control top.
  have hcell0 : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = CUR → c0.tape p = false := by
    intro p hp
    have := windowSpells_cell c0.tape _ _ hcert 0 (by omega) p (by omega)
    rw [this, hbits]
    rfl
  have hcell1 : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = CUR + 1 → c0.tape p = true := by
    intro p hp
    have := windowSpells_cell c0.tape _ _ hcert 1 (by omega) p (by omega)
    rw [this, hbits]
    rfl
  have hcell2 : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = CUR + 2 → c0.tape p = true := by
    intro p hp
    have := windowSpells_cell c0.tape _ _ hcert 2 (by omega) p (by omega)
    rw [this, hbits]
    rfl
  have htop : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = ctop → c0.tape p = true := by
    intro p hp
    have hcell := windowSpells_cell c0.tape z.ctrlBase (encodeCtrlStackR st.ctrl) hctrlw
      ((encodeCtrlStackR st.ctrl).length - 1) (by omega) p (by omega)
    rw [hcell]
    have hlast := encodeCtrlStackR_getLast_true st.ctrl
    rw [List.getLast?_eq_getElem?] at hlast
    rw [List.getD_eq_getElem?_getD, hlast]
    rfl
  -- Leg 1 (phases 0–1 → 2): step right onto the cursor.
  obtain ⟨hp1, hh1, ht1⟩ := nodeIter_region_stepRight.run_stepRight_hop c0 hphase (by omega)
  set c1 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c0 2 with hc1
  -- Leg 2 (phases 2–13 → 14): the tag trie, tand verdict (ftt), landing past the tag.
  obtain ⟨hp2, hh2, ht2⟩ := nodeIter_region_certTrie.run_certTrie_and_hop
    (by rfl) (by rfl) (by rfl) (by rfl) c1 hp1 (by omega)
    (by rw [ht1]; exact hcell0 c1.head (by omega))
    (fun p hp => by rw [ht1]; exact hcell1 p (by omega))
    (fun p hp => by rw [ht1]; exact hcell2 p (by omega))
  set c2 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c1 4 with hc2
  -- Legs 3–6 (phases 14–21 → 22): four steps left, back onto the old marker.
  obtain ⟨hp3, hh3, ht3⟩ := nodeIter_region_And_sL1.run_stepLeft_hop c2 hp2 (by omega)
  set c3 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c2 2 with hc3
  obtain ⟨hp4, hh4, ht4⟩ := nodeIter_region_And_sL2.run_stepLeft_hop c3 hp3 (by omega)
  set c4 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c3 2 with hc4
  obtain ⟨hp5, hh5, ht5⟩ := nodeIter_region_And_sL3.run_stepLeft_hop c4 hp4 (by omega)
  set c5 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c4 2 with hc5
  obtain ⟨hp6, hh6, ht6⟩ := nodeIter_region_And_sL4.run_stepLeft_hop c5 hp5 (by omega)
  set c6 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c5 2 with hc6
  have hh6' : (c6.head : Nat) = CUR - 1 := by omega
  -- Leg 7 (phases 22–26 → 27): the marker-block rewrite from the old marker.
  obtain ⟨hp7, hh7, ht7⟩ := nodeIter_region_And_mark.run_writeBits_hop c6 hp6
    (by simp only [nodeMarkBlock_length]; omega)
  set c7 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c6
    (nodeMarkBlock.length + 1) with hc7
  have ht7' : c7.tape = writeBlockTape c0.tape (CUR - 1) nodeMarkBlock := by
    rw [ht7, ht6, ht5, ht4, ht3, ht2, ht1, hh6']
  have hh7' : (c7.head : Nat) = CUR + 3 := by
    rw [hh7, hh6']
    simp only [nodeMarkBlock_length]
    omega
  -- The rewritten cursor area: zeros on [CUR − 1, CUR + 2), the new marker at CUR + 2.
  have h7low : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) < CUR - 1 → c7.tape p = c0.tape p := by
    intro p hp
    rw [ht7']
    exact writeBlockTape_below _ _ _ p hp
  have h7mark : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      CUR - 1 ≤ (p : Nat) → (p : Nat) < CUR + 2 → c7.tape p = false := by
    intro p hlo hhi
    rw [ht7']
    unfold writeBlockTape
    rw [if_pos (by simp only [nodeMarkBlock_length]; omega)]
    have h3 : (p : Nat) - (CUR - 1) = 0 ∨ (p : Nat) - (CUR - 1) = 1
        ∨ (p : Nat) - (CUR - 1) = 2 := by omega
    rcases h3 with h | h | h <;> rw [h] <;> rfl
  have h7anchor : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = CUR + 2 → c7.tape p = true := by
    intro p hp
    rw [ht7']
    unfold writeBlockTape
    rw [if_pos (by simp only [nodeMarkBlock_length]; omega),
      show (p : Nat) - (CUR - 1) = 3 from by omega]
    rfl
  -- Legs 8–9 (phases 27–30 → 31): two steps left off the new marker.
  obtain ⟨hp8, hh8, ht8⟩ := nodeIter_region_And_sL5.run_stepLeft_hop c7 hp7 (by omega)
  set c8 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c7 2 with hc8
  obtain ⟨hp9, hh9, ht9⟩ := nodeIter_region_And_sL6.run_stepLeft_hop c8 hp8 (by omega)
  set c9 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c8 2 with hc9
  -- Leg 10 (phases 31–32 → 33): scan left onto the control top.
  obtain ⟨hp10, hh10, ht10⟩ := nodeIter_region_And_scanL.run_scanLeft_hop c9 hp9 ctop
    (by omega)
    (fun p hlo hhi => by
      rw [ht9, ht8]
      by_cases hp : (p : Nat) < CUR - 1
      · rw [h7low p hp]
        exact hcorr p (by omega) (by omega)
      · exact h7mark p (by omega) (by omega))
    (fun p hp => by
      rw [ht9, ht8, h7low p (by omega)]
      exact htop p hp)
  set c10 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c9
    (((c9.head : Nat) - ctop) + 2) with hc10
  -- Leg 11 (phases 33–34 → 35): step right onto the first free control cell.
  obtain ⟨hp11, hh11, ht11⟩ := nodeIter_region_And_sR.run_stepRight_hop c10 hp10 (by omega)
  set c11 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c10 2 with hc11
  have hh11' : (c11.head : Nat) = z.ctrlBase + (encodeCtrlStackR st.ctrl).length := by omega
  -- Leg 12 (phases 35–41 → 112): the frame push at the control zone's right end.
  obtain ⟨hp12, hh12, ht12⟩ := nodeIter_region_And_frame.run_writeBits_hop c11 hp11
    (by
      simp only [nodeFrame_length, ITag.arity, ITag.tagCode]
      omega)
  set c12 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c11
    ((nodeFrame ITag.tand).length + 1) with hc12
  have hh12' : (c12.head : Nat) = z.ctrlBase + (encodeCtrlStackR st.ctrl).length + 8 := by
    rw [hh12, hh11']
    simp only [nodeFrame_length, ITag.arity, ITag.tagCode]
  have ht12' : c12.tape = nodeStepTape c0.tape CUR
      (z.ctrlBase + (encodeCtrlStackR st.ctrl).length)
      (encodeCtrlFrameR (ITag.tand, ITag.tand.arity)) := by
    rw [ht12, ht11, ht10, ht9, ht8, hh11', ht7']
    exact writeMarkFrame_eq_nodeStepTape c0.tape CUR
      (z.ctrlBase + (encodeCtrlStackR st.ctrl).length) (nodeFrame ITag.tand) (by omega)
      (by simp only [nodeFrame_length, ITag.arity, ITag.tagCode]; omega)
  -- The transformed tape off the two written zones, for the return scan.
  have h12low : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      z.ctrlBase + (encodeCtrlStackR st.ctrl).length + 8 ≤ (p : Nat) →
      (p : Nat) < CUR - 1 → c12.tape p = false := by
    intro p hlo hhi
    rw [ht12']
    unfold nodeStepTape
    rw [if_neg (by omega), if_neg (by omega),
      if_neg (by
        simp only [encodeCtrlFrameR_length, ITag.arity, ITag.tagCode]
        omega)]
    exact hcorr p (by omega) (by omega)
  have h12mark : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      CUR - 1 ≤ (p : Nat) → (p : Nat) < CUR + 2 → c12.tape p = false := by
    intro p hlo hhi
    rw [ht12']
    unfold nodeStepTape
    rw [if_neg (by omega), if_pos ⟨hlo, hhi⟩]
  have h12anchor : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = CUR + 2 → c12.tape p = true := by
    intro p hp
    rw [ht12']
    unfold nodeStepTape
    rw [if_pos hp]
  -- Leg 13 (phases 112–113 → 114): scan right home onto the new marker.
  obtain ⟨hp13, hh13, ht13⟩ := nodeIter_region_scanRight.run_scanRight_hop c12 hp12
    ((CUR + 2) - (c12.head : Nat))
    (by omega)
    (fun p hlo hhi => by
      by_cases hp : (p : Nat) < CUR - 1
      · exact h12low p (by omega) hp
      · exact h12mark p (by omega) (by omega))
    (fun p hp => h12anchor p (by omega))
  -- Assemble the chain (right-nested junctions; each split is one controlled rewrite).
  have hfinal : TM.runConfig (M := nodeIterProgram.toPhased.toTM) c0
      (2 + (4 + (2 + (2 + (2 + (2 + ((nodeMarkBlock.length + 1) + (2 + (2
        + ((((c9.head : Nat) - ctop) + 2) + (2 + (((nodeFrame ITag.tand).length + 1)
          + (((CUR + 2) - (c12.head : Nat)) + 2)))))))))))))
      = TM.runConfig (M := nodeIterProgram.toPhased.toTM) c12
          (((CUR + 2) - (c12.head : Nat)) + 2) := by
    rw [TM.runConfig_add, ← hc1]
    rw [TM.runConfig_add, ← hc2]
    rw [TM.runConfig_add, ← hc3]
    rw [TM.runConfig_add, ← hc4]
    rw [TM.runConfig_add, ← hc5]
    rw [TM.runConfig_add, ← hc6]
    rw [TM.runConfig_add, ← hc7]
    rw [TM.runConfig_add, ← hc8]
    rw [TM.runConfig_add, ← hc9]
    rw [TM.runConfig_add, ← hc10]
    rw [TM.runConfig_add, ← hc11]
    rw [TM.runConfig_add, ← hc12]
  refine ⟨2 + (4 + (2 + (2 + (2 + (2 + ((nodeMarkBlock.length + 1) + (2 + (2
      + ((((c9.head : Nat) - ctop) + 2) + (2 + (((nodeFrame ITag.tand).length + 1)
        + (((CUR + 2) - (c12.head : Nat)) + 2)))))))))))),
    by
      simp only [nodeMarkBlock_length, nodeFrame_length, ITag.arity, ITag.tagCode]
      omega, ?_, ?_, ?_⟩
  · rw [hfinal, hp13]
  · rw [hfinal]
    omega
  · rw [hfinal, ht13]
    exact ht12'

/-- **The node iteration (tor), end to end** — the `tor` mirror of `nodeIter_run_tor`. -/
theorem nodeIter_run_tor {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (st : DriveState n) (toks' : List (PreToken n))
    (c0 : Configuration (M := nodeIterProgram.toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z c0.tape st)
    (htoks : st.toks = PreToken.node ITag.tor :: toks')
    (htoks' : toks' ≠ [])
    (hcap : z.ctrlBase + (encodeCtrlStackR st.ctrl).length
        + (encodeCtrlFrameR (ITag.tor, ITag.tor.arity)).length ≤ z.ctrlEnd)
    (hphase : (c0.state.fst : Nat) = 0)
    (hhead : (c0.head : Nat) = z.certEnd - (encodePreorder width h_width st.toks).length - 1) :
    ∃ T : Nat, T ≤ 2 * z.certEnd + 40
      ∧ (((TM.runConfig (M := nodeIterProgram.toPhased.toTM) c0 T).state).fst : Nat) = 114
      ∧ ((TM.runConfig (M := nodeIterProgram.toPhased.toTM) c0 T).head : Nat)
          = z.certEnd - (encodePreorder width h_width toks').length - 1
      ∧ (TM.runConfig (M := nodeIterProgram.toPhased.toTM) c0 T).tape
          = nodeStepTape c0.tape
              (z.certEnd - (encodePreorder width h_width st.toks).length)
              (z.ctrlBase + (encodeCtrlStackR st.ctrl).length)
              (encodeCtrlFrameR (ITag.tor, ITag.tor.arity)) := by
  obtain ⟨hwf, hcert, hcfit, hmark, hcorr, hout, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrlw, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwf
  replace hcert : windowSpells c0.tape
      (z.certEnd - (encodePreorder width h_width st.toks).length)
      (encodePreorder width h_width st.toks) := hcert
  replace hcfit : z.certBase + (encodePreorder width h_width st.toks).length ≤ z.certEnd := hcfit
  replace hmark : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = z.certEnd - (encodePreorder width h_width st.toks).length - 1 →
      c0.tape p = true := hmark
  replace hcorr : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      z.ctrlBase + (encodeCtrlStackR st.ctrl).length ≤ (p : Nat) →
      (p : Nat) < z.certEnd - (encodePreorder width h_width st.toks).length - 1 →
      c0.tape p = false := hcorr
  replace hctrlw : windowSpells c0.tape z.ctrlBase (encodeCtrlStackR st.ctrl) := hctrlw
  replace hcfit2 : z.ctrlBase + (encodeCtrlStackR st.ctrl).length ≤ z.ctrlEnd := hcfit2
  replace hvalid : ValidCertTokens st.toks := hvalid
  rw [htoks] at hcert hcfit hmark hcorr hvalid hhead ⊢
  -- Geometry: the cursor, the tag bits, the tail room, the control top.
  have hbits : encodePreorder width h_width (PreToken.node ITag.tor :: toks')
      = [true, false, false] ++ encodePreorder width h_width toks' := by
    rw [encodePreorder_cons]
    rfl
  have henc_len : (encodePreorder width h_width (PreToken.node ITag.tor :: toks')).length
      = 3 + (encodePreorder width h_width toks').length := by
    rw [hbits, List.length_append]
    rfl
  have htail : 1 ≤ (encodePreorder width h_width toks').length := by
    obtain ⟨t, ts, rfl⟩ := List.exists_cons_of_ne_nil htoks'
    have hvt : ValidCertToken t := hvalid t (List.mem_cons_of_mem _ List.mem_cons_self)
    have h1t := validCertToken_one_le_length width h_width hvt
    rw [encodePreorder_cons, List.length_append]
    omega
  set CUR := z.certEnd - (encodePreorder width h_width (PreToken.node ITag.tor :: toks')).length
    with hCUR
  have hlen1 : 1 ≤ (encodeCtrlStackR st.ctrl).length := by
    unfold encodeCtrlStackR
    simp
  have hcap9 : z.ctrlBase + (encodeCtrlStackR st.ctrl).length + 9 ≤ z.ctrlEnd := by
    have := hcap
    simp only [encodeCtrlFrameR_length, ITag.arity, ITag.tagCode] at this
    omega
  set ctop := z.ctrlBase + (encodeCtrlStackR st.ctrl).length - 1 with hctop
  -- The cert window's tag cells, the marker, the control top.
  have hcell0 : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = CUR → c0.tape p = true := by
    intro p hp
    have := windowSpells_cell c0.tape _ _ hcert 0 (by omega) p (by omega)
    rw [this, hbits]
    rfl
  have hcell1 : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = CUR + 1 → c0.tape p = false := by
    intro p hp
    have := windowSpells_cell c0.tape _ _ hcert 1 (by omega) p (by omega)
    rw [this, hbits]
    rfl
  have hcell2 : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = CUR + 2 → c0.tape p = false := by
    intro p hp
    have := windowSpells_cell c0.tape _ _ hcert 2 (by omega) p (by omega)
    rw [this, hbits]
    rfl
  have htop : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = ctop → c0.tape p = true := by
    intro p hp
    have hcell := windowSpells_cell c0.tape z.ctrlBase (encodeCtrlStackR st.ctrl) hctrlw
      ((encodeCtrlStackR st.ctrl).length - 1) (by omega) p (by omega)
    rw [hcell]
    have hlast := encodeCtrlStackR_getLast_true st.ctrl
    rw [List.getLast?_eq_getElem?] at hlast
    rw [List.getD_eq_getElem?_getD, hlast]
    rfl
  -- Leg 1 (phases 0–1 → 2): step right onto the cursor.
  obtain ⟨hp1, hh1, ht1⟩ := nodeIter_region_stepRight.run_stepRight_hop c0 hphase (by omega)
  set c1 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c0 2 with hc1
  -- Leg 2 (phases 2–13 → 14): the tag trie, tor verdict (tff), landing past the tag.
  obtain ⟨hp2, hh2, ht2⟩ := nodeIter_region_certTrie.run_certTrie_or_hop
    (by rfl) (by rfl) (by rfl) (by rfl) c1 hp1 (by omega)
    (by rw [ht1]; exact hcell0 c1.head (by omega))
    (fun p hp => by rw [ht1]; exact hcell1 p (by omega))
    (fun p hp => by rw [ht1]; exact hcell2 p (by omega))
  set c2 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c1 4 with hc2
  -- Legs 3–6 (phases 14–21 → 22): four steps left, back onto the old marker.
  obtain ⟨hp3, hh3, ht3⟩ := nodeIter_region_Or_sL1.run_stepLeft_hop c2 hp2 (by omega)
  set c3 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c2 2 with hc3
  obtain ⟨hp4, hh4, ht4⟩ := nodeIter_region_Or_sL2.run_stepLeft_hop c3 hp3 (by omega)
  set c4 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c3 2 with hc4
  obtain ⟨hp5, hh5, ht5⟩ := nodeIter_region_Or_sL3.run_stepLeft_hop c4 hp4 (by omega)
  set c5 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c4 2 with hc5
  obtain ⟨hp6, hh6, ht6⟩ := nodeIter_region_Or_sL4.run_stepLeft_hop c5 hp5 (by omega)
  set c6 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c5 2 with hc6
  have hh6' : (c6.head : Nat) = CUR - 1 := by omega
  -- Leg 7 (phases 22–26 → 27): the marker-block rewrite from the old marker.
  obtain ⟨hp7, hh7, ht7⟩ := nodeIter_region_Or_mark.run_writeBits_hop c6 hp6
    (by simp only [nodeMarkBlock_length]; omega)
  set c7 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c6
    (nodeMarkBlock.length + 1) with hc7
  have ht7' : c7.tape = writeBlockTape c0.tape (CUR - 1) nodeMarkBlock := by
    rw [ht7, ht6, ht5, ht4, ht3, ht2, ht1, hh6']
  have hh7' : (c7.head : Nat) = CUR + 3 := by
    rw [hh7, hh6']
    simp only [nodeMarkBlock_length]
    omega
  -- The rewritten cursor area: zeros on [CUR − 1, CUR + 2), the new marker at CUR + 2.
  have h7low : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) < CUR - 1 → c7.tape p = c0.tape p := by
    intro p hp
    rw [ht7']
    exact writeBlockTape_below _ _ _ p hp
  have h7mark : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      CUR - 1 ≤ (p : Nat) → (p : Nat) < CUR + 2 → c7.tape p = false := by
    intro p hlo hhi
    rw [ht7']
    unfold writeBlockTape
    rw [if_pos (by simp only [nodeMarkBlock_length]; omega)]
    have h3 : (p : Nat) - (CUR - 1) = 0 ∨ (p : Nat) - (CUR - 1) = 1
        ∨ (p : Nat) - (CUR - 1) = 2 := by omega
    rcases h3 with h | h | h <;> rw [h] <;> rfl
  have h7anchor : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = CUR + 2 → c7.tape p = true := by
    intro p hp
    rw [ht7']
    unfold writeBlockTape
    rw [if_pos (by simp only [nodeMarkBlock_length]; omega),
      show (p : Nat) - (CUR - 1) = 3 from by omega]
    rfl
  -- Legs 8–9 (phases 27–30 → 31): two steps left off the new marker.
  obtain ⟨hp8, hh8, ht8⟩ := nodeIter_region_Or_sL5.run_stepLeft_hop c7 hp7 (by omega)
  set c8 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c7 2 with hc8
  obtain ⟨hp9, hh9, ht9⟩ := nodeIter_region_Or_sL6.run_stepLeft_hop c8 hp8 (by omega)
  set c9 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c8 2 with hc9
  -- Leg 10 (phases 31–32 → 33): scan left onto the control top.
  obtain ⟨hp10, hh10, ht10⟩ := nodeIter_region_Or_scanL.run_scanLeft_hop c9 hp9 ctop
    (by omega)
    (fun p hlo hhi => by
      rw [ht9, ht8]
      by_cases hp : (p : Nat) < CUR - 1
      · rw [h7low p hp]
        exact hcorr p (by omega) (by omega)
      · exact h7mark p (by omega) (by omega))
    (fun p hp => by
      rw [ht9, ht8, h7low p (by omega)]
      exact htop p hp)
  set c10 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c9
    (((c9.head : Nat) - ctop) + 2) with hc10
  -- Leg 11 (phases 33–34 → 35): step right onto the first free control cell.
  obtain ⟨hp11, hh11, ht11⟩ := nodeIter_region_Or_sR.run_stepRight_hop c10 hp10 (by omega)
  set c11 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c10 2 with hc11
  have hh11' : (c11.head : Nat) = z.ctrlBase + (encodeCtrlStackR st.ctrl).length := by omega
  -- Leg 12 (phases 35–41 → 112): the frame push at the control zone's right end.
  obtain ⟨hp12, hh12, ht12⟩ := nodeIter_region_Or_frame.run_writeBits_hop c11 hp11
    (by
      simp only [nodeFrame_length, ITag.arity, ITag.tagCode]
      omega)
  set c12 := TM.runConfig (M := nodeIterProgram.toPhased.toTM) c11
    ((nodeFrame ITag.tor).length + 1) with hc12
  have hh12' : (c12.head : Nat) = z.ctrlBase + (encodeCtrlStackR st.ctrl).length + 9 := by
    rw [hh12, hh11']
    simp only [nodeFrame_length, ITag.arity, ITag.tagCode]
  have ht12' : c12.tape = nodeStepTape c0.tape CUR
      (z.ctrlBase + (encodeCtrlStackR st.ctrl).length)
      (encodeCtrlFrameR (ITag.tor, ITag.tor.arity)) := by
    rw [ht12, ht11, ht10, ht9, ht8, hh11', ht7']
    exact writeMarkFrame_eq_nodeStepTape c0.tape CUR
      (z.ctrlBase + (encodeCtrlStackR st.ctrl).length) (nodeFrame ITag.tor) (by omega)
      (by simp only [nodeFrame_length, ITag.arity, ITag.tagCode]; omega)
  -- The transformed tape off the two written zones, for the return scan.
  have h12low : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      z.ctrlBase + (encodeCtrlStackR st.ctrl).length + 9 ≤ (p : Nat) →
      (p : Nat) < CUR - 1 → c12.tape p = false := by
    intro p hlo hhi
    rw [ht12']
    unfold nodeStepTape
    rw [if_neg (by omega), if_neg (by omega),
      if_neg (by
        simp only [encodeCtrlFrameR_length, ITag.arity, ITag.tagCode]
        omega)]
    exact hcorr p (by omega) (by omega)
  have h12mark : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      CUR - 1 ≤ (p : Nat) → (p : Nat) < CUR + 2 → c12.tape p = false := by
    intro p hlo hhi
    rw [ht12']
    unfold nodeStepTape
    rw [if_neg (by omega), if_pos ⟨hlo, hhi⟩]
  have h12anchor : ∀ p : Fin (nodeIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = CUR + 2 → c12.tape p = true := by
    intro p hp
    rw [ht12']
    unfold nodeStepTape
    rw [if_pos hp]
  -- Leg 13 (phases 112–113 → 114): scan right home onto the new marker.
  obtain ⟨hp13, hh13, ht13⟩ := nodeIter_region_scanRight.run_scanRight_hop c12 hp12
    ((CUR + 2) - (c12.head : Nat))
    (by omega)
    (fun p hlo hhi => by
      by_cases hp : (p : Nat) < CUR - 1
      · exact h12low p (by omega) hp
      · exact h12mark p (by omega) (by omega))
    (fun p hp => h12anchor p (by omega))
  -- Assemble the chain (right-nested junctions; each split is one controlled rewrite).
  have hfinal : TM.runConfig (M := nodeIterProgram.toPhased.toTM) c0
      (2 + (4 + (2 + (2 + (2 + (2 + ((nodeMarkBlock.length + 1) + (2 + (2
        + ((((c9.head : Nat) - ctop) + 2) + (2 + (((nodeFrame ITag.tor).length + 1)
          + (((CUR + 2) - (c12.head : Nat)) + 2)))))))))))))
      = TM.runConfig (M := nodeIterProgram.toPhased.toTM) c12
          (((CUR + 2) - (c12.head : Nat)) + 2) := by
    rw [TM.runConfig_add, ← hc1]
    rw [TM.runConfig_add, ← hc2]
    rw [TM.runConfig_add, ← hc3]
    rw [TM.runConfig_add, ← hc4]
    rw [TM.runConfig_add, ← hc5]
    rw [TM.runConfig_add, ← hc6]
    rw [TM.runConfig_add, ← hc7]
    rw [TM.runConfig_add, ← hc8]
    rw [TM.runConfig_add, ← hc9]
    rw [TM.runConfig_add, ← hc10]
    rw [TM.runConfig_add, ← hc11]
    rw [TM.runConfig_add, ← hc12]
  refine ⟨2 + (4 + (2 + (2 + (2 + (2 + ((nodeMarkBlock.length + 1) + (2 + (2
      + ((((c9.head : Nat) - ctop) + 2) + (2 + (((nodeFrame ITag.tor).length + 1)
        + (((CUR + 2) - (c12.head : Nat)) + 2)))))))))))),
    by
      simp only [nodeMarkBlock_length, nodeFrame_length, ITag.arity, ITag.tagCode]
      omega, ?_, ?_, ?_⟩
  · rw [hfinal, hp13]
  · rw [hfinal]
    omega
  · rw [hfinal, ht13]
    exact ht12'

end ContractExpansion
end Frontier
end Pnp4
