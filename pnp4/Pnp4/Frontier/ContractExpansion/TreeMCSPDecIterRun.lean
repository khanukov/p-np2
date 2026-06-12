import Pnp4.Frontier.ContractExpansion.TreeMCSPDecIterProgram

/-!
# The dec iteration, end to end (tnot) — D2t-5b (Block A5m-4, run)

The first **writing** arm run on a concrete U-stack machine: on `decIterProgram`, for a settling
state whose top control frame is `(tnot, 2)`, from the settle home the machine navigates to the
control top, reads the tag (two ones) and the remaining count (three ones — the dec verdict),
rewrites the frame in place with `decBlock tnot = encodeCtrlFrameR (tnot, 1) ++ [false]` from the
frame base, and scans home — ending at the home-read out with the head back on the marker and the
tape **exactly `corridorInv_decStep`'s transformer**.  The `tand`/`tor` runs mirror this one.

**Progress classification (AGENTS.md): Infrastructure** — a staging machine's end-to-end run;
proves no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.  **No
`P ≠ NP` claim.** -/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- **The dec iteration (tnot), end to end.**  For a settling state with top frame `(tnot, 2)`,
from the settle home, `decIterProgram` reaches the home-read out (phase `67`) with the head back on
the cursor marker and the tape exactly `corridorInv_decStep`'s transformer, within
`2 · certEnd + 30` steps. -/
theorem decIter_run_tnot {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (st : DriveState n) (rest : List (ITag × Nat))
    (c0 : Configuration (M := decIterProgram.toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z c0.tape st)
    (hctrl : st.ctrl = (ITag.tnot, 2) :: rest)
    (hphase : (c0.state.fst : Nat) = 0)
    (hhead : (c0.head : Nat) = z.certEnd - (encodePreorder width h_width st.toks).length - 1) :
    ∃ T : Nat, T ≤ 2 * z.certEnd + 30
      ∧ (((TM.runConfig (M := decIterProgram.toPhased.toTM) c0 T).state).fst : Nat) = 67
      ∧ ((TM.runConfig (M := decIterProgram.toPhased.toTM) c0 T).head : Nat)
          = z.certEnd - (encodePreorder width h_width st.toks).length - 1
      ∧ (TM.runConfig (M := decIterProgram.toPhased.toTM) c0 T).tape
          = writeBlockTape c0.tape (z.ctrlBase + (encodeCtrlStackR rest).length)
              (decBlock ITag.tnot) := by
  obtain ⟨hwf, hcert, hcfit, hmark, hcorr, hout, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrlw, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwf
  replace hmark : ∀ p : Fin (decIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = z.certEnd - (encodePreorder width h_width st.toks).length - 1 →
      c0.tape p = true := hmark
  replace hcorr : ∀ p : Fin (decIterProgram.toPhased.toTM.tapeLength L),
      z.ctrlBase + (encodeCtrlStackR st.ctrl).length ≤ (p : Nat) →
      (p : Nat) < z.certEnd - (encodePreorder width h_width st.toks).length - 1 →
      c0.tape p = false := hcorr
  replace hctrlw : windowSpells c0.tape z.ctrlBase (encodeCtrlStackR st.ctrl) := hctrlw
  replace hcfit2 : z.ctrlBase + (encodeCtrlStackR st.ctrl).length ≤ z.ctrlEnd := hcfit2
  replace hcfit : z.certBase + (encodePreorder width h_width st.toks).length ≤ z.certEnd := hcfit
  rw [hctrl] at hctrlw hcorr hcfit2
  set M := z.certEnd - (encodePreorder width h_width st.toks).length - 1 with hM
  -- Geometry: the encoded-stack length, the top, the separator, the frame base.
  have hlen_ctrl : (encodeCtrlStackR ((ITag.tnot, 2) :: rest)).length
      = (encodeCtrlStackR rest).length + 7 := by
    rw [encodeCtrlStackR_cons, List.length_append, encodeCtrlFrameR_length]
    simp [ITag.tagCode]
  set top := z.ctrlBase + (encodeCtrlStackR ((ITag.tnot, 2) :: rest)).length - 1 with htopdef
  have hMlow : z.certBase - 1 ≤ M := by omega
  have htopM : top + 1 < M := by omega
  -- Cells of the top frame, off the control window.
  have hcell : ∀ (i : Nat) (p : Fin (decIterProgram.toPhased.toTM.tapeLength L)),
      i < (encodeCtrlStackR ((ITag.tnot, 2) :: rest)).length →
      (p : Nat) = z.ctrlBase + ((encodeCtrlStackR ((ITag.tnot, 2) :: rest)).length - 1 - i) →
      c0.tape p = (encodeCtrlStackR ((ITag.tnot, 2) :: rest)).getD
        ((encodeCtrlStackR ((ITag.tnot, 2) :: rest)).length - 1 - i) false := by
    intro i p hi hp
    exact windowSpells_cell c0.tape z.ctrlBase _ hctrlw _ (by omega) p hp
  have htag0 : ∀ p : Fin (decIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = top → c0.tape p = true := by
    intro p hp
    rw [hcell 0 p (by omega) (by omega)]
    exact encodeCtrlStackR_tagBlock_true ITag.tnot 2 rest 0 (by simp [ITag.tagCode])
  have htag1 : ∀ p : Fin (decIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = top - 1 → c0.tape p = true := by
    intro p hp
    rw [hcell 1 p (by omega) (by omega)]
    exact encodeCtrlStackR_tagBlock_true ITag.tnot 2 rest 1 (by simp [ITag.tagCode])
  have hsep : ∀ p : Fin (decIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = top - 2 → c0.tape p = false := by
    intro p hp
    rw [hcell 2 p (by omega) (by omega)]
    have h := encodeCtrlStackR_tagSep_false ITag.tnot 2 rest
    rw [show (encodeCtrlStackR ((ITag.tnot, 2) :: rest)).length - 1 - (ITag.tnot.tagCode + 2)
        = (encodeCtrlStackR ((ITag.tnot, 2) :: rest)).length - 1 - 2 from by
      simp [ITag.tagCode]] at h
    exact h
  have hrem : ∀ (i : Nat) (p : Fin (decIterProgram.toPhased.toTM.tapeLength L)), i < 3 →
      (p : Nat) = top - 3 - i → c0.tape p = true := by
    intro i p hi hp
    rw [hcell (3 + i) p (by omega) (by omega)]
    have h := encodeCtrlStackR_remBlock_true ITag.tnot 2 rest i (by omega)
    rw [show (encodeCtrlStackR ((ITag.tnot, 2) :: rest)).length - 1 - (ITag.tnot.tagCode + 2)
          - 1 - i
        = (encodeCtrlStackR ((ITag.tnot, 2) :: rest)).length - 1 - (3 + i) from by
      simp only [ITag.tagCode]
      omega] at h
    exact h
  have hbase : ∀ p : Fin (decIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = top - 6 → c0.tape p = false := by
    intro p hp
    rw [hcell 6 p (by omega) (by omega)]
    have h := encodeCtrlStackR_frameBase_false ITag.tnot 2 rest
    rw [show (encodeCtrlStackR ((ITag.tnot, 2) :: rest)).length - 1 - (ITag.tnot.tagCode + 2)
          - 1 - (2 + 1)
        = (encodeCtrlStackR ((ITag.tnot, 2) :: rest)).length - 1 - 6 from by
      simp only [ITag.tagCode]
      omega] at h
    exact h
  have hcfb : top - 6 = z.ctrlBase + (encodeCtrlStackR rest).length := by omega
  -- Leg 1: step left off the marker (phases 0–1 → 2).
  obtain ⟨hp1, hh1, ht1⟩ := decIter_region_stepLeft.run_stepLeft_hop c0 hphase (by omega)
  set c1 := TM.runConfig (M := decIterProgram.toPhased.toTM) c0 2 with hc1
  -- Leg 2: scan left onto the control top (phases 2–3 → 4).
  obtain ⟨hp2, hh2, ht2⟩ := decIter_region_scanLeft.run_scanLeft_hop c1 hp1 top
    (by omega)
    (fun p hlo hhi => by
      rw [ht1]
      exact hcorr p (by omega) (by omega))
    (fun p hp => by rw [ht1]; exact htag0 p hp)
  set c2 := TM.runConfig (M := decIterProgram.toPhased.toTM) c1
    (((c1.head : Nat) - top) + 2) with hc2
  -- Leg 3: the tag read, tnot verdict (phases 4–13 → 14), landing on the separator.
  obtain ⟨hp3, hh3, ht3⟩ := decIter_region_ctrlTopWalk.run_ctrlTop_tnot_hop
    (by rfl) (by rfl) (by rfl) (by rfl) c2 hp2 (by omega)
    (fun p hp => by rw [ht2, ht1]; exact htag1 p (by omega))
    (fun p hp => by rw [ht2, ht1]; exact hsep p (by omega))
  set c3 := TM.runConfig (M := decIterProgram.toPhased.toTM) c2 4 with hc3
  -- Leg 4: the rem read, dec verdict (phases 14–21 → 38), landing on the frame base.
  obtain ⟨hp4, hh4, ht4⟩ := decIter_region_remWalkNot.run_rem_dec_hop
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) c3 hp3 (by omega)
    (fun p hp => by rw [ht3, ht2, ht1]; exact hrem 0 p (by omega) (by omega))
    (fun p hp => by rw [ht3, ht2, ht1]; exact hrem 1 p (by omega) (by omega))
    (fun p hp => by rw [ht3, ht2, ht1]; exact hrem 2 p (by omega) (by omega))
    (fun p hp => by rw [ht3, ht2, ht1]; exact hbase p (by omega))
  set c4 := TM.runConfig (M := decIterProgram.toPhased.toTM) c3 6 with hc4
  -- Leg 5: the in-place frame rewrite (phases 38–45 → 65).
  have hh4' : (c4.head : Nat) = top - 6 := by omega
  obtain ⟨hp5, hh5, ht5⟩ := decIter_region_writeNot.run_writeBits_hop c4 hp4
    (by
      have hfit2 : z.ctrlBase + (encodeCtrlStackR ((ITag.tnot, 2) :: rest)).length
          ≤ z.ctrlEnd := by omega
      have := c0.head.isLt
      simp only [decBlock_length, ITag.tagCode]
      omega)
  set c5 := TM.runConfig (M := decIterProgram.toPhased.toTM) c4
    ((decBlock ITag.tnot).length + 1) with hc5
  have hh5' : (c5.head : Nat)
      = z.ctrlBase + (encodeCtrlStackR ((ITag.tnot, 2) :: rest)).length := by
    rw [hh5, hh4']
    simp only [decBlock_length, ITag.tagCode]
    omega
  have ht5' : c5.tape = writeBlockTape c0.tape (z.ctrlBase + (encodeCtrlStackR rest).length)
      (decBlock ITag.tnot) := by
    rw [ht5, ht4, ht3, ht2, ht1, hh4', hcfb]
  -- Leg 6: scan right home onto the marker (phases 65–66 → 67).
  obtain ⟨hp6, hh6, ht6⟩ := decIter_region_scanRight.run_scanRight_hop c5 hp5
    (M - (z.ctrlBase + (encodeCtrlStackR ((ITag.tnot, 2) :: rest)).length))
    (by
      have := c0.head.isLt
      omega)
    (fun p hlo hhi => by
      rw [ht5']
      rw [writeBlockTape_above _ _ _ p (by
        simp only [decBlock_length, ITag.tagCode]
        omega)]
      exact hcorr p (by omega) (by omega))
    (fun p hp => by
      rw [ht5']
      rw [writeBlockTape_above _ _ _ p (by
        simp only [decBlock_length, ITag.tagCode]
        omega)]
      exact hmark p (by omega))
  -- Assemble.
  have hfinal : TM.runConfig (M := decIterProgram.toPhased.toTM) c0
      (2 + ((((c1.head : Nat) - top) + 2) + (4 + (6 + (((decBlock ITag.tnot).length + 1)
        + ((M - (z.ctrlBase + (encodeCtrlStackR ((ITag.tnot, 2) :: rest)).length)) + 2))))))
      = TM.runConfig (M := decIterProgram.toPhased.toTM) c5 ((M - (z.ctrlBase + (encodeCtrlStackR ((ITag.tnot, 2) :: rest)).length)) + 2) := by
    rw [TM.runConfig_add, ← hc1]
    rw [TM.runConfig_add, ← hc2]
    rw [TM.runConfig_add, ← hc3]
    rw [TM.runConfig_add, ← hc4]
    rw [TM.runConfig_add, ← hc5]
  refine ⟨2 + ((((c1.head : Nat) - top) + 2) + (4 + (6 + (((decBlock ITag.tnot).length + 1)
      + ((M - (z.ctrlBase + (encodeCtrlStackR ((ITag.tnot, 2) :: rest)).length)) + 2))))),
    by
      have := c0.head.isLt
      simp only [decBlock_length, ITag.tagCode]
      omega, ?_, ?_, ?_⟩
  · rw [hfinal, hp6]
  · rw [hfinal]
    omega
  · rw [hfinal, ht6, ht5']



/-- **The dec iteration (tand), end to end** — the `tand` mirror of `decIter_run_tnot`. -/
theorem decIter_run_tand {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (st : DriveState n) (rest : List (ITag × Nat))
    (c0 : Configuration (M := decIterProgram.toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z c0.tape st)
    (hctrl : st.ctrl = (ITag.tand, 2) :: rest)
    (hphase : (c0.state.fst : Nat) = 0)
    (hhead : (c0.head : Nat) = z.certEnd - (encodePreorder width h_width st.toks).length - 1) :
    ∃ T : Nat, T ≤ 2 * z.certEnd + 30
      ∧ (((TM.runConfig (M := decIterProgram.toPhased.toTM) c0 T).state).fst : Nat) = 67
      ∧ ((TM.runConfig (M := decIterProgram.toPhased.toTM) c0 T).head : Nat)
          = z.certEnd - (encodePreorder width h_width st.toks).length - 1
      ∧ (TM.runConfig (M := decIterProgram.toPhased.toTM) c0 T).tape
          = writeBlockTape c0.tape (z.ctrlBase + (encodeCtrlStackR rest).length)
              (decBlock ITag.tand) := by
  obtain ⟨hwf, hcert, hcfit, hmark, hcorr, hout, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrlw, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwf
  replace hmark : ∀ p : Fin (decIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = z.certEnd - (encodePreorder width h_width st.toks).length - 1 →
      c0.tape p = true := hmark
  replace hcorr : ∀ p : Fin (decIterProgram.toPhased.toTM.tapeLength L),
      z.ctrlBase + (encodeCtrlStackR st.ctrl).length ≤ (p : Nat) →
      (p : Nat) < z.certEnd - (encodePreorder width h_width st.toks).length - 1 →
      c0.tape p = false := hcorr
  replace hctrlw : windowSpells c0.tape z.ctrlBase (encodeCtrlStackR st.ctrl) := hctrlw
  replace hcfit2 : z.ctrlBase + (encodeCtrlStackR st.ctrl).length ≤ z.ctrlEnd := hcfit2
  replace hcfit : z.certBase + (encodePreorder width h_width st.toks).length ≤ z.certEnd := hcfit
  rw [hctrl] at hctrlw hcorr hcfit2
  set M := z.certEnd - (encodePreorder width h_width st.toks).length - 1 with hM
  have hlen_ctrl : (encodeCtrlStackR ((ITag.tand, 2) :: rest)).length
      = (encodeCtrlStackR rest).length + 8 := by
    rw [encodeCtrlStackR_cons, List.length_append, encodeCtrlFrameR_length]
    simp [ITag.tagCode]
  set top := z.ctrlBase + (encodeCtrlStackR ((ITag.tand, 2) :: rest)).length - 1 with htopdef
  have hMlow : z.certBase - 1 ≤ M := by omega
  have htopM : top + 1 < M := by omega
  have hcell : ∀ (i : Nat) (p : Fin (decIterProgram.toPhased.toTM.tapeLength L)),
      i < (encodeCtrlStackR ((ITag.tand, 2) :: rest)).length →
      (p : Nat) = z.ctrlBase + ((encodeCtrlStackR ((ITag.tand, 2) :: rest)).length - 1 - i) →
      c0.tape p = (encodeCtrlStackR ((ITag.tand, 2) :: rest)).getD
        ((encodeCtrlStackR ((ITag.tand, 2) :: rest)).length - 1 - i) false := by
    intro i p hi hp
    exact windowSpells_cell c0.tape z.ctrlBase _ hctrlw _ (by omega) p hp
  have htag0 : ∀ p : Fin (decIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = top - 0 → c0.tape p = true := by
    intro p hp
    rw [hcell 0 p (by omega) (by omega)]
    exact encodeCtrlStackR_tagBlock_true ITag.tand 2 rest 0 (by simp [ITag.tagCode])
  have htag1 : ∀ p : Fin (decIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = top - 1 → c0.tape p = true := by
    intro p hp
    rw [hcell 1 p (by omega) (by omega)]
    exact encodeCtrlStackR_tagBlock_true ITag.tand 2 rest 1 (by simp [ITag.tagCode])
  have htag2 : ∀ p : Fin (decIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = top - 2 → c0.tape p = true := by
    intro p hp
    rw [hcell 2 p (by omega) (by omega)]
    exact encodeCtrlStackR_tagBlock_true ITag.tand 2 rest 2 (by simp [ITag.tagCode])
  have hsep : ∀ p : Fin (decIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = top - 3 → c0.tape p = false := by
    intro p hp
    rw [hcell 3 p (by omega) (by omega)]
    have h := encodeCtrlStackR_tagSep_false ITag.tand 2 rest
    rw [show (encodeCtrlStackR ((ITag.tand, 2) :: rest)).length - 1 - (ITag.tand.tagCode + 2)
        = (encodeCtrlStackR ((ITag.tand, 2) :: rest)).length - 1 - 3 from by
      simp only [ITag.tagCode]] at h
    exact h
  have hrem : ∀ (i : Nat) (p : Fin (decIterProgram.toPhased.toTM.tapeLength L)), i < 3 →
      (p : Nat) = top - 4 - i → c0.tape p = true := by
    intro i p hi hp
    rw [hcell (4 + i) p (by omega) (by omega)]
    have h := encodeCtrlStackR_remBlock_true ITag.tand 2 rest i (by omega)
    rw [show (encodeCtrlStackR ((ITag.tand, 2) :: rest)).length - 1 - (ITag.tand.tagCode + 2)
          - 1 - i
        = (encodeCtrlStackR ((ITag.tand, 2) :: rest)).length - 1 - (4 + i) from by
      simp only [ITag.tagCode]
      omega] at h
    exact h
  have hbase : ∀ p : Fin (decIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = top - 7 → c0.tape p = false := by
    intro p hp
    rw [hcell 7 p (by omega) (by omega)]
    have h := encodeCtrlStackR_frameBase_false ITag.tand 2 rest
    rw [show (encodeCtrlStackR ((ITag.tand, 2) :: rest)).length - 1 - (ITag.tand.tagCode + 2)
          - 1 - (2 + 1)
        = (encodeCtrlStackR ((ITag.tand, 2) :: rest)).length - 1 - 7 from by
      simp only [ITag.tagCode]
      omega] at h
    exact h
  have hcfb : top - 7 = z.ctrlBase + (encodeCtrlStackR rest).length := by omega
  obtain ⟨hp1, hh1, ht1⟩ := decIter_region_stepLeft.run_stepLeft_hop c0 hphase (by omega)
  set c1 := TM.runConfig (M := decIterProgram.toPhased.toTM) c0 2 with hc1
  obtain ⟨hp2, hh2, ht2⟩ := decIter_region_scanLeft.run_scanLeft_hop c1 hp1 top
    (by omega)
    (fun p hlo hhi => by
      rw [ht1]
      exact hcorr p (by omega) (by omega))
    (fun p hp => by rw [ht1]; exact htag0 p hp)
  set c2 := TM.runConfig (M := decIterProgram.toPhased.toTM) c1
    (((c1.head : Nat) - top) + 2) with hc2
  obtain ⟨hp3, hh3, ht3⟩ := decIter_region_ctrlTopWalk.run_ctrlTop_tand_hop
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) c2 hp2 (by omega)
    (fun p hp => by rw [ht2, ht1]; exact htag1 p (by omega))
    (fun p hp => by rw [ht2, ht1]; exact htag2 p (by omega))
    (fun p hp => by rw [ht2, ht1]; exact hsep p (by omega))
  set c3 := TM.runConfig (M := decIterProgram.toPhased.toTM) c2 5 with hc3
  obtain ⟨hp4, hh4, ht4⟩ := decIter_region_remWalkAnd.run_rem_dec_hop
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) c3 hp3 (by omega)
    (fun p hp => by rw [ht3, ht2, ht1]; exact hrem 0 p (by omega) (by omega))
    (fun p hp => by rw [ht3, ht2, ht1]; exact hrem 1 p (by omega) (by omega))
    (fun p hp => by rw [ht3, ht2, ht1]; exact hrem 2 p (by omega) (by omega))
    (fun p hp => by rw [ht3, ht2, ht1]; exact hbase p (by omega))
  set c4 := TM.runConfig (M := decIterProgram.toPhased.toTM) c3 6 with hc4
  have hh4' : (c4.head : Nat) = top - 7 := by omega
  obtain ⟨hp5, hh5, ht5⟩ := decIter_region_writeAnd.run_writeBits_hop c4 hp4
    (by
      have hfit2 : z.ctrlBase + (encodeCtrlStackR ((ITag.tand, 2) :: rest)).length
          ≤ z.ctrlEnd := by omega
      have := c0.head.isLt
      simp only [decBlock_length, ITag.tagCode]
      omega)
  set c5 := TM.runConfig (M := decIterProgram.toPhased.toTM) c4
    ((decBlock ITag.tand).length + 1) with hc5
  have hh5' : (c5.head : Nat)
      = z.ctrlBase + (encodeCtrlStackR ((ITag.tand, 2) :: rest)).length := by
    rw [hh5, hh4']
    simp only [decBlock_length, ITag.tagCode]
    omega
  have ht5' : c5.tape = writeBlockTape c0.tape (z.ctrlBase + (encodeCtrlStackR rest).length)
      (decBlock ITag.tand) := by
    rw [ht5, ht4, ht3, ht2, ht1, hh4', hcfb]
  obtain ⟨hp6, hh6, ht6⟩ := decIter_region_scanRight.run_scanRight_hop c5 hp5
    (M - (z.ctrlBase + (encodeCtrlStackR ((ITag.tand, 2) :: rest)).length))
    (by
      have := c0.head.isLt
      omega)
    (fun p hlo hhi => by
      rw [ht5']
      rw [writeBlockTape_above _ _ _ p (by
        simp only [decBlock_length, ITag.tagCode]
        omega)]
      exact hcorr p (by omega) (by omega))
    (fun p hp => by
      rw [ht5']
      rw [writeBlockTape_above _ _ _ p (by
        simp only [decBlock_length, ITag.tagCode]
        omega)]
      exact hmark p (by omega))
  have hfinal : TM.runConfig (M := decIterProgram.toPhased.toTM) c0
      (2 + ((((c1.head : Nat) - top) + 2) + (5 + (6 + (((decBlock ITag.tand).length + 1)
        + ((M - (z.ctrlBase + (encodeCtrlStackR ((ITag.tand, 2) :: rest)).length)) + 2))))))
      = TM.runConfig (M := decIterProgram.toPhased.toTM) c5
          ((M - (z.ctrlBase + (encodeCtrlStackR ((ITag.tand, 2) :: rest)).length)) + 2) := by
    rw [TM.runConfig_add, ← hc1]
    rw [TM.runConfig_add, ← hc2]
    rw [TM.runConfig_add, ← hc3]
    rw [TM.runConfig_add, ← hc4]
    rw [TM.runConfig_add, ← hc5]
  refine ⟨2 + ((((c1.head : Nat) - top) + 2) + (5 + (6 + (((decBlock ITag.tand).length + 1)
      + ((M - (z.ctrlBase + (encodeCtrlStackR ((ITag.tand, 2) :: rest)).length)) + 2))))),
    by
      have := c0.head.isLt
      simp only [decBlock_length, ITag.tagCode]
      omega, ?_, ?_, ?_⟩
  · rw [hfinal, hp6]
  · rw [hfinal]
    omega
  · rw [hfinal, ht6, ht5']


/-- **The dec iteration (tor), end to end** — the `tor` mirror of `decIter_run_tnot`. -/
theorem decIter_run_tor {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (st : DriveState n) (rest : List (ITag × Nat))
    (c0 : Configuration (M := decIterProgram.toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z c0.tape st)
    (hctrl : st.ctrl = (ITag.tor, 2) :: rest)
    (hphase : (c0.state.fst : Nat) = 0)
    (hhead : (c0.head : Nat) = z.certEnd - (encodePreorder width h_width st.toks).length - 1) :
    ∃ T : Nat, T ≤ 2 * z.certEnd + 30
      ∧ (((TM.runConfig (M := decIterProgram.toPhased.toTM) c0 T).state).fst : Nat) = 67
      ∧ ((TM.runConfig (M := decIterProgram.toPhased.toTM) c0 T).head : Nat)
          = z.certEnd - (encodePreorder width h_width st.toks).length - 1
      ∧ (TM.runConfig (M := decIterProgram.toPhased.toTM) c0 T).tape
          = writeBlockTape c0.tape (z.ctrlBase + (encodeCtrlStackR rest).length)
              (decBlock ITag.tor) := by
  obtain ⟨hwf, hcert, hcfit, hmark, hcorr, hout, hFM, hffit, hfzeros, hval, hvfit, hvzeros,
    hshw, hsfit, hszeros, hctrlw, hcfit2, hvalid, hcoh⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hwf
  replace hmark : ∀ p : Fin (decIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = z.certEnd - (encodePreorder width h_width st.toks).length - 1 →
      c0.tape p = true := hmark
  replace hcorr : ∀ p : Fin (decIterProgram.toPhased.toTM.tapeLength L),
      z.ctrlBase + (encodeCtrlStackR st.ctrl).length ≤ (p : Nat) →
      (p : Nat) < z.certEnd - (encodePreorder width h_width st.toks).length - 1 →
      c0.tape p = false := hcorr
  replace hctrlw : windowSpells c0.tape z.ctrlBase (encodeCtrlStackR st.ctrl) := hctrlw
  replace hcfit2 : z.ctrlBase + (encodeCtrlStackR st.ctrl).length ≤ z.ctrlEnd := hcfit2
  replace hcfit : z.certBase + (encodePreorder width h_width st.toks).length ≤ z.certEnd := hcfit
  rw [hctrl] at hctrlw hcorr hcfit2
  set M := z.certEnd - (encodePreorder width h_width st.toks).length - 1 with hM
  have hlen_ctrl : (encodeCtrlStackR ((ITag.tor, 2) :: rest)).length
      = (encodeCtrlStackR rest).length + 9 := by
    rw [encodeCtrlStackR_cons, List.length_append, encodeCtrlFrameR_length]
    simp [ITag.tagCode]
  set top := z.ctrlBase + (encodeCtrlStackR ((ITag.tor, 2) :: rest)).length - 1 with htopdef
  have hMlow : z.certBase - 1 ≤ M := by omega
  have htopM : top + 1 < M := by omega
  have hcell : ∀ (i : Nat) (p : Fin (decIterProgram.toPhased.toTM.tapeLength L)),
      i < (encodeCtrlStackR ((ITag.tor, 2) :: rest)).length →
      (p : Nat) = z.ctrlBase + ((encodeCtrlStackR ((ITag.tor, 2) :: rest)).length - 1 - i) →
      c0.tape p = (encodeCtrlStackR ((ITag.tor, 2) :: rest)).getD
        ((encodeCtrlStackR ((ITag.tor, 2) :: rest)).length - 1 - i) false := by
    intro i p hi hp
    exact windowSpells_cell c0.tape z.ctrlBase _ hctrlw _ (by omega) p hp
  have htag0 : ∀ p : Fin (decIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = top - 0 → c0.tape p = true := by
    intro p hp
    rw [hcell 0 p (by omega) (by omega)]
    exact encodeCtrlStackR_tagBlock_true ITag.tor 2 rest 0 (by simp [ITag.tagCode])
  have htag1 : ∀ p : Fin (decIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = top - 1 → c0.tape p = true := by
    intro p hp
    rw [hcell 1 p (by omega) (by omega)]
    exact encodeCtrlStackR_tagBlock_true ITag.tor 2 rest 1 (by simp [ITag.tagCode])
  have htag2 : ∀ p : Fin (decIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = top - 2 → c0.tape p = true := by
    intro p hp
    rw [hcell 2 p (by omega) (by omega)]
    exact encodeCtrlStackR_tagBlock_true ITag.tor 2 rest 2 (by simp [ITag.tagCode])
  have htag3 : ∀ p : Fin (decIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = top - 3 → c0.tape p = true := by
    intro p hp
    rw [hcell 3 p (by omega) (by omega)]
    exact encodeCtrlStackR_tagBlock_true ITag.tor 2 rest 3 (by simp [ITag.tagCode])
  have hsep : ∀ p : Fin (decIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = top - 4 → c0.tape p = false := by
    intro p hp
    rw [hcell 4 p (by omega) (by omega)]
    have h := encodeCtrlStackR_tagSep_false ITag.tor 2 rest
    rw [show (encodeCtrlStackR ((ITag.tor, 2) :: rest)).length - 1 - (ITag.tor.tagCode + 2)
        = (encodeCtrlStackR ((ITag.tor, 2) :: rest)).length - 1 - 4 from by
      simp only [ITag.tagCode]] at h
    exact h
  have hrem : ∀ (i : Nat) (p : Fin (decIterProgram.toPhased.toTM.tapeLength L)), i < 3 →
      (p : Nat) = top - 5 - i → c0.tape p = true := by
    intro i p hi hp
    rw [hcell (5 + i) p (by omega) (by omega)]
    have h := encodeCtrlStackR_remBlock_true ITag.tor 2 rest i (by omega)
    rw [show (encodeCtrlStackR ((ITag.tor, 2) :: rest)).length - 1 - (ITag.tor.tagCode + 2)
          - 1 - i
        = (encodeCtrlStackR ((ITag.tor, 2) :: rest)).length - 1 - (5 + i) from by
      simp only [ITag.tagCode]
      omega] at h
    exact h
  have hbase : ∀ p : Fin (decIterProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = top - 8 → c0.tape p = false := by
    intro p hp
    rw [hcell 8 p (by omega) (by omega)]
    have h := encodeCtrlStackR_frameBase_false ITag.tor 2 rest
    rw [show (encodeCtrlStackR ((ITag.tor, 2) :: rest)).length - 1 - (ITag.tor.tagCode + 2)
          - 1 - (2 + 1)
        = (encodeCtrlStackR ((ITag.tor, 2) :: rest)).length - 1 - 8 from by
      simp only [ITag.tagCode]
      omega] at h
    exact h
  have hcfb : top - 8 = z.ctrlBase + (encodeCtrlStackR rest).length := by omega
  obtain ⟨hp1, hh1, ht1⟩ := decIter_region_stepLeft.run_stepLeft_hop c0 hphase (by omega)
  set c1 := TM.runConfig (M := decIterProgram.toPhased.toTM) c0 2 with hc1
  obtain ⟨hp2, hh2, ht2⟩ := decIter_region_scanLeft.run_scanLeft_hop c1 hp1 top
    (by omega)
    (fun p hlo hhi => by
      rw [ht1]
      exact hcorr p (by omega) (by omega))
    (fun p hp => by rw [ht1]; exact htag0 p hp)
  set c2 := TM.runConfig (M := decIterProgram.toPhased.toTM) c1
    (((c1.head : Nat) - top) + 2) with hc2
  obtain ⟨hp3, hh3, ht3⟩ := decIter_region_ctrlTopWalk.run_ctrlTop_tor_hop
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) c2 hp2 (by omega)
    (fun p hp => by rw [ht2, ht1]; exact htag1 p (by omega))
    (fun p hp => by rw [ht2, ht1]; exact htag2 p (by omega))
    (fun p hp => by rw [ht2, ht1]; exact htag3 p (by omega))
    (fun p hp => by rw [ht2, ht1]; exact hsep p (by omega))
  set c3 := TM.runConfig (M := decIterProgram.toPhased.toTM) c2 6 with hc3
  obtain ⟨hp4, hh4, ht4⟩ := decIter_region_remWalkOr.run_rem_dec_hop
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) c3 hp3 (by omega)
    (fun p hp => by rw [ht3, ht2, ht1]; exact hrem 0 p (by omega) (by omega))
    (fun p hp => by rw [ht3, ht2, ht1]; exact hrem 1 p (by omega) (by omega))
    (fun p hp => by rw [ht3, ht2, ht1]; exact hrem 2 p (by omega) (by omega))
    (fun p hp => by rw [ht3, ht2, ht1]; exact hbase p (by omega))
  set c4 := TM.runConfig (M := decIterProgram.toPhased.toTM) c3 6 with hc4
  have hh4' : (c4.head : Nat) = top - 8 := by omega
  obtain ⟨hp5, hh5, ht5⟩ := decIter_region_writeOr.run_writeBits_hop c4 hp4
    (by
      have hfit2 : z.ctrlBase + (encodeCtrlStackR ((ITag.tor, 2) :: rest)).length
          ≤ z.ctrlEnd := by omega
      have := c0.head.isLt
      simp only [decBlock_length, ITag.tagCode]
      omega)
  set c5 := TM.runConfig (M := decIterProgram.toPhased.toTM) c4
    ((decBlock ITag.tor).length + 1) with hc5
  have hh5' : (c5.head : Nat)
      = z.ctrlBase + (encodeCtrlStackR ((ITag.tor, 2) :: rest)).length := by
    rw [hh5, hh4']
    simp only [decBlock_length, ITag.tagCode]
    omega
  have ht5' : c5.tape = writeBlockTape c0.tape (z.ctrlBase + (encodeCtrlStackR rest).length)
      (decBlock ITag.tor) := by
    rw [ht5, ht4, ht3, ht2, ht1, hh4', hcfb]
  obtain ⟨hp6, hh6, ht6⟩ := decIter_region_scanRight.run_scanRight_hop c5 hp5
    (M - (z.ctrlBase + (encodeCtrlStackR ((ITag.tor, 2) :: rest)).length))
    (by
      have := c0.head.isLt
      omega)
    (fun p hlo hhi => by
      rw [ht5']
      rw [writeBlockTape_above _ _ _ p (by
        simp only [decBlock_length, ITag.tagCode]
        omega)]
      exact hcorr p (by omega) (by omega))
    (fun p hp => by
      rw [ht5']
      rw [writeBlockTape_above _ _ _ p (by
        simp only [decBlock_length, ITag.tagCode]
        omega)]
      exact hmark p (by omega))
  have hfinal : TM.runConfig (M := decIterProgram.toPhased.toTM) c0
      (2 + ((((c1.head : Nat) - top) + 2) + (6 + (6 + (((decBlock ITag.tor).length + 1)
        + ((M - (z.ctrlBase + (encodeCtrlStackR ((ITag.tor, 2) :: rest)).length)) + 2))))))
      = TM.runConfig (M := decIterProgram.toPhased.toTM) c5
          ((M - (z.ctrlBase + (encodeCtrlStackR ((ITag.tor, 2) :: rest)).length)) + 2) := by
    rw [TM.runConfig_add, ← hc1]
    rw [TM.runConfig_add, ← hc2]
    rw [TM.runConfig_add, ← hc3]
    rw [TM.runConfig_add, ← hc4]
    rw [TM.runConfig_add, ← hc5]
  refine ⟨2 + ((((c1.head : Nat) - top) + 2) + (6 + (6 + (((decBlock ITag.tor).length + 1)
      + ((M - (z.ctrlBase + (encodeCtrlStackR ((ITag.tor, 2) :: rest)).length)) + 2))))),
    by
      have := c0.head.isLt
      simp only [decBlock_length, ITag.tagCode]
      omega, ?_, ?_, ?_⟩
  · rw [hfinal, hp6]
  · rw [hfinal]
    omega
  · rw [hfinal, ht6, ht5']

end ContractExpansion
end Frontier
end Pnp4
