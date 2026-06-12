import Pnp4.Frontier.ContractExpansion.TreeMCSPCorridorLeafLast
import Pnp4.Frontier.ContractExpansion.TreeMCSPCorridorNodeStep
import Pnp4.Frontier.ContractExpansion.TreeMCSPCorridorSettleClear

/-!
# `driverStepTape` — D2t-5b (Block A5b): the total one-step tape dispatcher

The per-branch corridor keystones (Block A4 + the A5a gap-fillers) each say: *given the right bounded
tape rewrite, `driverCorridorInv` is preserved across one specific `DriveState.step` branch*.  This
module assembles them into a single **total** statement, the exact shape the on-tape loop's invariant
induction consumes:

* `driverStepTape` — the total tape transformer: by cases on the abstract state's branch (mirroring
  `DriveState.step`'s match structure), the tape rewrite that branch's machine arm performs — the
  settle-emit `popStepTape`, the settle-decrement frame rewrite, the leaf `leafStepTape`, the node
  `nodeStepTape`, and the identity on the flag-only / terminal branches.
* `DriverStepFits` — the branch's capacity side conditions (output / WORK / value-zone room for the
  write branches, frame room and tail-nonemptiness for the node branch), to be discharged later from
  the zone sizing and reachable-state bounds.
* `corridorInv_driverStep` — **the one-step dispatcher keystone**: for every state,
  `driverCorridorInv` is preserved from `st` to `st.step` across `driverStepTape`.  The degenerate
  branches (operand underflow, `rem = 0`) ride `corridorInv_clearFlag`; invalid leaf tokens are
  refuted from the invariant's `ValidCertTokens` clause.

This is the *semantic* half of the A5 loop discharge: it fixes, for each branch, the exact tape map
the machine arm must realise, and proves the invariant transport once and for all.  The machine half
(arms as composed `ConstStatePhasedProgram`s whose run equals `driverStepTape`, head/phase tracking,
`reachesSink`) remains separate.

**Progress classification (AGENTS.md): Infrastructure** — tape-level invariant plumbing over the
verified keystones; builds no machine and proves no separation.  Standard `[propext,
Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- **The total one-step tape transformer.**  By cases on the state's `DriveState.step` branch, the
tape rewrite that branch's machine arm performs; identity on the branches that only flip the
`settling` flag (empty control stack, operand underflow, `rem = 0`) or idle (terminal).  Every
**emit** branch (leaf read, settle-pop) additionally performs the **shadow-count tick**: one `1`
appended at the SHW window's right end (`shwBase + |out| + 1`), keeping `SHW` spelling
`1^(|out| + 1)` along the run. -/
def driverStepTape {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width) (z : DriverCorridor)
    (st : DriveState n) (tape : Fin L → Bool) : Fin L → Bool :=
  match st with
  | ⟨_, out, ctrl, val, true⟩ =>
      match ctrl with
      | [] => tape
      | (tag, rem) :: ctrl' =>
          if rem = 1 then
            match tag, val with
            | ITag.tnot, i :: vs =>
                writeBlockTape
                  (popStepTape tape (z.ctrlBase + (encodeCtrlStackR ctrl').length)
                    (List.replicate (encodeCtrlFrameR (ITag.tnot, 1)).length false)
                    (z.valBase + (encodeNatStackR vs).length)
                    (encodeNatEntryR out.length
                      ++ List.replicate ((([i] : List Nat).reverse.flatMap encodeNatEntryR).length
                          - (out.length + 3)) false)
                    (z.workBase + (encodeGateRecordStream out).length)
                    (encodeGateRecord (SLGate.notGate i : SLGate n)))
                  (z.shwBase + out.length + 1) [true]
            | ITag.tand, i2 :: i1 :: vs =>
                writeBlockTape
                  (popStepTape tape (z.ctrlBase + (encodeCtrlStackR ctrl').length)
                    (List.replicate (encodeCtrlFrameR (ITag.tand, 1)).length false)
                    (z.valBase + (encodeNatStackR vs).length)
                    (encodeNatEntryR out.length
                      ++ List.replicate ((([i2, i1] : List Nat).reverse.flatMap encodeNatEntryR).length
                          - (out.length + 3)) false)
                    (z.workBase + (encodeGateRecordStream out).length)
                    (encodeGateRecord (SLGate.andGate i1 i2 : SLGate n)))
                  (z.shwBase + out.length + 1) [true]
            | ITag.tor, i2 :: i1 :: vs =>
                writeBlockTape
                  (popStepTape tape (z.ctrlBase + (encodeCtrlStackR ctrl').length)
                    (List.replicate (encodeCtrlFrameR (ITag.tor, 1)).length false)
                    (z.valBase + (encodeNatStackR vs).length)
                    (encodeNatEntryR out.length
                      ++ List.replicate ((([i2, i1] : List Nat).reverse.flatMap encodeNatEntryR).length
                          - (out.length + 3)) false)
                    (z.workBase + (encodeGateRecordStream out).length)
                    (encodeGateRecord (SLGate.orGate i1 i2 : SLGate n)))
                  (z.shwBase + out.length + 1) [true]
            | _, _ => tape
          else if 2 ≤ rem then
            writeBlockTape tape (z.ctrlBase + (encodeCtrlStackR ctrl').length)
              (encodeCtrlFrameR (tag, rem - 1) ++ [false])
          else tape
  | ⟨[], _, _, _, false⟩ => tape
  | ⟨PreToken.leaf g :: toks', out, _, val, false⟩ =>
      writeBlockTape
        (leafStepTape tape
          (z.certEnd - (encodePreorder width h_width (PreToken.leaf g :: toks')).length)
          (encodePreToken width h_width (PreToken.leaf g)).length
          (z.valBase + (encodeNatStackR val).length)
          (z.workBase + (encodeGateRecordStream out).length)
          (encodeNatEntryR out.length)
          (encodeGateRecord g))
        (z.shwBase + out.length + 1) [true]
  | ⟨PreToken.node tag :: toks', _, ctrl, _, false⟩ =>
      nodeStepTape tape
        (z.certEnd - (encodePreorder width h_width (PreToken.node tag :: toks')).length)
        (z.ctrlBase + (encodeCtrlStackR ctrl).length)
        (encodeCtrlFrameR (tag, tag.arity))

/-- **The branch side conditions** for `corridorInv_driverStep`: zone capacities for the write
branches (settle-emit, leaf emit, node frame push — the emit branches also need one shadow-count
cell of room for the tick) and tail-nonemptiness for the node branch (a node token is never last in
a well-formed stream).  `True` on the identity and settle-decrement branches.  Discharged later from
zone sizing + reachable-state bounds. -/
def DriverStepFits {n : Nat} (z : DriverCorridor) (st : DriveState n) : Prop :=
  match st with
  | ⟨_, out, ctrl, val, true⟩ =>
      match ctrl with
      | [] => True
      | (tag, rem) :: _ =>
          if rem = 1 then
            match tag, val with
            | ITag.tnot, i :: vs =>
                z.workBase + (encodeGateRecordStream out).length
                    + (encodeGateRecord (SLGate.notGate i : SLGate n)).length + 1 ≤ z.workEnd
                ∧ z.valBase + (encodeNatStackR vs).length + (out.length + 3) ≤ z.valEnd
                ∧ z.shwBase + out.length + 2 ≤ z.shwEnd
            | ITag.tand, i2 :: i1 :: vs =>
                z.workBase + (encodeGateRecordStream out).length
                    + (encodeGateRecord (SLGate.andGate i1 i2 : SLGate n)).length + 1 ≤ z.workEnd
                ∧ z.valBase + (encodeNatStackR vs).length + (out.length + 3) ≤ z.valEnd
                ∧ z.shwBase + out.length + 2 ≤ z.shwEnd
            | ITag.tor, i2 :: i1 :: vs =>
                z.workBase + (encodeGateRecordStream out).length
                    + (encodeGateRecord (SLGate.orGate i1 i2 : SLGate n)).length + 1 ≤ z.workEnd
                ∧ z.valBase + (encodeNatStackR vs).length + (out.length + 3) ≤ z.valEnd
                ∧ z.shwBase + out.length + 2 ≤ z.shwEnd
            | _, _ => True
          else True
  | ⟨[], _, _, _, false⟩ => True
  | ⟨PreToken.leaf g :: _, out, _, val, false⟩ =>
      z.workBase + (encodeGateRecordStream out).length
          + (encodeGateRecord g).length + 1 ≤ z.workEnd
      ∧ z.valBase + (encodeNatStackR val).length + (out.length + 3) ≤ z.valEnd
      ∧ z.shwBase + out.length + 2 ≤ z.shwEnd
  | ⟨PreToken.node tag :: toks', _, ctrl, _, false⟩ =>
      toks' ≠ []
      ∧ z.ctrlBase + (encodeCtrlStackR ctrl).length
          + (encodeCtrlFrameR (tag, tag.arity)).length ≤ z.ctrlEnd

/-- **The one-step dispatcher keystone.**  For every abstract state, under the branch's side
conditions, the total transformer `driverStepTape` carries `driverCorridorInv` from `st` to
`st.step`.  This is the exact per-iteration fact the on-tape loop's invariant induction consumes. -/
theorem corridorInv_driverStep {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (st : DriveState n) (tape : Fin L → Bool)
    (hinv : driverCorridorInv width h_width z tape st)
    (hfits : DriverStepFits z st) :
    driverCorridorInv width h_width z (driverStepTape width h_width z st tape) st.step := by
  obtain ⟨toks, out, ctrl, val, settling⟩ := st
  cases settling with
  | true =>
      cases ctrl with
      | nil =>
          simp only [driverStepTape, DriveState.step]
          exact corridorInv_settleClearStep width h_width z toks out val tape hinv
      | cons f ctrl' =>
          obtain ⟨tag, rem⟩ := f
          by_cases hrem : rem = 1
          · subst hrem
            cases tag with
            | tnot =>
                cases val with
                | nil =>
                    simp only [driverStepTape, DriveState.step]
                    exact corridorInv_clearFlag width h_width z toks out _ [] tape hinv
                | cons i vs =>
                    simp only [driverStepTape, DriveState.step, DriverStepFits] at hfits ⊢
                    exact corridorInv_popStep width h_width z ITag.tnot (SLGate.notGate i)
                      [i] vs toks out ctrl' tape hinv hfits.1 hfits.2.1 hfits.2.2
            | tand =>
                cases val with
                | nil =>
                    simp only [driverStepTape, DriveState.step]
                    exact corridorInv_clearFlag width h_width z toks out _ [] tape hinv
                | cons i2 rest =>
                    cases rest with
                    | nil =>
                        simp only [driverStepTape, DriveState.step]
                        exact corridorInv_clearFlag width h_width z toks out _ [i2] tape hinv
                    | cons i1 vs =>
                        simp only [driverStepTape, DriveState.step, DriverStepFits] at hfits ⊢
                        exact corridorInv_popStep width h_width z ITag.tand
                          (SLGate.andGate i1 i2) [i2, i1] vs toks out ctrl' tape hinv
                          hfits.1 hfits.2.1 hfits.2.2
            | tor =>
                cases val with
                | nil =>
                    simp only [driverStepTape, DriveState.step]
                    exact corridorInv_clearFlag width h_width z toks out _ [] tape hinv
                | cons i2 rest =>
                    cases rest with
                    | nil =>
                        simp only [driverStepTape, DriveState.step]
                        exact corridorInv_clearFlag width h_width z toks out _ [i2] tape hinv
                    | cons i1 vs =>
                        simp only [driverStepTape, DriveState.step, DriverStepFits] at hfits ⊢
                        exact corridorInv_popStep width h_width z ITag.tor
                          (SLGate.orGate i1 i2) [i2, i1] vs toks out ctrl' tape hinv
                          hfits.1 hfits.2.1 hfits.2.2
          · by_cases h2 : 2 ≤ rem
            · simp only [driverStepTape, DriveState.step, if_neg hrem, if_pos h2]
              exact corridorInv_decStep width h_width z tag rem h2 toks out ctrl' val tape hinv
            · have hr0 : rem = 0 := by omega
              subst hr0
              simp only [driverStepTape, DriveState.step, if_neg hrem, if_neg h2, Nat.zero_sub]
              exact corridorInv_clearFlag width h_width z toks out ((tag, 0) :: ctrl') val tape hinv
  | false =>
      cases toks with
      | nil =>
          simpa only [driverStepTape] using
            corridorInv_terminalStep width h_width z out ctrl val tape hinv
      | cons tok toks' =>
          cases tok with
          | leaf g =>
              simp only [DriverStepFits] at hfits
              obtain ⟨hwcap, hvcap, hscap⟩ := hfits
              cases toks' with
              | nil =>
                  simp only [driverStepTape, DriveState.step]
                  exact corridorInv_leafStep_last width h_width z g out ctrl val tape hinv
                    hwcap hvcap hscap
              | cons t ts =>
                  cases g with
                  | input i =>
                      simp only [driverStepTape, DriveState.step]
                      rw [show (encodePreToken width h_width
                          (PreToken.leaf (SLGate.input i))).length = 3 + width from by
                        show ([false, false, false]
                          ++ encodeFin width ⟨i.val, lt_of_lt_of_le i.isLt h_width⟩).length
                          = 3 + width
                        rw [List.length_append, encodeFin_length]
                        rfl]
                      exact corridorInv_inputStep width h_width z i (t :: ts) out ctrl val tape
                        hinv (List.cons_ne_nil t ts) hwcap hvcap hscap
                  | const b =>
                      have hwcap4 : z.workBase + (encodeGateRecordStream out).length + 4
                          ≤ z.workEnd := by
                        have hlen : (encodeGateRecord (SLGate.const b : SLGate n)).length = 3 := by
                          simp [encodeGateRecord, unaryField]
                        omega
                      simp only [driverStepTape, DriveState.step]
                      exact corridorInv_constStep width h_width z b (t :: ts) out ctrl val tape
                        hinv (List.cons_ne_nil t ts) hwcap4 hvcap hscap
                  | notGate k =>
                      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hvalid, _⟩
                        := hinv
                      have h := hvalid _ (List.mem_cons_self ..)
                      simp only [ValidCertToken] at h
                  | andGate k l =>
                      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hvalid, _⟩
                        := hinv
                      have h := hvalid _ (List.mem_cons_self ..)
                      simp only [ValidCertToken] at h
                  | orGate k l =>
                      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hvalid, _⟩
                        := hinv
                      have h := hvalid _ (List.mem_cons_self ..)
                      simp only [ValidCertToken] at h
          | node tag =>
              simp only [DriverStepFits] at hfits
              obtain ⟨htoks', hcap⟩ := hfits
              simp only [driverStepTape, DriveState.step]
              exact corridorInv_nodeStep width h_width z tag toks' out ctrl val tape hinv
                htoks' hcap

end ContractExpansion
end Frontier
end Pnp4
