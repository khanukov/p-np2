import Pnp4.Frontier.ContractExpansion.TreeMCSPDriverRealization

/-!
# `settleProbe` — D2t-5b (Block A5m-2): the control-stack empty test at the top anchor

The settling dispatch's first decision: with the head on the control stack's rightmost content `1`
(where `corridor_scan_M_to_ctrlTop` parks it), **peek one cell left** — a `1` means the top block is
a frame's tag block (every frame block carries `≥ 2` ones, the A3 walker-disambiguation discipline),
a `0` means the top `1` was the lone **base sentinel** (the stack is empty; the cell to its left is
the dead val→ctrl corridor).  `settleProbe` is that two-step machine, with one outcome phase per
verdict:

* `φ0` — step left (peek);
* `φ1` — decide: `1` → `φ2` (**frame**), `0` → `φ3` (**empty**);
* `φ2`/`φ3` — outcome idle.

`settleProbe_runConfig_frame` / `settleProbe_runConfig_empty` instantiate the two verdicts under
`driverCorridorInv` (the frame case via the codec fact `encodeCtrlStackR_penultimate_true`; the
empty case via the val→ctrl dead corridor), each in exactly `2` steps, tape unchanged.

**Progress classification (AGENTS.md): Infrastructure** — a verifier machine component with its run
lemmas; builds no verifier and proves no separation.  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-! ### Codec fact: a nonempty control stack's penultimate cell is `1` -/

/-- `getD` into an all-`true` block is `true` at every in-range index. -/
theorem getD_replicate_true (m i : Nat) (h : i < m) :
    (List.replicate m true).getD i false = true := by
  induction m generalizing i with
  | zero => omega
  | succ m ih =>
      cases i with
      | zero => rfl
      | succ i => rw [List.replicate_succ, List.getD_cons_succ]; exact ih i (by omega)

/-- **A nonempty control stack's penultimate cell is `1`**: the rightmost block is the top frame's
tag block, which carries `tagCode + 2 ≥ 2` ones. -/
theorem encodeCtrlStackR_penultimate_true (f : ITag × Nat) (rest : List (ITag × Nat)) :
    (encodeCtrlStackR (f :: rest)).getD ((encodeCtrlStackR (f :: rest)).length - 2) false
      = true := by
  obtain ⟨tag, rem⟩ := f
  have hsplit : encodeCtrlStackR ((tag, rem) :: rest)
      = (encodeCtrlStackR rest ++ (false :: List.replicate (rem + 1) true ++ [false]))
        ++ List.replicate (tag.tagCode + 2) true := by
    rw [encodeCtrlStackR_cons]
    show encodeCtrlStackR rest
        ++ (false :: (List.replicate (rem + 1) true
          ++ (false :: List.replicate (tag.tagCode + 2) true)))
      = _
    simp [List.append_assoc]
  rw [hsplit]
  have hlen : ((encodeCtrlStackR rest ++ (false :: List.replicate (rem + 1) true ++ [false]))
      ++ List.replicate (tag.tagCode + 2) true).length
      = (encodeCtrlStackR rest ++ (false :: List.replicate (rem + 1) true ++ [false])).length
        + (tag.tagCode + 2) := by
    rw [List.length_append, List.length_replicate]
  rw [hlen, List.getD_append_right _ _ _ _ (by omega)]
  exact getD_replicate_true _ _ (by omega)

/-! ### The probe machine -/

/-- **The settle probe** (4 phases): step left to peek the cell left of the control top; decide —
`1` is a frame block (→ `φ2`, **frame**), `0` is the dead zone left of the base sentinel (→ `φ3`,
**empty**); the outcome phases idle. -/
def settleProbe : ConstStatePhasedProgram Unit where
  numPhases := 4
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨3, by omega⟩
  acceptState := ()
  transition := fun i _ b =>
    if i.val = 0 then (⟨1, by omega⟩, (), b, Move.left)
    else if i.val = 1 then
      if b then (⟨2, by omega⟩, (), b, Move.stay)
      else (⟨3, by omega⟩, (), b, Move.stay)
    else (⟨i.val, i.isLt⟩, (), b, Move.stay)
  timeBound := fun _ => 2

/-! ### Single steps -/

/-- φ0 (step-left-to-peek): the phase advances to `1`. -/
theorem settleProbe_stepConfig_p0_phase {L : Nat}
    (c : Configuration (M := settleProbe.toPhased.toTM) L)
    {i : Fin 4} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    ((TM.stepConfig (M := settleProbe.toPhased.toTM) c).state).fst.val = 1 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, settleProbe, hi]

/-- φ0: the head moves left. -/
theorem settleProbe_stepConfig_p0_head {L : Nat}
    (c : Configuration (M := settleProbe.toPhased.toTM) L)
    {i : Fin 4} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := settleProbe.toPhased.toTM) c).head
      = Configuration.moveHead (c := c) Move.left := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, settleProbe, hi]

/-- φ0: the tape is unchanged. -/
theorem settleProbe_stepConfig_p0_tape {L : Nat}
    (c : Configuration (M := settleProbe.toPhased.toTM) L)
    {i : Fin 4} {s : Unit} (hi : i.val = 0) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := settleProbe.toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := settleProbe.toPhased.toTM) c).tape
      = c.write c.head (c.tape c.head) := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    simp [ConstStatePhasedProgram.toPhased, settleProbe, hi]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-- φ1 (decide) on a `1`: the **frame** verdict — phase `2`, head stays. -/
theorem settleProbe_stepConfig_p1_one_phase {L : Nat}
    (c : Configuration (M := settleProbe.toPhased.toTM) L)
    {i : Fin 4} {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = true) :
    ((TM.stepConfig (M := settleProbe.toPhased.toTM) c).state).fst.val = 2 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, settleProbe, hi, hbit]

/-- φ1 on a `0`: the **empty** verdict — phase `3`, head stays. -/
theorem settleProbe_stepConfig_p1_zero_phase {L : Nat}
    (c : Configuration (M := settleProbe.toPhased.toTM) L)
    {i : Fin 4} {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩)
    (hbit : c.tape c.head = false) :
    ((TM.stepConfig (M := settleProbe.toPhased.toTM) c).state).fst.val = 3 := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  simp [ConstStatePhasedProgram.toPhased, settleProbe, hi, hbit]

/-- φ1: the head stays (either verdict). -/
theorem settleProbe_stepConfig_p1_head {L : Nat}
    (c : Configuration (M := settleProbe.toPhased.toTM) L)
    {i : Fin 4} {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := settleProbe.toPhased.toTM) c).head = c.head := by
  unfold TM.stepConfig
  rw [hstate]
  simp only [PhasedProgram.toTM_step]
  by_cases hbit : c.tape c.head
  · simp [ConstStatePhasedProgram.toPhased, settleProbe, hi, hbit, Configuration.moveHead]
  · simp only [Bool.not_eq_true] at hbit
    simp [ConstStatePhasedProgram.toPhased, settleProbe, hi, hbit, Configuration.moveHead]

/-- φ1: the tape is unchanged (either verdict). -/
theorem settleProbe_stepConfig_p1_tape {L : Nat}
    (c : Configuration (M := settleProbe.toPhased.toTM) L)
    {i : Fin 4} {s : Unit} (hi : i.val = 1) (hstate : c.state = ⟨i, s⟩) :
    (TM.stepConfig (M := settleProbe.toPhased.toTM) c).tape = c.tape := by
  have hwrite : (TM.stepConfig (M := settleProbe.toPhased.toTM) c).tape
      = c.write c.head (c.tape c.head) := by
    unfold TM.stepConfig
    rw [hstate]
    simp only [PhasedProgram.toTM_step]
    by_cases hbit : c.tape c.head
    · simp [ConstStatePhasedProgram.toPhased, settleProbe, hi, hbit]
    · simp only [Bool.not_eq_true] at hbit
      simp [ConstStatePhasedProgram.toPhased, settleProbe, hi, hbit]
  rw [hwrite]
  funext j
  by_cases hj : j = c.head
  · subst hj; simp [Configuration.write]
  · simp [Configuration.write, hj]

/-! ### The two-step verdicts under the corridor invariant -/

/-- **The frame verdict.**  For a settling state with a nonempty control stack, from `φ0` on the
control top, two steps land in the **frame** outcome phase (`2`), head one left of the top, tape
unchanged.  (The peeked cell is the top frame's tag block, all-`1` by
`encodeCtrlStackR_penultimate_true`.) -/
theorem settleProbe_runConfig_frame {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (st : DriveState n) (f : ITag × Nat) (rest : List (ITag × Nat))
    (c0 : Configuration (M := settleProbe.toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z c0.tape st)
    (hctrl : st.ctrl = f :: rest)
    (hphase : (c0.state.fst : Nat) = 0)
    (hhead : (c0.head : Nat) = z.ctrlBase + (encodeCtrlStackR st.ctrl).length - 1) :
    (((TM.runConfig (M := settleProbe.toPhased.toTM) c0 2).state).fst : Nat) = 2
      ∧ ((TM.runConfig (M := settleProbe.toPhased.toTM) c0 2).head : Nat) = (c0.head : Nat) - 1
      ∧ (TM.runConfig (M := settleProbe.toPhased.toTM) c0 2).tape = c0.tape := by
  obtain ⟨hwf, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hctrlw, hcfit2, _, _⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hwf
  replace hctrlw : windowSpells c0.tape z.ctrlBase (encodeCtrlStackR st.ctrl) := hctrlw
  replace hcfit2 : z.ctrlBase + (encodeCtrlStackR st.ctrl).length ≤ z.ctrlEnd := hcfit2
  -- The encoded stack has ≥ 2 cells (sentinel + a frame's ≥ 8 cells).
  have hlen2 : 2 ≤ (encodeCtrlStackR st.ctrl).length := by
    rw [hctrl, encodeCtrlStackR_cons, List.length_append]
    obtain ⟨tag, rem⟩ := f
    rw [encodeCtrlFrameR_length]
    have : 1 ≤ (encodeCtrlStackR rest).length := by
      cases hr : encodeCtrlStackR rest with
      | nil =>
          have := encodeCtrlStackR_getLast_true rest
          rw [hr] at this; simp at this
      | cons a l => simp
    omega
  have hpos : 1 ≤ (c0.head : Nat) := by omega
  have hne : ¬ (c0.head : Nat) = 0 := by omega
  -- Step 1.
  rw [show (2 : Nat) = 1 + 1 from rfl, TM.runConfig_add, TM.runConfig_one]
  set c1 := TM.stepConfig (M := settleProbe.toPhased.toTM) c0 with hc1
  have hph1 : (c1.state.fst : Nat) = 1 :=
    settleProbe_stepConfig_p0_phase c0 (i := c0.state.fst) (s := c0.state.snd) hphase rfl
  have hhd1 : c1.head = Configuration.moveHead (c := c0) Move.left :=
    settleProbe_stepConfig_p0_head c0 (i := c0.state.fst) (s := c0.state.snd) hphase rfl
  have htp1 : c1.tape = c0.tape :=
    settleProbe_stepConfig_p0_tape c0 (i := c0.state.fst) (s := c0.state.snd) hphase rfl
  have hhd1v : (c1.head : Nat) = (c0.head : Nat) - 1 := by
    rw [hhd1]
    simp only [Configuration.moveHead, dif_neg hne]
  -- The peeked cell is the penultimate stack cell: `1`.
  have hbit1 : c1.tape c1.head = true := by
    rw [htp1]
    have hidx : (c1.head : Nat) = z.ctrlBase + ((encodeCtrlStackR st.ctrl).length - 2) := by
      omega
    have := hctrlw.2 c1.head (by omega) (by omega)
    rw [this, hidx]
    have hsub : z.ctrlBase + ((encodeCtrlStackR st.ctrl).length - 2) - z.ctrlBase
        = (encodeCtrlStackR st.ctrl).length - 2 := by omega
    rw [hsub, hctrl]
    exact encodeCtrlStackR_penultimate_true f rest
  -- Step 2.
  rw [TM.runConfig_one]
  refine ⟨?_, ?_, ?_⟩
  · exact settleProbe_stepConfig_p1_one_phase c1 (i := c1.state.fst) (s := c1.state.snd)
      hph1 rfl hbit1
  · rw [settleProbe_stepConfig_p1_head c1 (i := c1.state.fst) (s := c1.state.snd) hph1 rfl]
    exact hhd1v
  · rw [settleProbe_stepConfig_p1_tape c1 (i := c1.state.fst) (s := c1.state.snd) hph1 rfl]
    exact htp1

/-- **The empty verdict.**  For a settling state with an **empty** control stack, from `φ0` on the
base sentinel, two steps land in the **empty** outcome phase (`3`), head one left of the sentinel,
tape unchanged.  (The peeked cell is the dead SHW→ctrl corridor.) -/
theorem settleProbe_runConfig_empty {n L : Nat} (width : Nat) (h_width : n ≤ 2 ^ width)
    (z : DriverCorridor) (st : DriveState n)
    (c0 : Configuration (M := settleProbe.toPhased.toTM) L)
    (hinv : driverCorridorInv width h_width z c0.tape st)
    (hctrl : st.ctrl = [])
    (hphase : (c0.state.fst : Nat) = 0)
    (hhead : (c0.head : Nat) = z.ctrlBase) :
    (((TM.runConfig (M := settleProbe.toPhased.toTM) c0 2).state).fst : Nat) = 3
      ∧ ((TM.runConfig (M := settleProbe.toPhased.toTM) c0 2).head : Nat) = z.ctrlBase - 1
      ∧ (TM.runConfig (M := settleProbe.toPhased.toTM) c0 2).tape = c0.tape := by
  obtain ⟨hwf, _, _, _, _, _, _, _, _, _, _, _, _, _, hsfit, hszeros, _, _, _, _⟩ := hinv
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hwf
  replace hsfit : z.shwBase + st.out.length + 1 ≤ z.shwEnd := hsfit
  replace hszeros : ∀ p : Fin (settleProbe.toPhased.toTM.tapeLength L),
      z.shwBase + st.out.length + 1 ≤ (p : Nat) →
      (p : Nat) < z.ctrlBase → c0.tape p = false := hszeros
  have hpos : 1 ≤ (c0.head : Nat) := by omega
  have hne : ¬ (c0.head : Nat) = 0 := by omega
  rw [show (2 : Nat) = 1 + 1 from rfl, TM.runConfig_add, TM.runConfig_one]
  set c1 := TM.stepConfig (M := settleProbe.toPhased.toTM) c0 with hc1
  have hph1 : (c1.state.fst : Nat) = 1 :=
    settleProbe_stepConfig_p0_phase c0 (i := c0.state.fst) (s := c0.state.snd) hphase rfl
  have hhd1 : c1.head = Configuration.moveHead (c := c0) Move.left :=
    settleProbe_stepConfig_p0_head c0 (i := c0.state.fst) (s := c0.state.snd) hphase rfl
  have htp1 : c1.tape = c0.tape :=
    settleProbe_stepConfig_p0_tape c0 (i := c0.state.fst) (s := c0.state.snd) hphase rfl
  have hhd1v : (c1.head : Nat) = z.ctrlBase - 1 := by
    rw [hhd1]
    simp only [Configuration.moveHead, dif_neg hne]
    omega
  -- The peeked cell is the dead SHW→ctrl corridor.
  have hbit1 : c1.tape c1.head = false := by
    rw [htp1]
    exact hszeros c1.head (by omega) (by omega)
  rw [TM.runConfig_one]
  refine ⟨?_, ?_, ?_⟩
  · exact settleProbe_stepConfig_p1_zero_phase c1 (i := c1.state.fst) (s := c1.state.snd)
      hph1 rfl hbit1
  · rw [settleProbe_stepConfig_p1_head c1 (i := c1.state.fst) (s := c1.state.snd) hph1 rfl]
    exact hhd1v
  · rw [settleProbe_stepConfig_p1_tape c1 (i := c1.state.fst) (s := c1.state.snd) hph1 rfl]
    exact htp1

end ContractExpansion
end Frontier
end Pnp4
