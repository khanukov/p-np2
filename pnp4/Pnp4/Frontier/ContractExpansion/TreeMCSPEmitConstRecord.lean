import Pnp4.Frontier.ContractExpansion.TreeMCSPStepRightProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPGateRecordLayout

/-!
# `emitConstRecord` — D2t-4a: emit a `const` gate record (NP-verifier track — D2 transcoder)

The first **leaf-emit** brick (D2t-4a).  A `const b` gate encodes (`encodeGateRecord`, D0) as the fixed
3-cell record `unaryField 1 ++ [b] = [true, false, b]` — the unary tag `1 0` followed by the literal bit.
`emitConstRecord b` writes exactly that into WORK: a **monolithic** 4-phase program (write `1` →, write
`0` →, write `b` →, accept) that sidesteps any `seqList`/`seqP2` composition for this fixed-width record.

`emitConstRecord_runConfig_three` gives its run-through (from the write head at `p`, after `3` steps the
cells `[p, p+1, p+2]` hold `1 0 b` and the head rests at `p + 3`), and `emitConstRecord_runConfig_record`
states it against the **spec**: those cells equal `encodeGateRecord (SLGate.const b)`.

**Progress classification (AGENTS.md): Infrastructure** — a verifier emit-component proven against the
pure record codec; builds no verifier and proves no separation.  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram
open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- Monolithic emitter for a `const b` gate record `1 0 b`: three fixed right-moving writes (`1`, `0`,
`b`), then accept (phase `3`). -/
def emitConstRecord (b : Bool) : ConstStatePhasedProgram Unit where
  numPhases := 4
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨3, by omega⟩
  acceptState := ()
  transition := fun i _ _ =>
    if i.val = 0 then (⟨1, by omega⟩, (), true, Move.right)
    else if i.val = 1 then (⟨2, by omega⟩, (), false, Move.right)
    else if i.val = 2 then (⟨3, by omega⟩, (), b, Move.right)
    else (⟨3, by omega⟩, (), false, Move.stay)
  timeBound := fun _ => 3

@[simp] theorem emitConstRecord_numPhases (b : Bool) : (emitConstRecord b).numPhases = 4 := rfl
@[simp] theorem emitConstRecord_startPhase_val (b : Bool) : ((emitConstRecord b).startPhase : Nat) = 0 := rfl
@[simp] theorem emitConstRecord_acceptPhase_val (b : Bool) : ((emitConstRecord b).acceptPhase : Nat) = 3 := rfl
@[simp] theorem emitConstRecord_timeBound (b : Bool) (n : Nat) : (emitConstRecord b).timeBound n = 3 := rfl

/-- Common shape of a phase-`{0,1,2}` step: write `wb`, move right, advance to phase `np`. -/
private theorem stepGen {L : Nat} (b : Bool)
    (c : Configuration (M := (emitConstRecord b).toPhased.toTM) L)
    {i : Fin (emitConstRecord b).numPhases} {s : Unit} (np : Nat) (wb : Bool)
    (hstate : c.state = ⟨i, s⟩)
    (hhead : (c.head : Nat) + 1 < (emitConstRecord b).toPhased.toTM.tapeLength L)
    (hph : ((emitConstRecord b).transition i s (c.tape c.head)).1.val = np)
    (hmv : ((emitConstRecord b).transition i s (c.tape c.head)).2.2.2 = Move.right)
    (hbt : ((emitConstRecord b).transition i s (c.tape c.head)).2.2.1 = wb) :
    ((TM.stepConfig (M := (emitConstRecord b).toPhased.toTM) c).state).fst.val = np
      ∧ ((TM.stepConfig (M := (emitConstRecord b).toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1
      ∧ (TM.stepConfig (M := (emitConstRecord b).toPhased.toTM) c).tape = c.write c.head wb := by
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (emitConstRecord b) c hstate, hph]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (emitConstRecord b) c hstate, hmv,
      Configuration.moveHead_right_lt c hhead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (emitConstRecord b) c hstate, hbt]

/-- Phase-`0` step: write `1`, move right, reach phase `1`. -/
theorem emitConstRecord_step0 {L : Nat} (b : Bool)
    (c : Configuration (M := (emitConstRecord b).toPhased.toTM) L)
    {i : Fin (emitConstRecord b).numPhases} {s : Unit} (hi : (i : Nat) = 0) (hstate : c.state = ⟨i, s⟩)
    (hhead : (c.head : Nat) + 1 < (emitConstRecord b).toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := (emitConstRecord b).toPhased.toTM) c).state).fst.val = 1
      ∧ ((TM.stepConfig (M := (emitConstRecord b).toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1
      ∧ (TM.stepConfig (M := (emitConstRecord b).toPhased.toTM) c).tape = c.write c.head true :=
  stepGen b c 1 true hstate hhead (by simp [emitConstRecord, hi]) (by simp [emitConstRecord, hi])
    (by simp [emitConstRecord, hi])

/-- Phase-`1` step: write `0`, move right, reach phase `2`. -/
theorem emitConstRecord_step1 {L : Nat} (b : Bool)
    (c : Configuration (M := (emitConstRecord b).toPhased.toTM) L)
    {i : Fin (emitConstRecord b).numPhases} {s : Unit} (hi : (i : Nat) = 1) (hstate : c.state = ⟨i, s⟩)
    (hhead : (c.head : Nat) + 1 < (emitConstRecord b).toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := (emitConstRecord b).toPhased.toTM) c).state).fst.val = 2
      ∧ ((TM.stepConfig (M := (emitConstRecord b).toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1
      ∧ (TM.stepConfig (M := (emitConstRecord b).toPhased.toTM) c).tape = c.write c.head false :=
  stepGen b c 2 false hstate hhead (by simp [emitConstRecord, hi]) (by simp [emitConstRecord, hi])
    (by simp [emitConstRecord, hi])

/-- Phase-`2` step: write the literal `b`, move right, reach the accept phase `3`. -/
theorem emitConstRecord_step2 {L : Nat} (b : Bool)
    (c : Configuration (M := (emitConstRecord b).toPhased.toTM) L)
    {i : Fin (emitConstRecord b).numPhases} {s : Unit} (hi : (i : Nat) = 2) (hstate : c.state = ⟨i, s⟩)
    (hhead : (c.head : Nat) + 1 < (emitConstRecord b).toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := (emitConstRecord b).toPhased.toTM) c).state).fst.val = 3
      ∧ ((TM.stepConfig (M := (emitConstRecord b).toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1
      ∧ (TM.stepConfig (M := (emitConstRecord b).toPhased.toTM) c).tape = c.write c.head b :=
  stepGen b c 3 b hstate hhead (by simp [emitConstRecord, hi]) (by simp [emitConstRecord, hi])
    (by simp [emitConstRecord, hi])

/-- **`emitConstRecord` run-through.**  From the write head at `p = c.head` (phase `0`) with `3` cells of
room, after `3` steps the program is at the accept phase `3`, the head rests at `p + 3`, and the cells
`[p, p+1, p+2]` hold `1 0 b` (tape elsewhere unchanged). -/
theorem emitConstRecord_runConfig_three {L : Nat} (b : Bool)
    (c : Configuration (M := (emitConstRecord b).toPhased.toTM) L)
    (hphase : (c.state.fst : Nat) = 0)
    (hroom : (c.head : Nat) + 3 < (emitConstRecord b).toPhased.toTM.tapeLength L) :
    (((TM.runConfig (M := (emitConstRecord b).toPhased.toTM) c 3).state).fst : Nat) = 3
      ∧ ((TM.runConfig (M := (emitConstRecord b).toPhased.toTM) c 3).head : Nat) = (c.head : Nat) + 3
      ∧ ∀ q : Fin ((emitConstRecord b).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (emitConstRecord b).toPhased.toTM) c 3).tape q
            = (if (q : Nat) = (c.head : Nat) then true
               else if (q : Nat) = (c.head : Nat) + 1 then false
               else if (q : Nat) = (c.head : Nat) + 2 then b else c.tape q) := by
  obtain ⟨h0p, h0h, h0t⟩ := emitConstRecord_step0 b c (i := c.state.fst) (s := c.state.snd) hphase rfl (by omega)
  set c1 := TM.runConfig (M := (emitConstRecord b).toPhased.toTM) c 1 with hc1
  have hc1eq : c1 = TM.stepConfig (M := (emitConstRecord b).toPhased.toTM) c := by
    rw [hc1, show (1 : Nat) = 0 + 1 from rfl, TM.runConfig_succ]; rfl
  have h1h : (c1.head : Nat) = (c.head : Nat) + 1 := by rw [hc1eq]; exact h0h
  obtain ⟨h1p, h1h', h1t⟩ := emitConstRecord_step1 b c1 (i := c1.state.fst) (s := c1.state.snd)
    (by rw [hc1eq]; exact h0p) rfl (by rw [h1h]; omega)
  set c2 := TM.runConfig (M := (emitConstRecord b).toPhased.toTM) c 2 with hc2
  have hc2eq : c2 = TM.stepConfig (M := (emitConstRecord b).toPhased.toTM) c1 := by
    rw [hc2, show (2 : Nat) = 1 + 1 from rfl, TM.runConfig_succ, hc1]
  have h2h : (c2.head : Nat) = (c.head : Nat) + 2 := by rw [hc2eq, h1h', h1h]
  obtain ⟨h2p, h2h', h2t⟩ := emitConstRecord_step2 b c2 (i := c2.state.fst) (s := c2.state.snd)
    (by rw [hc2eq]; exact h1p) rfl (by rw [h2h]; omega)
  have hc3eq : TM.runConfig (M := (emitConstRecord b).toPhased.toTM) c 3
      = TM.stepConfig (M := (emitConstRecord b).toPhased.toTM) c2 := by
    rw [show (3 : Nat) = 2 + 1 from rfl, TM.runConfig_succ, hc2]
  refine ⟨?_, ?_, ?_⟩
  · rw [hc3eq]; exact h2p
  · rw [hc3eq, h2h', h2h]
  · intro q
    rw [hc3eq, h2t]
    have hc2t : c2.tape = c1.write c1.head false := by rw [hc2eq]; exact h1t
    have hc1t : c1.tape = c.write c.head true := by rw [hc1eq]; exact h0t
    by_cases hq2 : (q : Nat) = (c.head : Nat) + 2
    · have hqf : q = c2.head := Fin.ext (by rw [h2h]; exact hq2)
      rw [Configuration.write, dif_pos hqf, if_neg (by omega), if_neg (by omega), if_pos hq2]
    · have hqne2 : q ≠ c2.head := fun h => hq2 (by rw [h]; exact h2h)
      rw [Configuration.write, dif_neg hqne2, hc2t]
      by_cases hq1 : (q : Nat) = (c.head : Nat) + 1
      · have hqf : q = c1.head := Fin.ext (by rw [h1h]; exact hq1)
        rw [Configuration.write, dif_pos hqf, if_neg (by omega), if_pos hq1]
      · have hqne1 : q ≠ c1.head := fun h => hq1 (by rw [h]; exact h1h)
        rw [Configuration.write, dif_neg hqne1, hc1t]
        by_cases hq0 : (q : Nat) = (c.head : Nat)
        · have hqf : q = c.head := Fin.ext hq0
          rw [Configuration.write, dif_pos hqf, if_pos hq0]
        · have hqne0 : q ≠ c.head := fun h => hq0 (by rw [h])
          rw [Configuration.write, dif_neg hqne0, if_neg hq0, if_neg hq1, if_neg hq2]

/-- The `const b` record is the fixed 3-cell list `1 0 b` (a pure-spec fact). -/
@[simp] theorem encodeGateRecord_const {n : Nat} (b : Bool) :
    encodeGateRecord (n := n) (SLGate.const b) = [true, false, b] := by
  simp [encodeGateRecord, unaryField, List.replicate]

/-- **`emitConstRecord` correctness (against the spec).**  The three emitted cells are exactly the bits
of `encodeGateRecord (SLGate.const b) = [true, false, b]`: cell `p` holds `1`, cell `p+1` holds `0`, cell
`p+2` holds the literal `b`. -/
theorem emitConstRecord_runConfig_record {L : Nat} (b : Bool)
    (c : Configuration (M := (emitConstRecord b).toPhased.toTM) L)
    (hphase : (c.state.fst : Nat) = 0)
    (hroom : (c.head : Nat) + 3 < (emitConstRecord b).toPhased.toTM.tapeLength L) :
    (∀ q : Fin ((emitConstRecord b).toPhased.toTM.tapeLength L), (q : Nat) = (c.head : Nat) →
        (TM.runConfig (M := (emitConstRecord b).toPhased.toTM) c 3).tape q = true)
      ∧ (∀ q : Fin ((emitConstRecord b).toPhased.toTM.tapeLength L), (q : Nat) = (c.head : Nat) + 1 →
          (TM.runConfig (M := (emitConstRecord b).toPhased.toTM) c 3).tape q = false)
      ∧ (∀ q : Fin ((emitConstRecord b).toPhased.toTM.tapeLength L), (q : Nat) = (c.head : Nat) + 2 →
          (TM.runConfig (M := (emitConstRecord b).toPhased.toTM) c 3).tape q = b) := by
  obtain ⟨_, _, htape⟩ := emitConstRecord_runConfig_three b c hphase hroom
  refine ⟨?_, ?_, ?_⟩
  · intro q hq; rw [htape q, if_pos hq]
  · intro q hq; rw [htape q, if_neg (by omega), if_pos hq]
  · intro q hq; rw [htape q, if_neg (by omega), if_neg (by omega), if_pos hq]

end ContractExpansion
end Frontier
end Pnp4
