import Pnp4.Frontier.ContractExpansion.TreeMCSPEmitConstRecord

/-!
# `writeBits` — D2t-5a machine primitive: write a fixed bit-list rightward into a tape region

The first on-tape **machine** brick of D2t-5's realization.  `writeBits bs` is a monolithic
`bs.length + 1`-phase program that writes the fixed bit list `bs` left-to-right from the head, one cell per
step (phase `i < bs.length` writes `bs[i]`, moves right, advances to phase `i+1`; the final phase
`bs.length` accepts/idles).  It generalises `emitConstRecord`'s fixed 3-cell write to any fixed-width
payload.

This is the fixed-width writer the D2t-5a stack machines reuse: the control-stack `pushFrame` writes the
fixed per-tag frame `encodeCtrlFrame (tag, tag.arity)` (a fixed bit list once the tag is known from
`treeTagDispatch`), and leaf records (`encodeGateRecord (.const b)`) are fixed too.  (The *variable*-width
writes — a value-stack index `1^v` or an internal gate's operands — are separate binary→unary / copy
loops.)

`writeBits_runConfig`: from the write head at `p` (phase `0`) with `bs.length` cells of room, after
`bs.length` steps the program is at the accept phase `bs.length`, the head rests at `p + bs.length`, and the
window `[p, p + bs.length)` holds `bs` (tape elsewhere unchanged).  Bounded step-induction on the prefix
length (no `reachesSink`/measure needed — the run length is the fixed `bs.length`).

**Progress classification (AGENTS.md): Infrastructure** — a fixed-width tape-writer machine proven at the
configuration level; builds no verifier and proves no separation.  Standard `[propext, Classical.choice,
Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- Write the fixed bit list `bs` rightward: phase `i < bs.length` writes `bs[i]`, moves right, advances to
phase `i + 1`; phase `bs.length` accepts (idle: writes the scanned bit back, stays). -/
def writeBits (bs : List Bool) : ConstStatePhasedProgram Unit where
  numPhases := bs.length + 1
  startPhase := ⟨0, by omega⟩
  startState := ()
  acceptPhase := ⟨bs.length, by omega⟩
  acceptState := ()
  transition := fun i _ scan =>
    if h : i.val < bs.length then
      (⟨i.val + 1, by omega⟩, (), bs.getD i.val false, Move.right)
    else
      (i, (), scan, Move.stay)
  timeBound := fun _ => bs.length

@[simp] theorem writeBits_numPhases (bs : List Bool) : (writeBits bs).numPhases = bs.length + 1 := rfl
@[simp] theorem writeBits_startPhase_val (bs : List Bool) : ((writeBits bs).startPhase : Nat) = 0 := rfl
@[simp] theorem writeBits_acceptPhase_val (bs : List Bool) :
    ((writeBits bs).acceptPhase : Nat) = bs.length := rfl

/-- One write step (phase `k < bs.length`): write `bs[k]`, move right, advance to phase `k + 1`. -/
theorem writeBits_step {L : Nat} (bs : List Bool)
    (c : Configuration (M := (writeBits bs).toPhased.toTM) L)
    {i : Fin (writeBits bs).numPhases} {s : Unit} (k : Nat) (hk : k < bs.length)
    (hi : (i : Nat) = k) (hstate : c.state = ⟨i, s⟩)
    (hhead : (c.head : Nat) + 1 < (writeBits bs).toPhased.toTM.tapeLength L) :
    ((TM.stepConfig (M := (writeBits bs).toPhased.toTM) c).state).fst.val = k + 1
      ∧ ((TM.stepConfig (M := (writeBits bs).toPhased.toTM) c).head : Nat) = (c.head : Nat) + 1
      ∧ (TM.stepConfig (M := (writeBits bs).toPhased.toTM) c).tape
          = c.write c.head (bs.getD k false) := by
  have hph : ((writeBits bs).transition i s (c.tape c.head)).1.val = k + 1 := by
    simp [writeBits, hi, hk]
  have hmv : ((writeBits bs).transition i s (c.tape c.head)).2.2.2 = Move.right := by
    simp [writeBits, hi, hk]
  have hbt : ((writeBits bs).transition i s (c.tape c.head)).2.2.1 = bs.getD k false := by
    simp [writeBits, hi, hk]
  refine ⟨?_, ?_, ?_⟩
  · rw [ConstStatePhasedProgram.toTM_stepConfig_phase (writeBits bs) c hstate, hph]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_head (writeBits bs) c hstate, hmv,
      Configuration.moveHead_right_lt c hhead]
  · rw [ConstStatePhasedProgram.toTM_stepConfig_tape (writeBits bs) c hstate, hbt]

/-- Auxiliary: after `k ≤ bs.length` steps the head has advanced by `k`, the phase is `k`, and the window
`[p, p + k)` holds `bs`'s first `k` bits (tape elsewhere unchanged).  Induction on `k`. -/
theorem writeBits_runConfig_aux {L : Nat} (bs : List Bool)
    (c : Configuration (M := (writeBits bs).toPhased.toTM) L)
    (hphase : (c.state.fst : Nat) = 0)
    (hroom : (c.head : Nat) + bs.length < (writeBits bs).toPhased.toTM.tapeLength L) :
    ∀ k, k ≤ bs.length →
      ((TM.runConfig (M := (writeBits bs).toPhased.toTM) c k).state.fst : Nat) = k
        ∧ ((TM.runConfig (M := (writeBits bs).toPhased.toTM) c k).head : Nat) = (c.head : Nat) + k
        ∧ ∀ q : Fin ((writeBits bs).toPhased.toTM.tapeLength L),
            (TM.runConfig (M := (writeBits bs).toPhased.toTM) c k).tape q
              = if (c.head : Nat) ≤ (q : Nat) ∧ (q : Nat) < (c.head : Nat) + k
                then bs.getD ((q : Nat) - (c.head : Nat)) false
                else c.tape q := by
  intro k
  induction k with
  | zero =>
      intro _
      refine ⟨by simpa using hphase, by simp, ?_⟩
      intro q; simp
  | succ k ih =>
      intro hk
      obtain ⟨ihp, ihh, iht⟩ := ih (by omega)
      set d := TM.runConfig (M := (writeBits bs).toPhased.toTM) c k with hd
      have hdhead : (d.head : Nat) = (c.head : Nat) + k := ihh
      obtain ⟨sp, sh, st⟩ :=
        writeBits_step bs d (i := d.state.fst) (s := d.state.snd) k (by omega) ihp rfl
          (by rw [hdhead]; omega)
      have hsucc : TM.runConfig (M := (writeBits bs).toPhased.toTM) c (k + 1)
          = TM.stepConfig (M := (writeBits bs).toPhased.toTM) d := by
        rw [TM.runConfig_succ, ← hd]
      refine ⟨by rw [hsucc]; exact sp, by rw [hsucc, sh, hdhead]; omega, ?_⟩
      intro q
      rw [hsucc, st]
      by_cases hq : (q : Nat) = (c.head : Nat) + k
      · have hqd : q = d.head := Fin.ext (by rw [hdhead]; exact hq)
        rw [Configuration.write, dif_pos hqd, if_pos (by omega), hq]
        simp
      · have hqd : q ≠ d.head := fun h => hq (by rw [h, hdhead])
        rw [Configuration.write, dif_neg hqd, iht q]
        by_cases hlo : (c.head : Nat) ≤ (q : Nat)
        · by_cases hhi : (q : Nat) < (c.head : Nat) + k
          · rw [if_pos ⟨hlo, hhi⟩, if_pos ⟨hlo, by omega⟩]
          · rw [if_neg (by omega), if_neg (by omega)]
        · rw [if_neg (by omega), if_neg (by omega)]

/-- **`writeBits` run-through.**  From the write head at `p = c.head` (phase `0`) with `bs.length` cells of
room, after `bs.length` steps the program halts at the accept phase `bs.length`, the head rests at
`p + bs.length`, and the window `[p, p + bs.length)` holds exactly `bs` (cell `p + j = bs[j]`; tape
elsewhere unchanged). -/
theorem writeBits_runConfig {L : Nat} (bs : List Bool)
    (c : Configuration (M := (writeBits bs).toPhased.toTM) L)
    (hphase : (c.state.fst : Nat) = 0)
    (hroom : (c.head : Nat) + bs.length < (writeBits bs).toPhased.toTM.tapeLength L) :
    ((TM.runConfig (M := (writeBits bs).toPhased.toTM) c bs.length).state.fst : Nat) = bs.length
      ∧ ((TM.runConfig (M := (writeBits bs).toPhased.toTM) c bs.length).head : Nat)
          = (c.head : Nat) + bs.length
      ∧ ∀ q : Fin ((writeBits bs).toPhased.toTM.tapeLength L),
          (TM.runConfig (M := (writeBits bs).toPhased.toTM) c bs.length).tape q
            = if (c.head : Nat) ≤ (q : Nat) ∧ (q : Nat) < (c.head : Nat) + bs.length
              then bs.getD ((q : Nat) - (c.head : Nat)) false
              else c.tape q :=
  writeBits_runConfig_aux bs c hphase hroom bs.length (le_refl _)

end ContractExpansion
end Frontier
end Pnp4
