import Pnp4.Frontier.ContractExpansion.TreeMCSPClearIterProgram

/-!
# Region atom hops — D2t-5b (Block A5m-3a′): the single-cell movers and the probe, host-generic

The U3 segments covered the two scans; the arms' remaining navigation legs are the single-cell
movers and the probe.  Host-generic, fixed step counts, tape-preserving:

* `run_stepLeft_hop` — `2` steps (move left, redirect): phase `next`, head one left;
* `run_stepRight_hop` — `2` steps (move right, redirect): phase `next`, head one right;
* `run_probe_empty_hop` / `run_probe_frame_hop` — `3` steps (peek left, verdict, redirect): phase
  the verdict's redirect target, head one left — the branch taken is read off the peeked cell.

**Progress classification (AGENTS.md): Infrastructure** — host-generic run segments; proves no
separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP`
claim.** -/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- The write-back of the scanned bit leaves the tape unchanged. -/
private theorem write_self {M : TM} {L : Nat} (c : Configuration (M := M) L) :
    c.write c.head (c.tape c.head) = c.tape := by
  funext q
  by_cases hq : q = c.head
  · subst hq; simp [Configuration.write]
  · simp [Configuration.write, hq]

namespace RegionEmbedded

variable {U : ConstStatePhasedProgram Unit} {base next : Nat}

/-- **The left-step hop**: from the region's phase `base` at head `h ≥ 1`, `2` steps end at the
absolute phase `next`, head `h − 1`, tape unchanged. -/
theorem run_stepLeft_hop (hUP : RegionEmbedded U stepLeftOnce base next) {L : Nat}
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base) (hpos : 1 ≤ (c0.head : Nat)) :
    (((TM.runConfig (M := U.toPhased.toTM) c0 2).state).fst : Nat) = next
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 2).head : Nat) = (c0.head : Nat) - 1
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 2).tape = c0.tape := by
  have hne : ¬ (c0.head : Nat) = 0 := by omega
  rw [show (2 : Nat) = 1 + 1 from rfl, TM.runConfig_add, TM.runConfig_one, TM.runConfig_one]
  set c1 := TM.stepConfig (M := U.toPhased.toTM) c0 with hc1
  have hij : (c0.state.fst : Nat) = base + (⟨0, by simp [stepLeftOnce]⟩
      : Fin stepLeftOnce.numPhases).val := by simpa using hphase
  have hjne : (⟨0, by simp [stepLeftOnce]⟩ : Fin stepLeftOnce.numPhases).val
      ≠ (stepLeftOnce.acceptPhase : Nat) := by simp [stepLeftOnce]
  have hph1 : (c1.state.fst : Nat) = base + 1 := by
    rw [hc1, hUP.stepConfig_normal_phase c0 rfl _ hij hjne]
    simp [stepLeftOnce]
  have hhd1 : (c1.head : Nat) = (c0.head : Nat) - 1 := by
    rw [hc1, hUP.stepConfig_normal_head c0 rfl _ hij hjne]
    have hm : (stepLeftOnce.transition ⟨0, by simp [stepLeftOnce]⟩ ()
        (c0.tape c0.head)).snd.snd.snd = Move.left := by
      simp [stepLeftOnce]
    rw [hm]
    simp only [Configuration.moveHead, dif_neg hne]
  have htp1 : c1.tape = c0.tape := by
    rw [hc1, hUP.stepConfig_normal_tape c0 rfl _ hij hjne]
    have hb : (stepLeftOnce.transition ⟨0, by simp [stepLeftOnce]⟩ ()
        (c0.tape c0.head)).snd.snd.fst = c0.tape c0.head := by
      simp [stepLeftOnce]
    rw [hb]
    exact write_self c0
  have hij1 : (c1.state.fst : Nat) = base + (stepLeftOnce.acceptPhase : Nat) := by
    rw [hph1]; rfl
  refine ⟨?_, ?_, ?_⟩
  · exact hUP.stepConfig_accept_phase c1 rfl hij1
  · rw [hUP.stepConfig_accept_head c1 rfl hij1]; exact hhd1
  · rw [hUP.stepConfig_accept_tape c1 rfl hij1]; exact htp1

/-- **The right-step hop**: from the region's phase `base` (with head-room), `2` steps end at the
absolute phase `next`, head `h + 1`, tape unchanged. -/
theorem run_stepRight_hop (hUP : RegionEmbedded U stepRightOnce base next) {L : Nat}
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base)
    (hroom : (c0.head : Nat) + 1 < U.toPhased.toTM.tapeLength L) :
    (((TM.runConfig (M := U.toPhased.toTM) c0 2).state).fst : Nat) = next
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 2).head : Nat) = (c0.head : Nat) + 1
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 2).tape = c0.tape := by
  rw [show (2 : Nat) = 1 + 1 from rfl, TM.runConfig_add, TM.runConfig_one, TM.runConfig_one]
  set c1 := TM.stepConfig (M := U.toPhased.toTM) c0 with hc1
  have hij : (c0.state.fst : Nat) = base + (⟨0, by simp [stepRightOnce]⟩
      : Fin stepRightOnce.numPhases).val := by simpa using hphase
  have hjne : (⟨0, by simp [stepRightOnce]⟩ : Fin stepRightOnce.numPhases).val
      ≠ (stepRightOnce.acceptPhase : Nat) := by simp [stepRightOnce]
  have hph1 : (c1.state.fst : Nat) = base + 1 := by
    rw [hc1, hUP.stepConfig_normal_phase c0 rfl _ hij hjne]
    simp [stepRightOnce]
  have hhd1 : (c1.head : Nat) = (c0.head : Nat) + 1 := by
    rw [hc1, hUP.stepConfig_normal_head c0 rfl _ hij hjne]
    have hm : (stepRightOnce.transition ⟨0, by simp [stepRightOnce]⟩ ()
        (c0.tape c0.head)).snd.snd.snd = Move.right := by
      simp [stepRightOnce]
    rw [hm]
    simp only [Configuration.moveHead, dif_pos hroom]
  have htp1 : c1.tape = c0.tape := by
    rw [hc1, hUP.stepConfig_normal_tape c0 rfl _ hij hjne]
    have hb : (stepRightOnce.transition ⟨0, by simp [stepRightOnce]⟩ ()
        (c0.tape c0.head)).snd.snd.fst = c0.tape c0.head := by
      simp [stepRightOnce]
    rw [hb]
    exact write_self c0
  have hij1 : (c1.state.fst : Nat) = base + (stepRightOnce.acceptPhase : Nat) := by
    rw [hph1]; rfl
  refine ⟨?_, ?_, ?_⟩
  · exact hUP.stepConfig_accept_phase c1 rfl hij1
  · rw [hUP.stepConfig_accept_head c1 rfl hij1]; exact hhd1
  · rw [hUP.stepConfig_accept_tape c1 rfl hij1]; exact htp1

end RegionEmbedded

namespace RegionEmbeddedMulti

variable {U : ConstStatePhasedProgram Unit} {base : Nat} {redirect : Nat → Option Nat}

/-- **The probe hop, empty branch**: from the region's phase `base` at head `h ≥ 1` with the
peeked cell (`h − 1`) reading `0`, `3` steps (peek, the empty verdict, redirect) end at the
redirect target of the empty verdict, head `h − 1`, tape unchanged. -/
theorem run_probe_empty_hop (hUP : RegionEmbeddedMulti U settleProbe base redirect) {L : Nat}
    (hred0 : redirect 0 = none) (hred1 : redirect 1 = none) {nxt : Nat}
    (hred3 : redirect 3 = some nxt)
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base) (hpos : 1 ≤ (c0.head : Nat))
    (hpeek : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - 1 → c0.tape p = false) :
    (((TM.runConfig (M := U.toPhased.toTM) c0 3).state).fst : Nat) = nxt
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 3).head : Nat) = (c0.head : Nat) - 1
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 3).tape = c0.tape := by
  have hne : ¬ (c0.head : Nat) = 0 := by omega
  rw [show (3 : Nat) = (1 + 1) + 1 from rfl, TM.runConfig_add, TM.runConfig_add,
    TM.runConfig_one, TM.runConfig_one, TM.runConfig_one]
  set c1 := TM.stepConfig (M := U.toPhased.toTM) c0 with hc1
  have hij0 : (c0.state.fst : Nat) = base + (⟨0, by simp [settleProbe]⟩
      : Fin settleProbe.numPhases).val := by simpa using hphase
  have hph1 : (c1.state.fst : Nat) = base + 1 := by
    rw [hc1, hUP.stepConfig_normal_phase c0 rfl _ hij0 hred0]
    simp [settleProbe]
  have hhd1 : (c1.head : Nat) = (c0.head : Nat) - 1 := by
    rw [hc1, hUP.stepConfig_normal_head c0 rfl _ hij0 hred0]
    have hm : (settleProbe.transition ⟨0, by simp [settleProbe]⟩ ()
        (c0.tape c0.head)).snd.snd.snd = Move.left := by
      simp [settleProbe]
    rw [hm]
    simp only [Configuration.moveHead, dif_neg hne]
  have htp1 : c1.tape = c0.tape := by
    rw [hc1, hUP.stepConfig_normal_tape c0 rfl _ hij0 hred0]
    have hb : (settleProbe.transition ⟨0, by simp [settleProbe]⟩ ()
        (c0.tape c0.head)).snd.snd.fst = c0.tape c0.head := by
      simp [settleProbe]
    rw [hb]
    exact write_self c0
  set c2 := TM.stepConfig (M := U.toPhased.toTM) c1 with hc2
  have hbit1 : c1.tape c1.head = false := by
    rw [htp1]
    exact hpeek c1.head (by omega)
  have hij1 : (c1.state.fst : Nat) = base + (⟨1, by simp [settleProbe]⟩
      : Fin settleProbe.numPhases).val := by simpa using hph1
  have hph2 : (c2.state.fst : Nat) = base + 3 := by
    rw [hc2, hUP.stepConfig_normal_phase c1 rfl _ hij1 hred1]
    simp [settleProbe, hbit1]
  have hhd2 : (c2.head : Nat) = (c0.head : Nat) - 1 := by
    rw [hc2, hUP.stepConfig_normal_head c1 rfl _ hij1 hred1]
    have hm : (settleProbe.transition ⟨1, by simp [settleProbe]⟩ ()
        (c1.tape c1.head)).snd.snd.snd = Move.stay := by
      simp [settleProbe, hbit1]
    rw [hm]
    simpa [Configuration.moveHead] using hhd1
  have htp2 : c2.tape = c0.tape := by
    rw [hc2, hUP.stepConfig_normal_tape c1 rfl _ hij1 hred1]
    have hb : (settleProbe.transition ⟨1, by simp [settleProbe]⟩ ()
        (c1.tape c1.head)).snd.snd.fst = c1.tape c1.head := by
      simp [settleProbe, hbit1]
    rw [hb, write_self c1]
    exact htp1
  have hij2 : (c2.state.fst : Nat) = base + (⟨3, by simp [settleProbe]⟩
      : Fin settleProbe.numPhases).val := by simpa using hph2
  refine ⟨?_, ?_, ?_⟩
  · exact hUP.stepConfig_redirect_phase c2 rfl _ hij2 hred3
  · rw [hUP.stepConfig_redirect_head c2 rfl _ hij2 hred3]; exact hhd2
  · rw [hUP.stepConfig_redirect_tape c2 rfl _ hij2 hred3]; exact htp2

/-- **The probe hop, frame branch**: as `run_probe_empty_hop` with the peeked cell reading `1`,
ending at the frame verdict's redirect target. -/
theorem run_probe_frame_hop (hUP : RegionEmbeddedMulti U settleProbe base redirect) {L : Nat}
    (hred0 : redirect 0 = none) (hred1 : redirect 1 = none) {nxt : Nat}
    (hred2 : redirect 2 = some nxt)
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base) (hpos : 1 ≤ (c0.head : Nat))
    (hpeek : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - 1 → c0.tape p = true) :
    (((TM.runConfig (M := U.toPhased.toTM) c0 3).state).fst : Nat) = nxt
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 3).head : Nat) = (c0.head : Nat) - 1
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 3).tape = c0.tape := by
  have hne : ¬ (c0.head : Nat) = 0 := by omega
  rw [show (3 : Nat) = (1 + 1) + 1 from rfl, TM.runConfig_add, TM.runConfig_add,
    TM.runConfig_one, TM.runConfig_one, TM.runConfig_one]
  set c1 := TM.stepConfig (M := U.toPhased.toTM) c0 with hc1
  have hij0 : (c0.state.fst : Nat) = base + (⟨0, by simp [settleProbe]⟩
      : Fin settleProbe.numPhases).val := by simpa using hphase
  have hph1 : (c1.state.fst : Nat) = base + 1 := by
    rw [hc1, hUP.stepConfig_normal_phase c0 rfl _ hij0 hred0]
    simp [settleProbe]
  have hhd1 : (c1.head : Nat) = (c0.head : Nat) - 1 := by
    rw [hc1, hUP.stepConfig_normal_head c0 rfl _ hij0 hred0]
    have hm : (settleProbe.transition ⟨0, by simp [settleProbe]⟩ ()
        (c0.tape c0.head)).snd.snd.snd = Move.left := by
      simp [settleProbe]
    rw [hm]
    simp only [Configuration.moveHead, dif_neg hne]
  have htp1 : c1.tape = c0.tape := by
    rw [hc1, hUP.stepConfig_normal_tape c0 rfl _ hij0 hred0]
    have hb : (settleProbe.transition ⟨0, by simp [settleProbe]⟩ ()
        (c0.tape c0.head)).snd.snd.fst = c0.tape c0.head := by
      simp [settleProbe]
    rw [hb]
    exact write_self c0
  set c2 := TM.stepConfig (M := U.toPhased.toTM) c1 with hc2
  have hbit1 : c1.tape c1.head = true := by
    rw [htp1]
    exact hpeek c1.head (by omega)
  have hij1 : (c1.state.fst : Nat) = base + (⟨1, by simp [settleProbe]⟩
      : Fin settleProbe.numPhases).val := by simpa using hph1
  have hph2 : (c2.state.fst : Nat) = base + 2 := by
    rw [hc2, hUP.stepConfig_normal_phase c1 rfl _ hij1 hred1]
    simp [settleProbe, hbit1]
  have hhd2 : (c2.head : Nat) = (c0.head : Nat) - 1 := by
    rw [hc2, hUP.stepConfig_normal_head c1 rfl _ hij1 hred1]
    have hm : (settleProbe.transition ⟨1, by simp [settleProbe]⟩ ()
        (c1.tape c1.head)).snd.snd.snd = Move.stay := by
      simp [settleProbe, hbit1]
    rw [hm]
    simpa [Configuration.moveHead] using hhd1
  have htp2 : c2.tape = c0.tape := by
    rw [hc2, hUP.stepConfig_normal_tape c1 rfl _ hij1 hred1]
    have hb : (settleProbe.transition ⟨1, by simp [settleProbe]⟩ ()
        (c1.tape c1.head)).snd.snd.fst = c1.tape c1.head := by
      simp [settleProbe, hbit1]
    rw [hb, write_self c1]
    exact htp1
  have hij2 : (c2.state.fst : Nat) = base + (⟨2, by simp [settleProbe]⟩
      : Fin settleProbe.numPhases).val := by simpa using hph2
  refine ⟨?_, ?_, ?_⟩
  · exact hUP.stepConfig_redirect_phase c2 rfl _ hij2 hred2
  · rw [hUP.stepConfig_redirect_head c2 rfl _ hij2 hred2]; exact hhd2
  · rw [hUP.stepConfig_redirect_tape c2 rfl _ hij2 hred2]; exact htp2

end RegionEmbeddedMulti

end ContractExpansion
end Frontier
end Pnp4
