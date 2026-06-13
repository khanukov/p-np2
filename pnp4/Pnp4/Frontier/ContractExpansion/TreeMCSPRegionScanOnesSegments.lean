import Pnp4.Frontier.ContractExpansion.TreeMCSPRegionEmbedMulti
import Pnp4.Frontier.ContractExpansion.TreeMCSPScanLeftOneProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPScanRightOneProgram

/-!
# Region scan-over-ones segments — D2t-5b (Block A5m-6a, transfer): the `SHW` crossers, host-generic

The bit-duals of the A5m-U3 segments: the emit arms cross the shadow-count zone's `1`-block in both
directions, and the motion primitives are `selfLoopScanLeftOne` / `selfLoopScanRightOne` — scan over
`1`s, stop on the first `0`.  With the region contracts their run inductions are provable once,
generically over the host `U`: a hosted ones-scan with exit `next` performs the full hop — cross the
ones, read the terminating `0`, hand off — in `(distance) + 2` steps, ending at the absolute phase
`next` with the head on the terminator and the tape untouched.

**Progress classification (AGENTS.md): Infrastructure** — host-generic run segments for verifier
machine components; builds no machine and proves no separation.  Standard `[propext,
Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

namespace RegionEmbedded

variable {U : ConstStatePhasedProgram Unit} {base next : Nat}

/-- **The leftward ones-scan region segment, scanning half**: from the region's phase `base` (the
scan loop), `j` all-`1` cells retreat the head `j` cells left; the phase and tape are unchanged. -/
theorem run_scanLeftOne_scanning (hUP : RegionEmbedded U selfLoopScanLeftOne base next) {L : Nat}
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base) :
    ∀ j : Nat, j ≤ (c0.head : Nat) →
      (∀ p : Fin (U.toPhased.toTM.tapeLength L),
        (c0.head : Nat) - j < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = true) →
      (((TM.runConfig (M := U.toPhased.toTM) c0 j).state).fst : Nat) = base
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 j).head : Nat) = (c0.head : Nat) - j
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 j).tape = c0.tape := by
  intro j
  induction j with
  | zero => intro _ _; exact ⟨hphase, by simp, rfl⟩
  | succ j ih =>
      intro hj h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h1 p (by omega) hp2)
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := U.toPhased.toTM) c0 j with hc
      have hbit : c.tape c.head = true := by
        rw [htp]; exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hheadne : ¬ (c.head : Nat) = 0 := by rw [hhd]; omega
      have hij : (c.state.fst : Nat) = base + (⟨0, by simp [selfLoopScanLeftOne]⟩
          : Fin selfLoopScanLeftOne.numPhases).val := by
        simpa using hph
      have hjne : (⟨0, by simp [selfLoopScanLeftOne]⟩ : Fin selfLoopScanLeftOne.numPhases).val
          ≠ (selfLoopScanLeftOne.acceptPhase : Nat) := by simp [selfLoopScanLeftOne]
      refine ⟨?_, ?_, ?_⟩
      · rw [hUP.stepConfig_normal_phase c rfl _ hij hjne]
        simp [selfLoopScanLeftOne, hbit]
      · rw [hUP.stepConfig_normal_head c rfl _ hij hjne]
        have hm : (selfLoopScanLeftOne.transition ⟨0, by simp [selfLoopScanLeftOne]⟩ ()
            (c.tape c.head)).snd.snd.snd = Move.left := by
          simp [selfLoopScanLeftOne, hbit]
        rw [hm]
        simp only [Configuration.moveHead, dif_neg hheadne]
        rw [hhd]; omega
      · rw [hUP.stepConfig_normal_tape c rfl _ hij hjne]
        have hb : (selfLoopScanLeftOne.transition ⟨0, by simp [selfLoopScanLeftOne]⟩ ()
            (c.tape c.head)).snd.snd.fst = c.tape c.head := by
          simp [selfLoopScanLeftOne, hbit]
        rw [hb]
        have : c.write c.head (c.tape c.head) = c.tape := by
          funext q
          by_cases hq : q = c.head
          · subst hq; simp [Configuration.write]
          · simp [Configuration.write, hq]
        rw [this, htp]

/-- **The leftward ones-scan region hop**: from the region's phase `base` at head `h₀`, with a
`0`-terminator at `k < h₀` and `1`s in between, `(h₀ − k) + 2` steps (retreat, read the
terminator, hand off) end at the absolute phase `next`, head on the terminator, tape unchanged. -/
theorem run_scanLeftOne_hop (hUP : RegionEmbedded U selfLoopScanLeftOne base next) {L : Nat}
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base) (k : Nat) (hk : k < (c0.head : Nat))
    (hones : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      k < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = true)
    (hterm : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = k → c0.tape p = false) :
    (((TM.runConfig (M := U.toPhased.toTM) c0 (((c0.head : Nat) - k) + 2)).state).fst : Nat)
        = next
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 (((c0.head : Nat) - k) + 2)).head : Nat) = k
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 (((c0.head : Nat) - k) + 2)).tape = c0.tape := by
  obtain ⟨hph, hhd, htp⟩ :=
    run_scanLeftOne_scanning hUP c0 hphase ((c0.head : Nat) - k) (by omega)
      (fun p hp1 hp2 => hones p (by omega) hp2)
  have hsteps : ((c0.head : Nat) - k) + 2 = (((c0.head : Nat) - k) + 1) + 1 := by omega
  rw [hsteps, TM.runConfig_succ, TM.runConfig_succ]
  set c := TM.runConfig (M := U.toPhased.toTM) c0 ((c0.head : Nat) - k) with hc
  have hhdk : (c.head : Nat) = k := by rw [hhd]; omega
  have hbit : c.tape c.head = false := by rw [htp]; exact hterm c.head hhdk
  -- The terminator step: phase base → base + 1 (the scan's accept), head stays, tape kept.
  set c1 := TM.stepConfig (M := U.toPhased.toTM) c with hc1
  have hij : (c.state.fst : Nat) = base + (⟨0, by simp [selfLoopScanLeftOne]⟩
      : Fin selfLoopScanLeftOne.numPhases).val := by simpa using hph
  have hjne : (⟨0, by simp [selfLoopScanLeftOne]⟩ : Fin selfLoopScanLeftOne.numPhases).val
      ≠ (selfLoopScanLeftOne.acceptPhase : Nat) := by simp [selfLoopScanLeftOne]
  have hph1 : (c1.state.fst : Nat) = base + 1 := by
    rw [hc1, hUP.stepConfig_normal_phase c rfl _ hij hjne]
    simp [selfLoopScanLeftOne, hbit]
  have hhd1 : (c1.head : Nat) = k := by
    rw [hc1, hUP.stepConfig_normal_head c rfl _ hij hjne]
    have hm : (selfLoopScanLeftOne.transition ⟨0, by simp [selfLoopScanLeftOne]⟩ ()
        (c.tape c.head)).snd.snd.snd = Move.stay := by
      simp [selfLoopScanLeftOne, hbit]
    rw [hm]
    simpa [Configuration.moveHead] using hhdk
  have htp1 : c1.tape = c0.tape := by
    rw [hc1, hUP.stepConfig_normal_tape c rfl _ hij hjne]
    have hb : (selfLoopScanLeftOne.transition ⟨0, by simp [selfLoopScanLeftOne]⟩ ()
        (c.tape c.head)).snd.snd.fst = c.tape c.head := by
      simp [selfLoopScanLeftOne, hbit]
    rw [hb]
    have : c.write c.head (c.tape c.head) = c.tape := by
      funext q
      by_cases hq : q = c.head
      · subst hq; simp [Configuration.write]
      · simp [Configuration.write, hq]
    rw [this, htp]
  -- The redirect step (base + 1 = the region's accept).
  have hij1 : (c1.state.fst : Nat) = base + (selfLoopScanLeftOne.acceptPhase : Nat) := by
    rw [hph1]; rfl
  refine ⟨?_, ?_, ?_⟩
  · exact hUP.stepConfig_accept_phase c1 rfl hij1
  · rw [hUP.stepConfig_accept_head c1 rfl hij1]
    exact hhd1
  · rw [hUP.stepConfig_accept_tape c1 rfl hij1]
    exact htp1

/-- **The rightward ones-scan region segment, scanning half** (`selfLoopScanRightOne`): from the
region's phase `base`, `j` all-`1` cells advance the head `j` cells right (with head-room); phase
and tape unchanged. -/
theorem run_scanRightOne_scanning (hUP : RegionEmbedded U selfLoopScanRightOne base next)
    {L : Nat} (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base) :
    ∀ j : Nat, (c0.head : Nat) + j < U.toPhased.toTM.tapeLength L →
      (∀ p : Fin (U.toPhased.toTM.tapeLength L),
        (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + j → c0.tape p = true) →
      (((TM.runConfig (M := U.toPhased.toTM) c0 j).state).fst : Nat) = base
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 j).head : Nat) = (c0.head : Nat) + j
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 j).tape = c0.tape := by
  intro j
  induction j with
  | zero => intro _ _; exact ⟨hphase, by simp, rfl⟩
  | succ j ih =>
      intro hj h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h1 p hp1 (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := U.toPhased.toTM) c0 j with hc
      have hbit : c.tape c.head = true := by
        rw [htp]; exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hroom : (c.head : Nat) + 1 < U.toPhased.toTM.tapeLength L := by
        rw [hhd]; omega
      have hij : (c.state.fst : Nat) = base + (⟨0, by simp [selfLoopScanRightOne]⟩
          : Fin selfLoopScanRightOne.numPhases).val := by simpa using hph
      have hjne : (⟨0, by simp [selfLoopScanRightOne]⟩ : Fin selfLoopScanRightOne.numPhases).val
          ≠ (selfLoopScanRightOne.acceptPhase : Nat) := by simp [selfLoopScanRightOne]
      refine ⟨?_, ?_, ?_⟩
      · rw [hUP.stepConfig_normal_phase c rfl _ hij hjne]
        simp [selfLoopScanRightOne, hbit]
      · rw [hUP.stepConfig_normal_head c rfl _ hij hjne]
        have hm : (selfLoopScanRightOne.transition ⟨0, by simp [selfLoopScanRightOne]⟩ ()
            (c.tape c.head)).snd.snd.snd = Move.right := by
          simp [selfLoopScanRightOne, hbit]
        rw [hm]
        simp only [Configuration.moveHead, dif_pos hroom]
        rw [hhd]
        omega
      · rw [hUP.stepConfig_normal_tape c rfl _ hij hjne]
        have hb : (selfLoopScanRightOne.transition ⟨0, by simp [selfLoopScanRightOne]⟩ ()
            (c.tape c.head)).snd.snd.fst = c.tape c.head := by
          simp [selfLoopScanRightOne, hbit]
        rw [hb]
        have : c.write c.head (c.tape c.head) = c.tape := by
          funext q
          by_cases hq : q = c.head
          · subst hq; simp [Configuration.write]
          · simp [Configuration.write, hq]
        rw [this, htp]

/-- **The rightward ones-scan region hop**: from the region's phase `base`, `1`s on
`[head, head + m)` and a `0`-terminator at `head + m` (in range), `m + 2` steps end at the
absolute phase `next`, head on the terminator, tape unchanged. -/
theorem run_scanRightOne_hop (hUP : RegionEmbedded U selfLoopScanRightOne base next) {L : Nat}
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base) (m : Nat)
    (hroom : (c0.head : Nat) + m < U.toPhased.toTM.tapeLength L)
    (hones : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + m → c0.tape p = true)
    (hterm : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + m → c0.tape p = false) :
    (((TM.runConfig (M := U.toPhased.toTM) c0 (m + 2)).state).fst : Nat) = next
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 (m + 2)).head : Nat) = (c0.head : Nat) + m
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 (m + 2)).tape = c0.tape := by
  obtain ⟨hph, hhd, htp⟩ := run_scanRightOne_scanning hUP c0 hphase m hroom hones
  have hsteps : m + 2 = (m + 1) + 1 := by omega
  rw [hsteps, TM.runConfig_succ, TM.runConfig_succ]
  set c := TM.runConfig (M := U.toPhased.toTM) c0 m with hc
  have hhdk : (c.head : Nat) = (c0.head : Nat) + m := by rw [hhd]
  have hbit : c.tape c.head = false := by rw [htp]; exact hterm c.head hhdk
  set c1 := TM.stepConfig (M := U.toPhased.toTM) c with hc1
  have hij : (c.state.fst : Nat) = base + (⟨0, by simp [selfLoopScanRightOne]⟩
      : Fin selfLoopScanRightOne.numPhases).val := by simpa using hph
  have hjne : (⟨0, by simp [selfLoopScanRightOne]⟩ : Fin selfLoopScanRightOne.numPhases).val
      ≠ (selfLoopScanRightOne.acceptPhase : Nat) := by simp [selfLoopScanRightOne]
  have hph1 : (c1.state.fst : Nat) = base + 1 := by
    rw [hc1, hUP.stepConfig_normal_phase c rfl _ hij hjne]
    simp [selfLoopScanRightOne, hbit]
  have hhd1 : (c1.head : Nat) = (c0.head : Nat) + m := by
    rw [hc1, hUP.stepConfig_normal_head c rfl _ hij hjne]
    have hm : (selfLoopScanRightOne.transition ⟨0, by simp [selfLoopScanRightOne]⟩ ()
        (c.tape c.head)).snd.snd.snd = Move.stay := by
      simp [selfLoopScanRightOne, hbit]
    rw [hm]
    simpa [Configuration.moveHead] using hhdk
  have htp1 : c1.tape = c0.tape := by
    rw [hc1, hUP.stepConfig_normal_tape c rfl _ hij hjne]
    have hb : (selfLoopScanRightOne.transition ⟨0, by simp [selfLoopScanRightOne]⟩ ()
        (c.tape c.head)).snd.snd.fst = c.tape c.head := by
      simp [selfLoopScanRightOne, hbit]
    rw [hb]
    have : c.write c.head (c.tape c.head) = c.tape := by
      funext q
      by_cases hq : q = c.head
      · subst hq; simp [Configuration.write]
      · simp [Configuration.write, hq]
    rw [this, htp]
  have hij1 : (c1.state.fst : Nat) = base + (selfLoopScanRightOne.acceptPhase : Nat) := by
    rw [hph1]; rfl
  refine ⟨?_, ?_, ?_⟩
  · exact hUP.stepConfig_accept_phase c1 rfl hij1
  · rw [hUP.stepConfig_accept_head c1 rfl hij1]
    exact hhd1
  · rw [hUP.stepConfig_accept_tape c1 rfl hij1]
    exact htp1

end RegionEmbedded

end ContractExpansion
end Frontier
end Pnp4
