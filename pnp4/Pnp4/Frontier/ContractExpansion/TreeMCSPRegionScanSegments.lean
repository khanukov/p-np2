import Pnp4.Frontier.ContractExpansion.TreeMCSPRegionEmbedMulti

/-!
# Region scan segments — D2t-5b (Block A5m-U3): the corridor hops, host-generic

The driver's corridor hops are leftward/rightward `0`-scans onto a `1`-anchor.  With the region
contracts (A5m-U1/U2) their run inductions are provable **once, generically over the host**: any
machine `U` hosting `selfLoopScanLeft` (resp. `gammaSelfLoopScan`) as a region with exit `next`
performs the full hop — scan to the anchor, read it, hand off — in `(distance) + 2` steps, ending at
the absolute phase `next` with the head on the anchor and the tape untouched.

At assembly, every hop of every arm instantiates one of these two segments at its region base — no
per-hop re-proof.

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

/-- **The leftward-scan region segment, scanning half**: from the region's phase `base` (the scan
loop), `j` all-`0` cells retreat the head `j` cells left; the phase and tape are unchanged. -/
theorem run_scanLeft_scanning (hUP : RegionEmbedded U selfLoopScanLeft base next) {L : Nat}
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base) :
    ∀ j : Nat, j ≤ (c0.head : Nat) →
      (∀ p : Fin (U.toPhased.toTM.tapeLength L),
        (c0.head : Nat) - j < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = false) →
      (((TM.runConfig (M := U.toPhased.toTM) c0 j).state).fst : Nat) = base
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 j).head : Nat) = (c0.head : Nat) - j
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 j).tape = c0.tape := by
  intro j
  induction j with
  | zero => intro _ _; exact ⟨hphase, by simp, rfl⟩
  | succ j ih =>
      intro hj h0
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h0 p (by omega) hp2)
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := U.toPhased.toTM) c0 j with hc
      have hbit : c.tape c.head = false := by
        rw [htp]; exact h0 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hheadne : ¬ (c.head : Nat) = 0 := by rw [hhd]; omega
      have hij : (c.state.fst : Nat) = base + (⟨0, by simp [selfLoopScanLeft]⟩
          : Fin selfLoopScanLeft.numPhases).val := by
        simpa using hph
      have hjne : (⟨0, by simp [selfLoopScanLeft]⟩ : Fin selfLoopScanLeft.numPhases).val
          ≠ (selfLoopScanLeft.acceptPhase : Nat) := by simp [selfLoopScanLeft]
      refine ⟨?_, ?_, ?_⟩
      · rw [hUP.stepConfig_normal_phase c rfl _ hij hjne]
        simp [selfLoopScanLeft, hbit]
      · rw [hUP.stepConfig_normal_head c rfl _ hij hjne]
        have hm : (selfLoopScanLeft.transition ⟨0, by simp [selfLoopScanLeft]⟩ ()
            (c.tape c.head)).snd.snd.snd = Move.left := by
          simp [selfLoopScanLeft, hbit]
        rw [hm]
        simp only [Configuration.moveHead, dif_neg hheadne]
        rw [hhd]; omega
      · rw [hUP.stepConfig_normal_tape c rfl _ hij hjne]
        have hb : (selfLoopScanLeft.transition ⟨0, by simp [selfLoopScanLeft]⟩ ()
            (c.tape c.head)).snd.snd.fst = c.tape c.head := by
          simp [selfLoopScanLeft, hbit]
        rw [hb]
        have : c.write c.head (c.tape c.head) = c.tape := by
          funext q
          by_cases hq : q = c.head
          · subst hq; simp [Configuration.write]
          · simp [Configuration.write, hq]
        rw [this, htp]

/-- **The leftward-scan region hop**: from the region's phase `base` at head `h₀`, with a
`1`-anchor at `k < h₀` and `0`s in between, `(h₀ − k) + 2` steps (retreat, read the anchor, hand
off) end at the absolute phase `next`, head on the anchor, tape unchanged. -/
theorem run_scanLeft_hop (hUP : RegionEmbedded U selfLoopScanLeft base next) {L : Nat}
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base) (k : Nat) (hk : k < (c0.head : Nat))
    (hzeros : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      k < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = false)
    (hterm : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = k → c0.tape p = true) :
    (((TM.runConfig (M := U.toPhased.toTM) c0 (((c0.head : Nat) - k) + 2)).state).fst : Nat)
        = next
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 (((c0.head : Nat) - k) + 2)).head : Nat) = k
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 (((c0.head : Nat) - k) + 2)).tape = c0.tape := by
  obtain ⟨hph, hhd, htp⟩ :=
    run_scanLeft_scanning hUP c0 hphase ((c0.head : Nat) - k) (by omega)
      (fun p hp1 hp2 => hzeros p (by omega) hp2)
  have hsteps : ((c0.head : Nat) - k) + 2 = (((c0.head : Nat) - k) + 1) + 1 := by omega
  rw [hsteps, TM.runConfig_succ, TM.runConfig_succ]
  set c := TM.runConfig (M := U.toPhased.toTM) c0 ((c0.head : Nat) - k) with hc
  have hhdk : (c.head : Nat) = k := by rw [hhd]; omega
  have hbit : c.tape c.head = true := by rw [htp]; exact hterm c.head hhdk
  -- The anchor step: phase base → base + 1 (the scan's accept), head stays, tape kept.
  set c1 := TM.stepConfig (M := U.toPhased.toTM) c with hc1
  have hij : (c.state.fst : Nat) = base + (⟨0, by simp [selfLoopScanLeft]⟩
      : Fin selfLoopScanLeft.numPhases).val := by simpa using hph
  have hjne : (⟨0, by simp [selfLoopScanLeft]⟩ : Fin selfLoopScanLeft.numPhases).val
      ≠ (selfLoopScanLeft.acceptPhase : Nat) := by simp [selfLoopScanLeft]
  have hph1 : (c1.state.fst : Nat) = base + 1 := by
    rw [hc1, hUP.stepConfig_normal_phase c rfl _ hij hjne]
    simp [selfLoopScanLeft, hbit]
  have hhd1 : (c1.head : Nat) = k := by
    rw [hc1, hUP.stepConfig_normal_head c rfl _ hij hjne]
    have hm : (selfLoopScanLeft.transition ⟨0, by simp [selfLoopScanLeft]⟩ ()
        (c.tape c.head)).snd.snd.snd = Move.stay := by
      simp [selfLoopScanLeft, hbit]
    rw [hm]
    simpa [Configuration.moveHead] using hhdk
  have htp1 : c1.tape = c0.tape := by
    rw [hc1, hUP.stepConfig_normal_tape c rfl _ hij hjne]
    have hb : (selfLoopScanLeft.transition ⟨0, by simp [selfLoopScanLeft]⟩ ()
        (c.tape c.head)).snd.snd.fst = c.tape c.head := by
      simp [selfLoopScanLeft, hbit]
    rw [hb]
    have : c.write c.head (c.tape c.head) = c.tape := by
      funext q
      by_cases hq : q = c.head
      · subst hq; simp [Configuration.write]
      · simp [Configuration.write, hq]
    rw [this, htp]
  -- The redirect step (base + 1 = the region's accept).
  have hij1 : (c1.state.fst : Nat) = base + (selfLoopScanLeft.acceptPhase : Nat) := by
    rw [hph1]; rfl
  refine ⟨?_, ?_, ?_⟩
  · exact hUP.stepConfig_accept_phase c1 rfl hij1
  · rw [hUP.stepConfig_accept_head c1 rfl hij1]
    exact hhd1
  · rw [hUP.stepConfig_accept_tape c1 rfl hij1]
    exact htp1

/-- **The rightward-scan region segment, scanning half** (`gammaSelfLoopScan`): from the region's
phase `base`, `j` all-`0` cells advance the head `j` cells right (with head-room); phase and tape
unchanged. -/
theorem run_scanRight_scanning (hUP : RegionEmbedded U gammaSelfLoopScan base next) {L : Nat}
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base) :
    ∀ j : Nat, (c0.head : Nat) + j < U.toPhased.toTM.tapeLength L →
      (∀ p : Fin (U.toPhased.toTM.tapeLength L),
        (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + j → c0.tape p = false) →
      (((TM.runConfig (M := U.toPhased.toTM) c0 j).state).fst : Nat) = base
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 j).head : Nat) = (c0.head : Nat) + j
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 j).tape = c0.tape := by
  intro j
  induction j with
  | zero => intro _ _; exact ⟨hphase, by simp, rfl⟩
  | succ j ih =>
      intro hj h0
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h0 p hp1 (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := U.toPhased.toTM) c0 j with hc
      have hbit : c.tape c.head = false := by
        rw [htp]; exact h0 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hroom : (c.head : Nat) + 1 < U.toPhased.toTM.tapeLength L := by
        rw [hhd]; omega
      have hij : (c.state.fst : Nat) = base + (⟨0, by simp [gammaSelfLoopScan]⟩
          : Fin gammaSelfLoopScan.numPhases).val := by simpa using hph
      have hjne : (⟨0, by simp [gammaSelfLoopScan]⟩ : Fin gammaSelfLoopScan.numPhases).val
          ≠ (gammaSelfLoopScan.acceptPhase : Nat) := by simp [gammaSelfLoopScan]
      refine ⟨?_, ?_, ?_⟩
      · rw [hUP.stepConfig_normal_phase c rfl _ hij hjne]
        simp [gammaSelfLoopScan, hbit]
      · rw [hUP.stepConfig_normal_head c rfl _ hij hjne]
        have hm : (gammaSelfLoopScan.transition ⟨0, by simp [gammaSelfLoopScan]⟩ ()
            (c.tape c.head)).snd.snd.snd = Move.right := by
          simp [gammaSelfLoopScan, hbit]
        rw [hm]
        simp only [Configuration.moveHead, dif_pos hroom]
        rw [hhd]
        omega
      · rw [hUP.stepConfig_normal_tape c rfl _ hij hjne]
        have hb : (gammaSelfLoopScan.transition ⟨0, by simp [gammaSelfLoopScan]⟩ ()
            (c.tape c.head)).snd.snd.fst = c.tape c.head := by
          simp [gammaSelfLoopScan, hbit]
        rw [hb]
        have : c.write c.head (c.tape c.head) = c.tape := by
          funext q
          by_cases hq : q = c.head
          · subst hq; simp [Configuration.write]
          · simp [Configuration.write, hq]
        rw [this, htp]

/-- **The rightward-scan region hop**: from the region's phase `base`, `0`s on `[head, head + m)`
and a `1`-anchor at `head + m` (in range), `m + 2` steps end at the absolute phase `next`, head on
the anchor, tape unchanged. -/
theorem run_scanRight_hop (hUP : RegionEmbedded U gammaSelfLoopScan base next) {L : Nat}
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base) (m : Nat)
    (hroom : (c0.head : Nat) + m < U.toPhased.toTM.tapeLength L)
    (hzeros : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + m → c0.tape p = false)
    (hterm : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + m → c0.tape p = true) :
    (((TM.runConfig (M := U.toPhased.toTM) c0 (m + 2)).state).fst : Nat) = next
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 (m + 2)).head : Nat) = (c0.head : Nat) + m
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 (m + 2)).tape = c0.tape := by
  obtain ⟨hph, hhd, htp⟩ := run_scanRight_scanning hUP c0 hphase m hroom hzeros
  have hsteps : m + 2 = (m + 1) + 1 := by omega
  rw [hsteps, TM.runConfig_succ, TM.runConfig_succ]
  set c := TM.runConfig (M := U.toPhased.toTM) c0 m with hc
  have hhdk : (c.head : Nat) = (c0.head : Nat) + m := by rw [hhd]
  have hbit : c.tape c.head = true := by rw [htp]; exact hterm c.head hhdk
  set c1 := TM.stepConfig (M := U.toPhased.toTM) c with hc1
  have hij : (c.state.fst : Nat) = base + (⟨0, by simp [gammaSelfLoopScan]⟩
      : Fin gammaSelfLoopScan.numPhases).val := by simpa using hph
  have hjne : (⟨0, by simp [gammaSelfLoopScan]⟩ : Fin gammaSelfLoopScan.numPhases).val
      ≠ (gammaSelfLoopScan.acceptPhase : Nat) := by simp [gammaSelfLoopScan]
  have hph1 : (c1.state.fst : Nat) = base + 1 := by
    rw [hc1, hUP.stepConfig_normal_phase c rfl _ hij hjne]
    simp [gammaSelfLoopScan, hbit]
  have hhd1 : (c1.head : Nat) = (c0.head : Nat) + m := by
    rw [hc1, hUP.stepConfig_normal_head c rfl _ hij hjne]
    have hm : (gammaSelfLoopScan.transition ⟨0, by simp [gammaSelfLoopScan]⟩ ()
        (c.tape c.head)).snd.snd.snd = Move.stay := by
      simp [gammaSelfLoopScan, hbit]
    rw [hm]
    simpa [Configuration.moveHead] using hhdk
  have htp1 : c1.tape = c0.tape := by
    rw [hc1, hUP.stepConfig_normal_tape c rfl _ hij hjne]
    have hb : (gammaSelfLoopScan.transition ⟨0, by simp [gammaSelfLoopScan]⟩ ()
        (c.tape c.head)).snd.snd.fst = c.tape c.head := by
      simp [gammaSelfLoopScan, hbit]
    rw [hb]
    have : c.write c.head (c.tape c.head) = c.tape := by
      funext q
      by_cases hq : q = c.head
      · subst hq; simp [Configuration.write]
      · simp [Configuration.write, hq]
    rw [this, htp]
  have hij1 : (c1.state.fst : Nat) = base + (gammaSelfLoopScan.acceptPhase : Nat) := by
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
