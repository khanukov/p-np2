import Pnp4.Frontier.ContractExpansion.TreeMCSPRegionScanSegments
import Pnp4.Frontier.ContractExpansion.TreeMCSPScanLeftOneProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPScanRightOneProgram
import Pnp4.Frontier.ContractExpansion.TreeMCSPStepRightBranch

/-!
# Region hops for the `1`-run scanners and the right-step branch — D2t-6b (M1 prep)

The value-push machine (A5m-V / M1) walks through unary **`1`-runs** (the shadow-count block, the
growing value entry) and branches on the cell right of its home anchor.  The component programs
exist (`selfLoopScanLeftOne`, `selfLoopScanRightOne`, `stepRightThenBranch`); this module supplies
their **region hop lemmas** in the style of `TreeMCSPRegionScanSegments` — exact step counts, the
landing head, and the untouched tape, all stated against a `RegionEmbedded` /
`RegionEmbeddedMulti` contract so any union machine gets them by one instantiation.

**Progress classification (AGENTS.md): Infrastructure** — component run lemmas for the
verifier-track machine builder; builds no machine and proves no separation.  Standard `[propext,
Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

namespace RegionEmbedded

variable {U : ConstStatePhasedProgram Unit} {base next : Nat}

/-! ### Leftward scan over a `1`-run (`selfLoopScanLeftOne`) -/

/-- Scanning segment: while the scanned cells are `1`, the region's phase `base` retreats left one
cell per step, tape unchanged. -/
theorem run_scanLeftOnes_scanning (hUP : RegionEmbedded U selfLoopScanLeftOne base next) {L : Nat}
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

/-- **The leftward `1`-run hop**: from the region's phase `base` at head `h₀`, with `1`s on
`(k, h₀]` and a `0`-stop at `k < h₀`, `(h₀ − k) + 2` steps end at the absolute phase `next`, head
on the stop cell `k`, tape unchanged. -/
theorem run_scanLeftOnes_hop (hUP : RegionEmbedded U selfLoopScanLeftOne base next) {L : Nat}
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base) (k : Nat) (hk : k < (c0.head : Nat))
    (hones : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      k < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = true)
    (hstop : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = k → c0.tape p = false) :
    (((TM.runConfig (M := U.toPhased.toTM) c0 (((c0.head : Nat) - k) + 2)).state).fst : Nat)
        = next
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 (((c0.head : Nat) - k) + 2)).head : Nat) = k
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 (((c0.head : Nat) - k) + 2)).tape = c0.tape := by
  obtain ⟨hph, hhd, htp⟩ :=
    run_scanLeftOnes_scanning hUP c0 hphase ((c0.head : Nat) - k) (by omega)
      (fun p hp1 hp2 => hones p (by omega) hp2)
  have hsteps : ((c0.head : Nat) - k) + 2 = (((c0.head : Nat) - k) + 1) + 1 := by omega
  rw [hsteps, TM.runConfig_succ, TM.runConfig_succ]
  set c := TM.runConfig (M := U.toPhased.toTM) c0 ((c0.head : Nat) - k) with hc
  have hhdk : (c.head : Nat) = k := by rw [hhd]; omega
  have hbit : c.tape c.head = false := by rw [htp]; exact hstop c.head hhdk
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
  have hij1 : (c1.state.fst : Nat) = base + (selfLoopScanLeftOne.acceptPhase : Nat) := by
    rw [hph1]; rfl
  refine ⟨?_, ?_, ?_⟩
  · exact hUP.stepConfig_accept_phase c1 rfl hij1
  · rw [hUP.stepConfig_accept_head c1 rfl hij1]; exact hhd1
  · rw [hUP.stepConfig_accept_tape c1 rfl hij1]; exact htp1

/-! ### Rightward scan over a `1`-run (`selfLoopScanRightOne`) -/

/-- Scanning segment: while the scanned cells are `1`, the region's phase `base` advances right one
cell per step, tape unchanged. -/
theorem run_scanRightOnes_scanning (hUP : RegionEmbedded U selfLoopScanRightOne base next)
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
          : Fin selfLoopScanRightOne.numPhases).val := by
        simpa using hph
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

/-- **The rightward `1`-run hop**: from the region's phase `base` at head `h₀`, with `1`s on
`[h₀, h₀ + m)` and a `0`-stop at `h₀ + m` (in range), `m + 2` steps end at the absolute phase
`next`, head on the stop cell `h₀ + m`, tape unchanged. -/
theorem run_scanRightOnes_hop (hUP : RegionEmbedded U selfLoopScanRightOne base next) {L : Nat}
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base) (m : Nat)
    (hroom : (c0.head : Nat) + m < U.toPhased.toTM.tapeLength L)
    (hones : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + m → c0.tape p = true)
    (hstop : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + m → c0.tape p = false) :
    (((TM.runConfig (M := U.toPhased.toTM) c0 (m + 2)).state).fst : Nat) = next
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 (m + 2)).head : Nat) = (c0.head : Nat) + m
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 (m + 2)).tape = c0.tape := by
  obtain ⟨hph, hhd, htp⟩ := run_scanRightOnes_scanning hUP c0 hphase m hroom hones
  have hsteps : m + 2 = (m + 1) + 1 := by omega
  rw [hsteps, TM.runConfig_succ, TM.runConfig_succ]
  set c := TM.runConfig (M := U.toPhased.toTM) c0 m with hc
  have hhdk : (c.head : Nat) = (c0.head : Nat) + m := by rw [hhd]
  have hbit : c.tape c.head = false := by rw [htp]; exact hstop c.head hhdk
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
  · rw [hUP.stepConfig_accept_head c1 rfl hij1]; exact hhd1
  · rw [hUP.stepConfig_accept_tape c1 rfl hij1]; exact htp1

end RegionEmbedded

namespace RegionEmbeddedMulti

variable {U : ConstStatePhasedProgram Unit} {base : Nat} {redirect : Nat → Option Nat}

/-! ### The right-step branch (`stepRightThenBranch`) -/

/-- **The branch hop on a `1`**: from the region's phase `base` (head-room available), with the
right neighbour reading `1` and the `1`-verdict phase `2` redirected to `next1`, `3` steps end at
the absolute phase `next1`, head one cell right, tape unchanged. -/
theorem run_stepRightBranch_hop_one
    (hUP : RegionEmbeddedMulti U stepRightThenBranch base redirect) {L : Nat}
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base)
    (hroom : (c0.head : Nat) + 1 < U.toPhased.toTM.tapeLength L)
    (hred0 : redirect 0 = none) (hred1 : redirect 1 = none)
    {next1 : Nat} (hred2 : redirect 2 = some next1)
    (hbit : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 → c0.tape p = true) :
    (((TM.runConfig (M := U.toPhased.toTM) c0 3).state).fst : Nat) = next1
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 3).head : Nat) = (c0.head : Nat) + 1
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 3).tape = c0.tape := by
  rw [show (3 : Nat) = 1 + 1 + 1 from rfl, TM.runConfig_add, TM.runConfig_add,
    TM.runConfig_one, TM.runConfig_one, TM.runConfig_one]
  -- step 1: phase 0 (step right)
  set c1 := TM.stepConfig (M := U.toPhased.toTM) c0 with hc1
  have hij0 : (c0.state.fst : Nat) = base + (⟨0, by simp [stepRightThenBranch]⟩
      : Fin stepRightThenBranch.numPhases).val := by simpa using hphase
  have hph1 : (c1.state.fst : Nat) = base + 1 := by
    rw [hc1, hUP.stepConfig_normal_phase c0 rfl _ hij0 hred0]
    simp [stepRightThenBranch]
  have hhd1 : (c1.head : Nat) = (c0.head : Nat) + 1 := by
    rw [hc1, hUP.stepConfig_normal_head c0 rfl _ hij0 hred0]
    have hm : (stepRightThenBranch.transition ⟨0, by simp [stepRightThenBranch]⟩ ()
        (c0.tape c0.head)).snd.snd.snd = Move.right := by
      simp [stepRightThenBranch]
    rw [hm]
    simp only [Configuration.moveHead, dif_pos hroom]
  have htp1 : c1.tape = c0.tape := by
    rw [hc1, hUP.stepConfig_normal_tape c0 rfl _ hij0 hred0]
    have hb : (stepRightThenBranch.transition ⟨0, by simp [stepRightThenBranch]⟩ ()
        (c0.tape c0.head)).snd.snd.fst = c0.tape c0.head := by
      simp [stepRightThenBranch]
    rw [hb]
    funext q
    by_cases hq : q = c0.head
    · subst hq; simp [Configuration.write]
    · simp [Configuration.write, hq]
  -- step 2: phase 1 (read + branch on 1 → local 2)
  have hbit1 : c1.tape c1.head = true := by
    rw [htp1]; exact hbit c1.head hhd1
  set c2 := TM.stepConfig (M := U.toPhased.toTM) c1 with hc2
  have hij1 : (c1.state.fst : Nat) = base + (⟨1, by simp [stepRightThenBranch]⟩
      : Fin stepRightThenBranch.numPhases).val := by simpa using hph1
  have hph2 : (c2.state.fst : Nat) = base + 2 := by
    rw [hc2, hUP.stepConfig_normal_phase c1 rfl _ hij1 hred1]
    simp [stepRightThenBranch, hbit1]
  have hhd2 : (c2.head : Nat) = (c0.head : Nat) + 1 := by
    rw [hc2, hUP.stepConfig_normal_head c1 rfl _ hij1 hred1]
    have hm : (stepRightThenBranch.transition ⟨1, by simp [stepRightThenBranch]⟩ ()
        (c1.tape c1.head)).snd.snd.snd = Move.stay := by
      simp [stepRightThenBranch, hbit1]
    rw [hm]
    simpa [Configuration.moveHead] using hhd1
  have htp2 : c2.tape = c0.tape := by
    rw [hc2, hUP.stepConfig_normal_tape c1 rfl _ hij1 hred1]
    have hb : (stepRightThenBranch.transition ⟨1, by simp [stepRightThenBranch]⟩ ()
        (c1.tape c1.head)).snd.snd.fst = c1.tape c1.head := by
      simp [stepRightThenBranch, hbit1]
    rw [hb]
    have : c1.write c1.head (c1.tape c1.head) = c1.tape := by
      funext q
      by_cases hq : q = c1.head
      · subst hq; simp [Configuration.write]
      · simp [Configuration.write, hq]
    rw [this, htp1]
  -- step 3: the redirect at local phase 2
  have hij2 : (c2.state.fst : Nat) = base + (2 : Nat) := hph2
  refine ⟨?_, ?_, ?_⟩
  · exact hUP.stepConfig_redirect_phase c2 rfl
      (j := ⟨2, by simp [stepRightThenBranch]⟩) hij2 hred2
  · rw [hUP.stepConfig_redirect_head c2 rfl
      (j := ⟨2, by simp [stepRightThenBranch]⟩) hij2 hred2]
    exact hhd2
  · rw [hUP.stepConfig_redirect_tape c2 rfl
      (j := ⟨2, by simp [stepRightThenBranch]⟩) hij2 hred2]
    exact htp2

/-- **The branch hop on a `0`**: as above with the right neighbour reading `0` and the `0`-verdict
phase `3` redirected to `next0`. -/
theorem run_stepRightBranch_hop_zero
    (hUP : RegionEmbeddedMulti U stepRightThenBranch base redirect) {L : Nat}
    (c0 : Configuration (M := U.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = base)
    (hroom : (c0.head : Nat) + 1 < U.toPhased.toTM.tapeLength L)
    (hred0 : redirect 0 = none) (hred1 : redirect 1 = none)
    {next0 : Nat} (hred3 : redirect 3 = some next0)
    (hbit : ∀ p : Fin (U.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 → c0.tape p = false) :
    (((TM.runConfig (M := U.toPhased.toTM) c0 3).state).fst : Nat) = next0
      ∧ ((TM.runConfig (M := U.toPhased.toTM) c0 3).head : Nat) = (c0.head : Nat) + 1
      ∧ (TM.runConfig (M := U.toPhased.toTM) c0 3).tape = c0.tape := by
  rw [show (3 : Nat) = 1 + 1 + 1 from rfl, TM.runConfig_add, TM.runConfig_add,
    TM.runConfig_one, TM.runConfig_one, TM.runConfig_one]
  set c1 := TM.stepConfig (M := U.toPhased.toTM) c0 with hc1
  have hij0 : (c0.state.fst : Nat) = base + (⟨0, by simp [stepRightThenBranch]⟩
      : Fin stepRightThenBranch.numPhases).val := by simpa using hphase
  have hph1 : (c1.state.fst : Nat) = base + 1 := by
    rw [hc1, hUP.stepConfig_normal_phase c0 rfl _ hij0 hred0]
    simp [stepRightThenBranch]
  have hhd1 : (c1.head : Nat) = (c0.head : Nat) + 1 := by
    rw [hc1, hUP.stepConfig_normal_head c0 rfl _ hij0 hred0]
    have hm : (stepRightThenBranch.transition ⟨0, by simp [stepRightThenBranch]⟩ ()
        (c0.tape c0.head)).snd.snd.snd = Move.right := by
      simp [stepRightThenBranch]
    rw [hm]
    simp only [Configuration.moveHead, dif_pos hroom]
  have htp1 : c1.tape = c0.tape := by
    rw [hc1, hUP.stepConfig_normal_tape c0 rfl _ hij0 hred0]
    have hb : (stepRightThenBranch.transition ⟨0, by simp [stepRightThenBranch]⟩ ()
        (c0.tape c0.head)).snd.snd.fst = c0.tape c0.head := by
      simp [stepRightThenBranch]
    rw [hb]
    funext q
    by_cases hq : q = c0.head
    · subst hq; simp [Configuration.write]
    · simp [Configuration.write, hq]
  have hbit1 : c1.tape c1.head = false := by
    rw [htp1]; exact hbit c1.head hhd1
  set c2 := TM.stepConfig (M := U.toPhased.toTM) c1 with hc2
  have hij1 : (c1.state.fst : Nat) = base + (⟨1, by simp [stepRightThenBranch]⟩
      : Fin stepRightThenBranch.numPhases).val := by simpa using hph1
  have hph2 : (c2.state.fst : Nat) = base + 3 := by
    rw [hc2, hUP.stepConfig_normal_phase c1 rfl _ hij1 hred1]
    simp [stepRightThenBranch, hbit1]
  have hhd2 : (c2.head : Nat) = (c0.head : Nat) + 1 := by
    rw [hc2, hUP.stepConfig_normal_head c1 rfl _ hij1 hred1]
    have hm : (stepRightThenBranch.transition ⟨1, by simp [stepRightThenBranch]⟩ ()
        (c1.tape c1.head)).snd.snd.snd = Move.stay := by
      simp [stepRightThenBranch, hbit1]
    rw [hm]
    simpa [Configuration.moveHead] using hhd1
  have htp2 : c2.tape = c0.tape := by
    rw [hc2, hUP.stepConfig_normal_tape c1 rfl _ hij1 hred1]
    have hb : (stepRightThenBranch.transition ⟨1, by simp [stepRightThenBranch]⟩ ()
        (c1.tape c1.head)).snd.snd.fst = c1.tape c1.head := by
      simp [stepRightThenBranch, hbit1]
    rw [hb]
    have : c1.write c1.head (c1.tape c1.head) = c1.tape := by
      funext q
      by_cases hq : q = c1.head
      · subst hq; simp [Configuration.write]
      · simp [Configuration.write, hq]
    rw [this, htp1]
  have hij2 : (c2.state.fst : Nat) = base + (3 : Nat) := hph2
  refine ⟨?_, ?_, ?_⟩
  · exact hUP.stepConfig_redirect_phase c2 rfl
      (j := ⟨3, by simp [stepRightThenBranch]⟩) hij2 hred3
  · rw [hUP.stepConfig_redirect_head c2 rfl
      (j := ⟨3, by simp [stepRightThenBranch]⟩) hij2 hred3]
    exact hhd2
  · rw [hUP.stepConfig_redirect_tape c2 rfl
      (j := ⟨3, by simp [stepRightThenBranch]⟩) hij2 hred3]
    exact htp2

end RegionEmbeddedMulti

end ContractExpansion
end Frontier
end Pnp4
