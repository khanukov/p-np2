import Pnp4.Frontier.ContractExpansion.TreeMCSPZoneWalk

/-!
# `zoneWalkLeft` run segments — D2t-5b (Block A4w): the per-block walk steps

`TreeMCSPZoneWalk` proved the inner field sub-scan (φ2).  This module assembles the two **segment**
walk-throughs that the full-zone walk (next brick) stitches by induction:

* `zoneWalkLeft_runConfig_field_segment` — one **field block** pass.  From φ0 on a block's rightmost
  cell, with `m ≥ 1` ones at `[head − m, head − 1]` and the delimiter `0` at `head − m − 1`, after
  `m + 4` steps the walker is back at φ0 on the **next** block's rightmost cell (`head − m − 2`), tape
  unchanged.  (φ0 step-left, φ1 decide-field, φ2 scan the `m` ones, φ2 stop on the delimiter, φ3 cross.)
* `zoneWalkLeft_runConfig_sentinel` — the **terminating** pass.  From φ0 on the single-`1` base
  sentinel, with a `0` (dead zone) at `head − 1`, after `2` steps the walker is **done** (φ4) on that
  `0`, tape unchanged.

Both are pinned by the `stepConfig` layer + the φ2 scanning lemma, composed through `TM.runConfig_add`.

**Progress classification (AGENTS.md): Infrastructure** — verifier machine run-throughs; build no
verifier and prove no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.
**No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **The terminating pass.**  From φ0 on the single-`1` base sentinel (`head > 0`, with a `0` at
`head − 1`), after `2` steps the walker is in the done phase `4` with the head on that `0`
(`head − 1`), tape unchanged — and along the way the phase stays below the done phase and the head
at or below the start (the per-step stream the region-embedding transfer consumes). -/
theorem zoneWalkLeft_runConfig_sentinel {L : Nat}
    (c0 : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) (hh : 0 < (c0.head : Nat))
    (hdead : ∀ p : Fin (zoneWalkLeft.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - 1 → c0.tape p = false) :
    (((TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c0 2).state).fst : Nat) = 4
    ∧ ((TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c0 2).head : Nat) = (c0.head : Nat) - 1
    ∧ (TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c0 2).tape = c0.tape
    ∧ ∀ s : Nat, s < 2 →
        (((TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c0 s).state).fst : Nat) < 4
        ∧ ((TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c0 s).head : Nat)
            ≤ (c0.head : Nat) := by
  rw [show (2 : Nat) = 1 + 1 from rfl, TM.runConfig_add, TM.runConfig_one, TM.runConfig_one]
  set c1 := TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c0 with hc1
  have hst0 : c0.state = ⟨c0.state.fst, c0.state.snd⟩ := rfl
  -- c1 = after φ0: phase 1, head head-1, tape unchanged.
  have h1ph : (c1.state.fst : Nat) = 1 := zoneWalkLeft_stepConfig_p0_phase c0 hphase hst0
  have h1hd : (c1.head : Nat) = (c0.head : Nat) - 1 := by
    rw [hc1, zoneWalkLeft_stepConfig_p0_head c0 hphase hst0]
    simp only [Configuration.moveHead, dif_neg (by omega : ¬ (c0.head : Nat) = 0)]
  have h1tp : c1.tape = c0.tape := zoneWalkLeft_stepConfig_p0_tape c0 hphase hst0
  -- c2 = after φ1 reading 0: phase 4, head unchanged, tape unchanged.
  have hst1 : c1.state = ⟨c1.state.fst, c1.state.snd⟩ := rfl
  have hbit : c1.tape c1.head = false := by
    rw [h1tp]; exact hdead c1.head (by rw [h1hd])
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact zoneWalkLeft_stepConfig_p1_zero_phase c1 h1ph hst1 hbit
  · rw [zoneWalkLeft_stepConfig_p1_zero_head c1 h1ph hst1 hbit, h1hd]
  · rw [zoneWalkLeft_stepConfig_p1_tape c1 h1ph hst1, h1tp]
  · intro s hs
    by_cases hs0 : s = 0
    · subst hs0
      rw [TM.runConfig_zero]
      exact ⟨by omega, by omega⟩
    · have hs1 : s = 1 := by omega
      subst hs1
      rw [TM.runConfig_one, ← hc1]
      exact ⟨by omega, by omega⟩

/-- **One field-block pass.**  From φ0 on a field block's rightmost cell (`head`), with `m ≥ 1` ones at
`[head − m, head − 1]` and the delimiter `0` at `head − m − 1` (and `head ≥ m + 2` so no move clamps),
after `m + 4` steps the walker is back at φ0 on the next block's rightmost cell (`head − m − 2`), tape
unchanged. -/
theorem zoneWalkLeft_runConfig_field_segment {L : Nat}
    (c0 : Configuration (M := zoneWalkLeft.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0) (m : Nat) (hm : 1 ≤ m)
    (hh : m + 2 ≤ (c0.head : Nat))
    (hones : ∀ p : Fin (zoneWalkLeft.toPhased.toTM.tapeLength L),
      (c0.head : Nat) - m ≤ (p : Nat) → (p : Nat) ≤ (c0.head : Nat) - 1 → c0.tape p = true)
    (hdelim : ∀ p : Fin (zoneWalkLeft.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) - m - 1 → c0.tape p = false) :
    (((TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c0 (m + 4)).state).fst : Nat) = 0
    ∧ ((TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c0 (m + 4)).head : Nat)
        = (c0.head : Nat) - m - 2
    ∧ (TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c0 (m + 4)).tape = c0.tape
    ∧ ∀ s : Nat, s < m + 4 →
        (((TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c0 s).state).fst : Nat) < 4
        ∧ ((TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c0 s).head : Nat)
            ≤ (c0.head : Nat) := by
  -- Split m + 4 = 2 + (m + 2): the (φ0,φ1) entry, the φ2 scan of m ones, the (φ2-stop, φ3) exit.
  have hsplit : m + 4 = 2 + (m + 2) := by omega
  rw [hsplit, TM.runConfig_add]
  -- c2 := after φ0, φ1: phase 2, head head-1, tape unchanged.
  set c2 := TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c0 2 with hc2
  have hst0 : c0.state = ⟨c0.state.fst, c0.state.snd⟩ := rfl
  have hc2eq : c2 = TM.stepConfig (M := zoneWalkLeft.toPhased.toTM)
      (TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c0) := by
    rw [hc2, show (2 : Nat) = 1 + 1 from rfl, TM.runConfig_add, TM.runConfig_one, TM.runConfig_one]
  set c1 := TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c0 with hc1
  have h1ph : (c1.state.fst : Nat) = 1 := zoneWalkLeft_stepConfig_p0_phase c0 hphase hst0
  have h1hd : (c1.head : Nat) = (c0.head : Nat) - 1 := by
    rw [hc1, zoneWalkLeft_stepConfig_p0_head c0 hphase hst0]
    simp only [Configuration.moveHead, dif_neg (by omega : ¬ (c0.head : Nat) = 0)]
  have h1tp : c1.tape = c0.tape := zoneWalkLeft_stepConfig_p0_tape c0 hphase hst0
  have hst1 : c1.state = ⟨c1.state.fst, c1.state.snd⟩ := rfl
  have hbit1 : c1.tape c1.head = true := by
    rw [h1tp]; exact hones c1.head (by rw [h1hd]; omega) (by rw [h1hd])
  have h2ph : (c2.state.fst : Nat) = 2 := by
    rw [hc2eq]; exact zoneWalkLeft_stepConfig_p1_one_phase c1 h1ph hst1 hbit1
  have h2hd : (c2.head : Nat) = (c0.head : Nat) - 1 := by
    rw [hc2eq, zoneWalkLeft_stepConfig_p1_one_head c1 h1ph hst1 hbit1, h1hd]
  have h2tp : c2.tape = c0.tape := by
    rw [hc2eq, zoneWalkLeft_stepConfig_p1_tape c1 h1ph hst1, h1tp]
  -- Scan the m ones: c3 := runConfig c2 m: phase 2, head head-1-m, tape unchanged.
  rw [TM.runConfig_add]
  obtain ⟨h3ph, h3hd, h3tp⟩ :=
    zoneWalkLeft_runConfig_p2_scanning c2 h2ph m (by rw [h2hd]; omega)
      (fun p hp1 hp2 => by
        rw [h2hd] at hp1 hp2
        rw [h2tp]
        exact hones p (by omega) (by omega))
  set c3 := TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c2 m with hc3
  rw [h2hd] at h3hd
  -- c3.head = head - 1 - m = head - m - 1 (the delimiter).
  have h3hd' : (c3.head : Nat) = (c0.head : Nat) - m - 1 := by omega
  -- Exit: 2 more steps (φ2 reads delimiter 0 → φ3; φ3 steps left → φ0).
  rw [show (2 : Nat) = 1 + 1 from rfl, TM.runConfig_add, TM.runConfig_one, TM.runConfig_one]
  set c4 := TM.stepConfig (M := zoneWalkLeft.toPhased.toTM) c3 with hc4
  have hst3 : c3.state = ⟨c3.state.fst, c3.state.snd⟩ := rfl
  have hbit3 : c3.tape c3.head = false := by
    rw [h3tp, h2tp]; exact hdelim c3.head (by rw [h3hd'])
  have h4ph : (c4.state.fst : Nat) = 3 := zoneWalkLeft_stepConfig_p2_zero_phase c3 h3ph hst3 hbit3
  have h4hd : (c4.head : Nat) = (c0.head : Nat) - m - 1 := by
    rw [hc4, zoneWalkLeft_stepConfig_p2_zero_head c3 h3ph hst3 hbit3, h3hd']
  have h4tp : c4.tape = c0.tape := by
    rw [hc4, zoneWalkLeft_stepConfig_p2_zero_tape c3 h3ph hst3 hbit3, h3tp, h2tp]
  have hst4 : c4.state = ⟨c4.state.fst, c4.state.snd⟩ := rfl
  -- The truncated chains for the per-step stream.
  have hcfg1 : TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c0 1 = c1 := by
    rw [TM.runConfig_one, ← hc1]
  have hcfg2 : TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c0 2 = c2 := hc2.symm
  have hcfg3 : TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c0 (2 + m) = c3 := by
    rw [TM.runConfig_add, hcfg2, ← hc3]
  have hcfg4 : TM.runConfig (M := zoneWalkLeft.toPhased.toTM) c0 (2 + m + 1) = c4 := by
    rw [TM.runConfig_succ, hcfg3, ← hc4]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact zoneWalkLeft_stepConfig_p3_phase c4 h4ph hst4
  · rw [zoneWalkLeft_stepConfig_p3_head c4 h4ph hst4]
    simp only [Configuration.moveHead, dif_neg (by rw [h4hd]; omega : ¬ (c4.head : Nat) = 0)]
    rw [h4hd]; omega
  · rw [zoneWalkLeft_stepConfig_p3_tape c4 h4ph hst4, h4tp]
  · intro s hs
    by_cases hs0 : s = 0
    · subst hs0
      rw [TM.runConfig_zero]
      exact ⟨by omega, by omega⟩
    by_cases hs1 : s = 1
    · subst hs1
      rw [hcfg1]
      exact ⟨by omega, by omega⟩
    by_cases hsm : s < 2 + m
    · -- inside the φ2 ones-scan, r := s − 2
      obtain ⟨hrp, hrh, _⟩ :=
        zoneWalkLeft_runConfig_p2_scanning c2 h2ph (s - 2) (by rw [h2hd]; omega)
          (fun p hp1 hp2 => by
            rw [h2hd] at hp1 hp2
            rw [h2tp]
            exact hones p (by omega) (by omega))
      rw [show s = 2 + (s - 2) from by omega, TM.runConfig_add, hcfg2]
      rw [h2hd] at hrh
      exact ⟨by omega, by omega⟩
    by_cases hsm2 : s = 2 + m
    · subst hsm2
      rw [hcfg3]
      exact ⟨by omega, by omega⟩
    · have hsm3 : s = 2 + m + 1 := by omega
      subst hsm3
      rw [hcfg4]
      exact ⟨by omega, by omega⟩

end ContractExpansion
end Frontier
end Pnp4
