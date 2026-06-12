import Pnp4.Frontier.ContractExpansion.TreeMCSPZoneWalkRight

/-!
# `zoneWalkRight` run segments — D2t-5b (Block A4w): the rightward per-block steps

The mirror of the leftward segments (`TreeMCSPZoneWalkRun`): the φ3 ones-scan invariant, the
single-block pass (from φ2 on a block's first `1`, `k + 2` steps to φ2 on the cell past its trailing
`0`), the 2-step entry (off the sentinel onto the decide cell), and the 1-step exit (φ2 on a dead `0`
is done).  The full rightward traversal (induction over the bottom-first block list) builds on these.

**Progress classification (AGENTS.md): Infrastructure** — verifier machine run-throughs; build no
verifier and prove no separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.
**No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- Rightward ones-scan invariant: from φ3 with the `j` cells `[head, head + j)` all `1`
(`head + j` within the tape), after `j` steps φ3 has advanced `j` cells, tape unchanged. -/
theorem zoneWalkRight_runConfig_p3_scanning {L : Nat}
    (c0 : Configuration (M := zoneWalkRight.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 3) :
    ∀ j : Nat, (c0.head : Nat) + j < zoneWalkRight.toPhased.toTM.tapeLength L →
      (∀ p : Fin (zoneWalkRight.toPhased.toTM.tapeLength L),
        (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + j → c0.tape p = true) →
      (((TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0 j).state).fst : Nat) = 3
      ∧ ((TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0 j).head : Nat) = (c0.head : Nat) + j
      ∧ (TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0 j).tape = c0.tape := by
  intro j
  induction j with
  | zero => intro _ _; exact ⟨hphase, by simp, rfl⟩
  | succ j ih =>
      intro hj h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h1 p hp1 (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0 j with hc
      have hbit : c.tape c.head = true := by
        rw [htp]; exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      have hstate : c.state = ⟨c.state.fst, c.state.snd⟩ := rfl
      have hlt : (c.head : Nat) + 1 < zoneWalkRight.toPhased.toTM.tapeLength L := by
        rw [hhd]; omega
      refine ⟨?_, ?_, ?_⟩
      · exact zoneWalkRight_stepConfig_p3_one_phase c hph hstate hbit
      · rw [zoneWalkRight_stepConfig_p3_one_head c hph hstate hbit]
        simp only [Configuration.moveHead, dif_pos hlt]
        omega
      · rw [zoneWalkRight_stepConfig_p3_one_tape c hph hstate hbit, htp]

/-- **One rightward block pass.**  From φ2 on a block's first `1` (`k ≥ 1` ones at `[head, head+k)`,
a `0` at `head + k`, and `head + k + 1` on the tape), after `k + 2` steps the walker is back at φ2 on
`head + k + 1` (the cell past the block's trailing `0`), tape unchanged. -/
theorem zoneWalkRight_runConfig_block_segment {L : Nat}
    (c0 : Configuration (M := zoneWalkRight.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 2) (k : Nat) (hk : 1 ≤ k)
    (hroom : (c0.head : Nat) + k + 1 < zoneWalkRight.toPhased.toTM.tapeLength L)
    (hones : ∀ p : Fin (zoneWalkRight.toPhased.toTM.tapeLength L),
      (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + k → c0.tape p = true)
    (hdelim : ∀ p : Fin (zoneWalkRight.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + k → c0.tape p = false) :
    (((TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0 (k + 2)).state).fst : Nat) = 2
    ∧ ((TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0 (k + 2)).head : Nat)
        = (c0.head : Nat) + k + 1
    ∧ (TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0 (k + 2)).tape = c0.tape
    ∧ ∀ s : Nat, s < k + 2 →
        (((TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0 s).state).fst : Nat) < 4
        ∧ ((TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0 s).head : Nat)
            ≤ (c0.head : Nat) + k := by
  -- Split k + 2 = 1 + (k + 1): the φ2-decide step, the φ3 ones-scan, the φ3 0-step.
  rw [show k + 2 = 1 + (k + 1) from by omega, TM.runConfig_add, TM.runConfig_one]
  set c1 := TM.stepConfig (M := zoneWalkRight.toPhased.toTM) c0 with hc1
  have hst0 : c0.state = ⟨c0.state.fst, c0.state.snd⟩ := rfl
  have hbit0 : c0.tape c0.head = true := hones c0.head (by omega) (by omega)
  have h1ph : (c1.state.fst : Nat) = 3 := zoneWalkRight_stepConfig_p2_one_phase c0 hphase hst0 hbit0
  have h1hd : (c1.head : Nat) = (c0.head : Nat) := by
    rw [hc1, zoneWalkRight_stepConfig_p2_one_head c0 hphase hst0 hbit0]
  have h1tp : c1.tape = c0.tape := by
    rw [hc1, zoneWalkRight_stepConfig_p2_tape c0 hphase hst0]
  -- φ3 scans the k ones.
  rw [show k + 1 = k + 1 from rfl, TM.runConfig_add]
  obtain ⟨h2ph, h2hd, h2tp⟩ :=
    zoneWalkRight_runConfig_p3_scanning c1 h1ph k (by omega)
      (fun p hp1 hp2 => by
        rw [h1hd] at hp1 hp2
        rw [h1tp]
        exact hones p hp1 hp2)
  set c2 := TM.runConfig (M := zoneWalkRight.toPhased.toTM) c1 k with hc2
  rw [h1hd] at h2hd
  -- φ3 reads the trailing 0 and steps right into φ2.
  rw [TM.runConfig_one]
  have hst2 : c2.state = ⟨c2.state.fst, c2.state.snd⟩ := rfl
  have hbit2 : c2.tape c2.head = false := by
    rw [h2tp, h1tp]
    exact hdelim c2.head (by rw [h2hd])
  have hlt2 : (c2.head : Nat) + 1 < zoneWalkRight.toPhased.toTM.tapeLength L := by
    rw [h2hd]; omega
  have hcfg1 : TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0 1 = c1 := by
    rw [TM.runConfig_one, ← hc1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact zoneWalkRight_stepConfig_p3_zero_phase c2 h2ph hst2 hbit2
  · rw [zoneWalkRight_stepConfig_p3_zero_head c2 h2ph hst2 hbit2]
    simp only [Configuration.moveHead, dif_pos hlt2]
    omega
  · rw [zoneWalkRight_stepConfig_p3_zero_tape c2 h2ph hst2 hbit2, h2tp, h1tp]
  · intro s hs
    by_cases hs0 : s = 0
    · subst hs0
      rw [TM.runConfig_zero]
      exact ⟨by omega, by omega⟩
    · -- inside the φ3 ones-scan, r := s − 1 ≤ k
      obtain ⟨hrp, hrh, _⟩ :=
        zoneWalkRight_runConfig_p3_scanning c1 h1ph (s - 1)
          (by rw [h1hd]; omega)
          (fun p hp1 hp2 => by
            rw [h1hd] at hp1 hp2
            rw [h1tp]
            exact hones p hp1 (by omega))
      rw [show s = 1 + (s - 1) from by omega, TM.runConfig_add, hcfg1]
      rw [h1hd] at hrh
      exact ⟨by omega, by omega⟩

/-- **Entry.**  From φ0 on the base sentinel, with the `0` at `head + 1` (and room), after `2` steps
the walker is at φ2 on `head + 2`, tape unchanged. -/
theorem zoneWalkRight_runConfig_entry {L : Nat}
    (c0 : Configuration (M := zoneWalkRight.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 0)
    (hroom : (c0.head : Nat) + 2 < zoneWalkRight.toPhased.toTM.tapeLength L)
    (hzero : ∀ p : Fin (zoneWalkRight.toPhased.toTM.tapeLength L),
      (p : Nat) = (c0.head : Nat) + 1 → c0.tape p = false) :
    (((TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0 2).state).fst : Nat) = 2
    ∧ ((TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0 2).head : Nat) = (c0.head : Nat) + 2
    ∧ (TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0 2).tape = c0.tape
    ∧ ∀ s : Nat, s < 2 →
        (((TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0 s).state).fst : Nat) < 4
        ∧ ((TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0 s).head : Nat)
            ≤ (c0.head : Nat) + 1 := by
  rw [show (2 : Nat) = 1 + 1 from rfl, TM.runConfig_add, TM.runConfig_one, TM.runConfig_one]
  set c1 := TM.stepConfig (M := zoneWalkRight.toPhased.toTM) c0 with hc1
  have hst0 : c0.state = ⟨c0.state.fst, c0.state.snd⟩ := rfl
  have h1ph : (c1.state.fst : Nat) = 1 := zoneWalkRight_stepConfig_p0_phase c0 hphase hst0
  have h1hd : (c1.head : Nat) = (c0.head : Nat) + 1 := by
    rw [hc1, zoneWalkRight_stepConfig_p0_head c0 hphase hst0]
    simp only [Configuration.moveHead,
      dif_pos (by omega : (c0.head : Nat) + 1 < zoneWalkRight.toPhased.toTM.tapeLength L)]
  have h1tp : c1.tape = c0.tape := by
    rw [hc1, zoneWalkRight_stepConfig_p0_tape c0 hphase hst0]
  have hst1 : c1.state = ⟨c1.state.fst, c1.state.snd⟩ := rfl
  have hbit1 : c1.tape c1.head = false := by
    rw [h1tp]; exact hzero c1.head (by rw [h1hd])
  have hlt1 : (c1.head : Nat) + 1 < zoneWalkRight.toPhased.toTM.tapeLength L := by
    rw [h1hd]; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact zoneWalkRight_stepConfig_p1_zero_phase c1 h1ph hst1 hbit1
  · rw [zoneWalkRight_stepConfig_p1_zero_head c1 h1ph hst1 hbit1]
    simp only [Configuration.moveHead, dif_pos hlt1]
    omega
  · rw [zoneWalkRight_stepConfig_p1_zero_tape c1 h1ph hst1 hbit1, h1tp]
  · intro s hs
    by_cases hs0 : s = 0
    · subst hs0
      rw [TM.runConfig_zero]
      exact ⟨by omega, by omega⟩
    · have hs1 : s = 1 := by omega
      subst hs1
      rw [TM.runConfig_one, ← hc1]
      exact ⟨by omega, by omega⟩

/-- **Exit.**  From φ2 on a dead `0`, one step finishes: φ4, head unchanged, tape unchanged. -/
theorem zoneWalkRight_runConfig_exit {L : Nat}
    (c0 : Configuration (M := zoneWalkRight.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = 2)
    (hzero : c0.tape c0.head = false) :
    (((TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0 1).state).fst : Nat) = 4
    ∧ ((TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0 1).head : Nat) = (c0.head : Nat)
    ∧ (TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0 1).tape = c0.tape
    ∧ ∀ s : Nat, s < 1 →
        (((TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0 s).state).fst : Nat) < 4
        ∧ ((TM.runConfig (M := zoneWalkRight.toPhased.toTM) c0 s).head : Nat)
            ≤ (c0.head : Nat) := by
  rw [TM.runConfig_one]
  have hst0 : c0.state = ⟨c0.state.fst, c0.state.snd⟩ := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact zoneWalkRight_stepConfig_p2_zero_phase c0 hphase hst0 hzero
  · rw [zoneWalkRight_stepConfig_p2_zero_head c0 hphase hst0 hzero]
  · rw [zoneWalkRight_stepConfig_p2_tape c0 hphase hst0]
  · intro s hs
    have hs0 : s = 0 := by omega
    subst hs0
    rw [TM.runConfig_zero]
    exact ⟨by omega, by omega⟩

end ContractExpansion
end Frontier
end Pnp4
