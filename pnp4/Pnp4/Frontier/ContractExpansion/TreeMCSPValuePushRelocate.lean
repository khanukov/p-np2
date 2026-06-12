import Pnp4.Frontier.ContractExpansion.TreeMCSPValuePushPass

/-!
# `valuePushProgram` — D2t-6b (M1 / A5m-V, run IV): the relocate loop

After the drain, the rebuilt block sits at `[shwBase + 3, shwBase + k + 3)` — shifted **two cells
right** of the shadow source's home.  The relocate loop (phases `52–67`) moves it back unit by unit,
restoring `SHW = [1]·1^k` in place: each pass tests the cell two right of the destination frontier,
erases it, and rewrites it at the frontier.

* `RelocateLayout` — the loop invariant (phase `52`, head `shwBase + 1 + j`, `j` units already
  relocated into `[shwBase + 1, shwBase + 1 + j)`, the remaining rebuilt block at
  `[shwBase + 3 + j, shwBase + k + 3)`, a two-cell working gap between);
* `valuePush_relocate_step` — one relocate pass (`j < k`): `RelocateLayout j → RelocateLayout (j+1)`,
  tape changed in exactly two cells (the erased `shwBase + 3 + j` and the written `shwBase + 1 + j`);
* `valuePush_relocate` — the induction to `j = k` (the restored shadow source).

Everything outside `[shwBase + 1, shwBase + k + 3)` — in particular the value entry being built — is
untouched.

**Progress classification (AGENTS.md): Infrastructure** — machine-component run lemmas; proves no
separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP`
claim.** -/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **The relocate loop invariant** (phase `52`, `j` of `k` units relocated). -/
structure RelocateLayout {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (shwBase k j : Nat) : Prop where
  hphase : (c.state.fst : Nat) = 52
  hhead : (c.head : Nat) = shwBase + 1 + j
  hjk : j ≤ k
  hbase : 1 ≤ shwBase
  hL : shwBase + k + 4 ≤ valuePushProgram.toPhased.toTM.tapeLength L
  hanchor : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    (p : Nat) = shwBase → c.tape p = true
  hnew : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    shwBase + 1 ≤ (p : Nat) → (p : Nat) < shwBase + 1 + j → c.tape p = true
  hwork : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    shwBase + 1 + j ≤ (p : Nat) → (p : Nat) < shwBase + 3 + j → c.tape p = false
  hrem : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    shwBase + 3 + j ≤ (p : Nat) → (p : Nat) < shwBase + k + 3 → c.tape p = true
  hterm : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    (p : Nat) = shwBase + k + 3 → c.tape p = false

set_option maxHeartbeats 1200000 in
/-- **One relocate pass** (`j < k`): in `T ≤ 15` steps, `RelocateLayout (j + 1)`, with the tape
changed in exactly the two cells `shwBase + 3 + j` (erased) and `shwBase + 1 + j` (written). -/
theorem valuePush_relocate_step {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (shwBase k j : Nat) (hlay : RelocateLayout c shwBase k j) (hjk : j < k) :
    ∃ T : Nat, T ≤ 15
      ∧ RelocateLayout (TM.runConfig (M := valuePushProgram.toPhased.toTM) c T) shwBase k (j + 1)
      ∧ ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
          (p : Nat) ≠ shwBase + 3 + j → (p : Nat) ≠ shwBase + 1 + j →
          (TM.runConfig (M := valuePushProgram.toPhased.toTM) c T).tape p = c.tape p := by
  obtain ⟨hphase, hhead, hjk', hbase, hL, hanchor, hnew, hwork, hrem, hterm⟩ := hlay
  -- L1: step right.
  obtain ⟨p1, h1, t1⟩ := valuePush_region_relocStepRight.run_stepRight_hop c hphase (by omega)
  rw [hhead] at h1
  set c1 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c 2 with hc1
  have h1' : (c1.head : Nat) = shwBase + 2 + j := by rw [h1]; omega
  -- L2: branch on the cell two right of the destination frontier (a rebuilt 1 since j < k).
  obtain ⟨p2, h2, t2⟩ := valuePush_region_relocBranch.run_stepRightBranch_hop_one c1 p1 (by omega)
    (by rfl) (by rfl) (by rfl)
    (fun p hp => by rw [t1]; exact hrem p (by omega) (by omega))
  rw [h1'] at h2
  set c2 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c1 3 with hc2
  have h2' : (c2.head : Nat) = shwBase + 3 + j := by rw [h2]; omega
  have htc2 : c2.tape = c.tape := by rw [t2, t1]
  -- L3: erase the rebuilt unit.
  obtain ⟨p3, h3, t3⟩ := valuePush_region_relocErase.run_writeBits_hop c2 p2
    (by simp only [List.length_singleton]; omega)
  simp only [List.length_singleton] at p3 h3 t3
  set c3 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c2 2 with hc3
  have h3' : (c3.head : Nat) = shwBase + 4 + j := by rw [h3, h2']; omega
  have htc3 : c3.tape = writeBlockTape c.tape (shwBase + 3 + j) [false] := by rw [t3, htc2, h2']
  -- L4–L6: three left steps to the destination frontier.
  obtain ⟨p4, h4, t4⟩ := valuePush_region_relocLeft1.run_stepLeft_hop c3 p3 (by omega)
  set c4 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c3 2 with hc4
  have h4' : (c4.head : Nat) = shwBase + 3 + j := by rw [h4, h3']; omega
  obtain ⟨p5, h5, t5⟩ := valuePush_region_relocLeft2.run_stepLeft_hop c4 p4 (by omega)
  set c5 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c4 2 with hc5
  have h5' : (c5.head : Nat) = shwBase + 2 + j := by rw [h5, h4']; omega
  obtain ⟨p6, h6, t6⟩ := valuePush_region_relocLeft3.run_stepLeft_hop c5 p5 (by omega)
  set c6 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c5 2 with hc6
  have h6' : (c6.head : Nat) = shwBase + 1 + j := by rw [h6, h5']; omega
  have htc6 : c6.tape = writeBlockTape c.tape (shwBase + 3 + j) [false] := by
    rw [t6, t5, t4, htc3]
  -- L7: write the relocated unit at the frontier (back-edge to 52).
  obtain ⟨p7, h7, t7⟩ := valuePush_region_relocWrite.run_writeBits_hop c6 p6
    (by simp only [List.length_singleton]; omega)
  simp only [List.length_singleton] at p7 h7 t7
  set c7 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c6 2 with hc7
  have h7' : (c7.head : Nat) = shwBase + 2 + j := by rw [h7, h6']; omega
  have htc7 : c7.tape = writeBlockTape (writeBlockTape c.tape (shwBase + 3 + j) [false])
      (shwBase + 1 + j) [true] := by rw [t7, htc6, h6']
  have hrun : TM.runConfig (M := valuePushProgram.toPhased.toTM) c
      (2 + (3 + (2 + (2 + (2 + (2 + 2)))))) = c7 := by
    rw [TM.runConfig_add, ← hc1]
    rw [TM.runConfig_add, ← hc2]
    rw [TM.runConfig_add, ← hc3]
    rw [TM.runConfig_add, ← hc4]
    rw [TM.runConfig_add, ← hc5]
    rw [TM.runConfig_add, ← hc6]
  have hcell : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      (p : Nat) ≠ shwBase + 3 + j → (p : Nat) ≠ shwBase + 1 + j → c7.tape p = c.tape p := by
    intro p hne1 hne2
    rw [htc7, writeBlockTape_singleton_ne _ _ _ _ hne2, writeBlockTape_singleton_ne _ _ _ _ hne1]
  have herase : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = shwBase + 3 + j → c7.tape p = false := by
    intro p hp
    rw [htc7, writeBlockTape_singleton_ne _ _ _ _ (by omega), writeBlockTape_singleton_eq _ _ _ _ hp]
  have hwrite : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = shwBase + 1 + j → c7.tape p = true := by
    intro p hp
    rw [htc7, writeBlockTape_singleton_eq _ _ _ _ hp]
  refine ⟨2 + (3 + (2 + (2 + (2 + (2 + 2))))), by omega, ?_, ?_⟩
  · rw [hrun]
    refine ⟨p7, by rw [h7']; omega, by omega, hbase, hL, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp; rw [hcell p (by omega) (by omega)]; exact hanchor p hp
    · intro p hp1 hp2
      by_cases hp : (p : Nat) = shwBase + 1 + j
      · exact hwrite p hp
      · rw [hcell p (by omega) hp]; exact hnew p hp1 (by omega)
    · intro p hp1 hp2
      by_cases hp : (p : Nat) = shwBase + 3 + j
      · exact herase p hp
      · rw [hcell p hp (by omega)]; exact hwork p (by omega) (by omega)
    · intro p hp1 hp2; rw [hcell p (by omega) (by omega)]; exact hrem p (by omega) hp2
    · intro p hp; rw [hcell p (by omega) (by omega)]; exact hterm p hp
  · rw [hrun]; exact hcell

set_option maxHeartbeats 800000 in
/-- **The relocate loop.**  From `RelocateLayout j`, the restored state `RelocateLayout k` (shadow
source `[shwBase + 1, shwBase + k + 1)` rebuilt in place) is reached in `≤ (k − j) · 13` steps, with
everything outside `[shwBase + 1, shwBase + k + 3)` untouched. -/
theorem valuePush_relocate {L : Nat}
    (c0 : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (shwBase k j : Nat) (hlay : RelocateLayout c0 shwBase k j) :
    ∃ T : Nat, T ≤ (k - j) * 15
      ∧ RelocateLayout (TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 T) shwBase k k
      ∧ ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
          ((p : Nat) < shwBase + 1 ∨ shwBase + k + 3 ≤ (p : Nat)) →
          (TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 T).tape p = c0.tape p := by
  suffices H : ∀ n (c : Configuration (M := valuePushProgram.toPhased.toTM) L) (j : Nat),
      RelocateLayout c shwBase k j → k - j = n →
      ∃ T : Nat, T ≤ n * 15
        ∧ RelocateLayout (TM.runConfig (M := valuePushProgram.toPhased.toTM) c T) shwBase k k
        ∧ ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
            ((p : Nat) < shwBase + 1 ∨ shwBase + k + 3 ≤ (p : Nat)) →
            (TM.runConfig (M := valuePushProgram.toPhased.toTM) c T).tape p = c.tape p by
    exact H (k - j) c0 j hlay rfl
  intro n
  induction n with
  | zero =>
      intro c j hlay hn
      have hjk : j = k := by have := hlay.hjk; omega
      subst hjk
      exact ⟨0, by simp, by simpa using hlay, fun p _ => rfl⟩
  | succ n ih =>
      intro c j hlay hn
      have hjk : j < k := by omega
      have hbase := hlay.hbase
      obtain ⟨T1, hT1, hlay1, hunt1⟩ := valuePush_relocate_step c shwBase k j hlay hjk
      obtain ⟨T2, hT2, hlay2, hunt2⟩ :=
        ih (TM.runConfig (M := valuePushProgram.toPhased.toTM) c T1) (j + 1) hlay1 (by omega)
      have hmul : (n + 1) * 15 = n * 15 + 15 := by ring
      refine ⟨T1 + T2, by rw [hmul]; omega, ?_, ?_⟩
      · rw [TM.runConfig_add]; exact hlay2
      · intro p hp
        rw [TM.runConfig_add]
        exact (hunt2 p hp).trans (hunt1 p (by omega) (by omega))

end ContractExpansion
end Frontier
end Pnp4
