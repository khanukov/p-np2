import Pnp4.Frontier.ContractExpansion.TreeMCSPValuePushProgram

/-!
# `valuePushProgram` — D2t-6b (M1 / A5m-V, run I): the fan-out pass

The loop invariant `ValuePushLayout` (home anchor, phase `12`, after `i` of `k` passes) and one
fan-out pass.  The pass is proved in two halves under their own heartbeat budgets — the broken-
`remWalk` lesson applies, so the machine is validated by this run lemma, not assumed:

* `valuePush_passVal` (legs L1–L7): branch on the source, walk to the value frontier, append one
  value unit, return to the home anchor (phase `28`); tape gains one `1` at `vend + 3 + i`;
* `valuePush_passSrc` (legs L8–L16): step onto the source, erase its rightmost unit, re-deposit it
  two cells right, walk back to the home anchor and back-edge to phase `12`; tape gains a `0` at
  `shwBase + (k − i)` and a `1` at `shwBase + (k − i) + 2`;
* `valuePush_pass`: composes the two, reaching the layout at `i + 1`, tape changed in exactly the
  three cells.

The geometry is the module docstring of `TreeMCSPValuePushProgram`; every leg is one region hop.

**Progress classification (AGENTS.md): Infrastructure** — machine-component run lemmas; proves no
separation.  Standard `[propext, Classical.choice, Quot.sound]` triple only.  **No `P ≠ NP`
claim.** -/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- A singleton block write read at its own cell. -/
theorem writeBlockTape_singleton_eq {L : Nat} (tape : Fin L → Bool) (pos : Nat) (b : Bool)
    (q : Fin L) (h : (q : Nat) = pos) :
    writeBlockTape tape pos [b] q = b := by
  unfold writeBlockTape
  rw [if_pos (by simp [h])]
  simp [h]

/-- A singleton block write read anywhere else. -/
theorem writeBlockTape_singleton_ne {L : Nat} (tape : Fin L → Bool) (pos : Nat) (b : Bool)
    (q : Fin L) (h : (q : Nat) ≠ pos) :
    writeBlockTape tape pos [b] q = tape q := by
  unfold writeBlockTape
  rw [if_neg (by simp; omega)]

/-- **The fan-out loop invariant** (home anchor, phase `12`, `i` of `k` passes done).  `vend` is
the value stack's content end (its guaranteed rightmost `1`); the entry under construction carries
`i + 1` ones (the pre-hop's framing one plus one per pass); the source holds `k − i` units; the
rebuilt block holds `i` units against its fixed right edge `shwBase + k + 2`. -/
structure ValuePushLayout {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (vend shwBase k i : Nat) : Prop where
  hphase : (c.state.fst : Nat) = 12
  hhead : (c.head : Nat) = shwBase
  hik : i ≤ k
  hvpos : 1 ≤ vend
  hD : vend + k + 4 ≤ shwBase
  hL : shwBase + k + 4 ≤ valuePushProgram.toPhased.toTM.tapeLength L
  hvend : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    (p : Nat) = vend → c.tape p = true
  hframe : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    (p : Nat) = vend + 1 → c.tape p = false
  hentry : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    vend + 2 ≤ (p : Nat) → (p : Nat) < vend + 3 + i → c.tape p = true
  hcorr : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    vend + 3 + i ≤ (p : Nat) → (p : Nat) < shwBase → c.tape p = false
  hanchor : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    (p : Nat) = shwBase → c.tape p = true
  hsrc : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    shwBase + 1 ≤ (p : Nat) → (p : Nat) < shwBase + 1 + (k - i) → c.tape p = true
  hgap : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    shwBase + 1 + (k - i) ≤ (p : Nat) → (p : Nat) < shwBase + k + 3 - i → c.tape p = false
  hrebuilt : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    shwBase + k + 3 - i ≤ (p : Nat) → (p : Nat) < shwBase + k + 3 → c.tape p = true
  hterm : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    (p : Nat) = shwBase + k + 3 → c.tape p = false

set_option maxHeartbeats 1600000 in
/-- **Pass, value half** (L1–L7): from the layout at `i < k`, in `T ≤ 2·shwBase + 14` steps reach
phase `28`, head `shwBase`, with one extra `1` appended at `vend + 3 + i`. -/
theorem valuePush_passVal {L : Nat}
    (c0 : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (vend shwBase k i : Nat) (hlay : ValuePushLayout c0 vend shwBase k i) (hik : i < k) :
    ∃ T : Nat, T ≤ 2 * shwBase + 14
      ∧ (((TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 T).state).fst : Nat) = 28
      ∧ ((TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 T).head : Nat) = shwBase
      ∧ (TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 T).tape
          = writeBlockTape c0.tape (vend + 3 + i) [true] := by
  obtain ⟨hphase, hhead, hik', hvpos, hD, hL, hvend, hframe, hentry, hcorr, hanchor, hsrc,
    hgap, hrebuilt, hterm⟩ := hlay
  -- L1: home branch reads the source's first unit.
  obtain ⟨p1, h1, t1⟩ := valuePush_region_homeBranch.run_stepRightBranch_hop_one c0 hphase
    (by omega) (by rfl) (by rfl) (by rfl)
    (fun p hp => hsrc p (by omega) (by omega))
  set c1 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 3 with hc1
  -- L2–L3: two left steps to the home anchor's left.
  obtain ⟨p2, h2, t2⟩ := valuePush_region_passStepLeft1.run_stepLeft_hop c1 p1 (by omega)
  set c2 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c1 2 with hc2
  have h2' : (c2.head : Nat) = shwBase := by rw [h2, h1]; omega
  obtain ⟨p3, h3, t3⟩ := valuePush_region_passStepLeft2.run_stepLeft_hop c2 p2 (by omega)
  set c3 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c2 2 with hc3
  have h3' : (c3.head : Nat) = shwBase - 1 := by rw [h3, h2']
  have htc3 : c3.tape = c0.tape := by rw [t3, t2, t1]
  -- L4: scan left over the corridor onto the entry's end.
  obtain ⟨p4, h4, t4⟩ := valuePush_region_passScanLeft.run_scanLeft_hop c3 p3 (vend + 2 + i)
    (by omega)
    (fun p hp1 hp2 => by rw [htc3]; exact hcorr p (by omega) (by omega))
    (fun p hp => by rw [htc3]; exact hentry p (by omega) (by omega))
  rw [h3'] at h4 t4 p4
  set c4 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c3
    ((shwBase - 1 - (vend + 2 + i)) + 2) with hc4
  have h4' : (c4.head : Nat) = vend + 2 + i := by rw [h4]
  -- L5: step right onto the append cell.
  obtain ⟨p5, h5, t5⟩ := valuePush_region_passStepRightVal.run_stepRight_hop c4 p4 (by omega)
  set c5 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c4 2 with hc5
  have h5' : (c5.head : Nat) = vend + 3 + i := by rw [h5, h4']; omega
  -- L6: write the appended value unit.
  obtain ⟨p6, h6, t6⟩ := valuePush_region_passWriteVal.run_writeBits_hop c5 p5
    (by simp only [List.length_singleton]; omega)
  simp only [List.length_singleton] at p6 h6 t6
  set c6 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c5 2 with hc6
  have h6' : (c6.head : Nat) = vend + 4 + i := by rw [h6, h5']; omega
  have htc6 : c6.tape = writeBlockTape c0.tape (vend + 3 + i) [true] := by
    rw [t6, t5, t4, htc3, h5']
  -- L7: scan right over the corridor back onto the home anchor.
  obtain ⟨p7, h7, t7⟩ := valuePush_region_passScanRightHome.run_scanRight_hop c6 p6
    (shwBase - (vend + 4 + i)) (by omega)
    (fun p hp1 hp2 => by
      rw [htc6, writeBlockTape_singleton_ne _ _ _ _ (by omega)]
      exact hcorr p (by omega) (by omega))
    (fun p hp => by
      rw [htc6, writeBlockTape_singleton_ne _ _ _ _ (by omega)]
      exact hanchor p (by omega))
  rw [h6'] at h7
  set c7 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c6
    ((shwBase - (vend + 4 + i)) + 2) with hc7
  have h7' : (c7.head : Nat) = shwBase := by rw [h7]; omega
  have hrunA : TM.runConfig (M := valuePushProgram.toPhased.toTM) c0
      (3 + (2 + (2 + (((shwBase - 1 - (vend + 2 + i)) + 2) + (2 + (2
        + ((shwBase - (vend + 4 + i)) + 2))))))) = c7 := by
    rw [TM.runConfig_add, ← hc1]
    rw [TM.runConfig_add, ← hc2]
    rw [TM.runConfig_add, ← hc3]
    rw [TM.runConfig_add, ← hc4]
    rw [TM.runConfig_add, ← hc5]
    rw [TM.runConfig_add, ← hc6]
  refine ⟨3 + (2 + (2 + (((shwBase - 1 - (vend + 2 + i)) + 2) + (2 + (2
      + ((shwBase - (vend + 4 + i)) + 2)))))), by omega, ?_, ?_, ?_⟩
  · rw [hrunA]; exact p7
  · rw [hrunA]; exact h7'
  · rw [hrunA, t7, htc6]

set_option maxHeartbeats 1200000 in
/-- **Pass, source half A** (L8–L13): step onto the source, scan to its end, erase the rightmost
unit and re-deposit it two cells right.  From phase `28`, head `shwBase`, in `T ≤ k + 12` steps
reach phase `40`, head `shwBase + (k − i) + 3`, tape gaining the erase/deposit pair. -/
theorem valuePush_passSrcA {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (shwBase k i : Nat) (hik : i < k) (hD : k + 4 ≤ shwBase)
    (hL : shwBase + k + 4 ≤ valuePushProgram.toPhased.toTM.tapeLength L)
    (hphase : (c.state.fst : Nat) = 28) (hhead : (c.head : Nat) = shwBase)
    (hsrc : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      shwBase + 1 ≤ (p : Nat) → (p : Nat) < shwBase + 1 + (k - i) → c.tape p = true)
    (hgap : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      shwBase + 1 + (k - i) ≤ (p : Nat) → (p : Nat) < shwBase + k + 3 - i → c.tape p = false) :
    ∃ T : Nat, T ≤ k + 12
      ∧ (((TM.runConfig (M := valuePushProgram.toPhased.toTM) c T).state).fst : Nat) = 40
      ∧ ((TM.runConfig (M := valuePushProgram.toPhased.toTM) c T).head : Nat) = shwBase + (k - i) + 3
      ∧ (TM.runConfig (M := valuePushProgram.toPhased.toTM) c T).tape
          = writeBlockTape (writeBlockTape c.tape (shwBase + (k - i)) [false])
              (shwBase + (k - i) + 2) [true] := by
  -- L8: step right onto the source's first unit.
  obtain ⟨p8, h8, t8⟩ := valuePush_region_passStepRightSrc.run_stepRight_hop c hphase (by omega)
  rw [hhead] at h8
  set c8 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c 2 with hc8
  have h8' : (c8.head : Nat) = shwBase + 1 := by rw [h8]
  -- L9: scan right over the source run onto its stop zero.
  obtain ⟨p9, h9, t9⟩ := valuePush_region_passScanRightOnes.run_scanRightOnes_hop c8 p8 (k - i)
    (by omega)
    (fun p hp1 hp2 => by rw [t8]; exact hsrc p (by omega) (by omega))
    (fun p hp => by rw [t8]; exact hgap p (by omega) (by omega))
  rw [h8'] at h9
  set c9 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c8 ((k - i) + 2) with hc9
  have h9' : (c9.head : Nat) = shwBase + 1 + (k - i) := by rw [h9]
  have htc9 : c9.tape = c.tape := by rw [t9, t8]
  -- L10: step left onto the source's last unit.
  obtain ⟨p10, h10, t10⟩ := valuePush_region_passStepLeftErase.run_stepLeft_hop c9 p9 (by omega)
  set c10 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c9 2 with hc10
  have h10' : (c10.head : Nat) = shwBase + (k - i) := by rw [h10, h9']; omega
  -- L11: erase it.
  obtain ⟨p11, h11, t11⟩ := valuePush_region_passErase.run_writeBits_hop c10 p10
    (by simp only [List.length_singleton]; omega)
  simp only [List.length_singleton] at p11 h11 t11
  set c11 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c10 2 with hc11
  have h11' : (c11.head : Nat) = shwBase + (k - i) + 1 := by rw [h11, h10']
  have htc11 : c11.tape = writeBlockTape c.tape (shwBase + (k - i)) [false] := by
    rw [t11, t10, htc9, h10']
  -- L12: step right over the gap cell.
  obtain ⟨p12, h12, t12⟩ := valuePush_region_passStepRightDeposit.run_stepRight_hop c11 p11
    (by omega)
  set c12 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c11 2 with hc12
  have h12' : (c12.head : Nat) = shwBase + (k - i) + 2 := by rw [h12, h11']
  -- L13: re-deposit the unit.
  obtain ⟨p13, h13, t13⟩ := valuePush_region_passDeposit.run_writeBits_hop c12 p12
    (by simp only [List.length_singleton]; omega)
  simp only [List.length_singleton] at p13 h13 t13
  set c13 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c12 2 with hc13
  have h13' : (c13.head : Nat) = shwBase + (k - i) + 3 := by rw [h13, h12']
  have htc13 : c13.tape = writeBlockTape (writeBlockTape c.tape (shwBase + (k - i)) [false])
      (shwBase + (k - i) + 2) [true] := by
    rw [t13, t12, htc11, h12']
  have hrun : TM.runConfig (M := valuePushProgram.toPhased.toTM) c
      (2 + (((k - i) + 2) + (2 + (2 + (2 + 2))))) = c13 := by
    rw [TM.runConfig_add, ← hc8]
    rw [TM.runConfig_add, ← hc9]
    rw [TM.runConfig_add, ← hc10]
    rw [TM.runConfig_add, ← hc11]
    rw [TM.runConfig_add, ← hc12]
  refine ⟨2 + (((k - i) + 2) + (2 + (2 + (2 + 2)))), by omega, ?_, ?_, ?_⟩
  · rw [hrun]; exact p13
  · rw [hrun]; exact h13'
  · rw [hrun]; exact htc13

set_option maxHeartbeats 1200000 in
/-- **Pass, source half B** (L14–L16): walk back from the deposit to the home anchor.  From phase
`40`, head `shwBase + (k − i) + 3`, with the home anchor, the source remainder and the left
corridor cell, in `T ≤ k + 12` steps reach phase `12`, head `shwBase`, tape unchanged. -/
theorem valuePush_passSrcB {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (shwBase k i : Nat) (hik : i < k) (hD : k + 4 ≤ shwBase)
    (hL : shwBase + k + 4 ≤ valuePushProgram.toPhased.toTM.tapeLength L)
    (hphase : (c.state.fst : Nat) = 40) (hhead : (c.head : Nat) = shwBase + (k - i) + 3)
    (hleft : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = shwBase - 1 → c.tape p = false)
    (hanchor : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = shwBase → c.tape p = true)
    (hsrcrem : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      shwBase + 1 ≤ (p : Nat) → (p : Nat) < shwBase + (k - i) → c.tape p = true) :
    ∃ T : Nat, T ≤ k + 12
      ∧ (((TM.runConfig (M := valuePushProgram.toPhased.toTM) c T).state).fst : Nat) = 12
      ∧ ((TM.runConfig (M := valuePushProgram.toPhased.toTM) c T).head : Nat) = shwBase
      ∧ (TM.runConfig (M := valuePushProgram.toPhased.toTM) c T).tape = c.tape := by
  -- L14: four fixed left steps.
  obtain ⟨p14a, h14a, t14a⟩ := valuePush_region_passHomeLeft1.run_stepLeft_hop c hphase (by omega)
  rw [hhead] at h14a
  set c14a := TM.runConfig (M := valuePushProgram.toPhased.toTM) c 2 with hc14a
  have h14a' : (c14a.head : Nat) = shwBase + (k - i) + 2 := by rw [h14a]; omega
  obtain ⟨p14b, h14b, t14b⟩ := valuePush_region_passHomeLeft2.run_stepLeft_hop c14a p14a (by omega)
  set c14b := TM.runConfig (M := valuePushProgram.toPhased.toTM) c14a 2 with hc14b
  have h14b' : (c14b.head : Nat) = shwBase + (k - i) + 1 := by rw [h14b, h14a']; omega
  obtain ⟨p14c, h14c, t14c⟩ := valuePush_region_passHomeLeft3.run_stepLeft_hop c14b p14b (by omega)
  set c14c := TM.runConfig (M := valuePushProgram.toPhased.toTM) c14b 2 with hc14c
  have h14c' : (c14c.head : Nat) = shwBase + (k - i) := by rw [h14c, h14b']; omega
  obtain ⟨p14d, h14d, t14d⟩ := valuePush_region_passHomeLeft4.run_stepLeft_hop c14c p14c (by omega)
  set c14d := TM.runConfig (M := valuePushProgram.toPhased.toTM) c14c 2 with hc14d
  have h14d' : (c14d.head : Nat) = shwBase + (k - i) - 1 := by rw [h14d, h14c']
  have htc14 : c14d.tape = c.tape := by rw [t14d, t14c, t14b, t14a]
  -- L15: scan left over the source remainder and the anchor onto the left corridor cell.
  obtain ⟨p15, h15, t15⟩ := valuePush_region_passHomeOnes.run_scanLeftOnes_hop c14d p14d
    (shwBase - 1) (by omega)
    (fun p hp1 hp2 => by
      rw [htc14]
      by_cases hp : (p : Nat) = shwBase
      · exact hanchor p hp
      · exact hsrcrem p (by omega) (by omega))
    (fun p hp => by rw [htc14]; exact hleft p hp)
  rw [h14d'] at p15 h15 t15
  set c15 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c14d
    (((shwBase + (k - i) - 1) - (shwBase - 1)) + 2) with hc15
  have h15' : (c15.head : Nat) = shwBase - 1 := by rw [h15]
  have htc15 : c15.tape = c.tape := by rw [t15, htc14]
  -- L16: step right back onto the home anchor.
  obtain ⟨p16, h16, t16⟩ := valuePush_region_passHomeStepRight.run_stepRight_hop c15 p15 (by omega)
  set c16 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c15 2 with hc16
  have h16' : (c16.head : Nat) = shwBase := by rw [h16, h15']; omega
  have htc16 : c16.tape = c.tape := by rw [t16, htc15]
  have hrun : TM.runConfig (M := valuePushProgram.toPhased.toTM) c
      (2 + (2 + (2 + (2 + ((((shwBase + (k - i) - 1) - (shwBase - 1)) + 2) + 2))))) = c16 := by
    rw [TM.runConfig_add, ← hc14a]
    rw [TM.runConfig_add, ← hc14b]
    rw [TM.runConfig_add, ← hc14c]
    rw [TM.runConfig_add, ← hc14d]
    rw [TM.runConfig_add, ← hc15]
  refine ⟨2 + (2 + (2 + (2 + ((((shwBase + (k - i) - 1) - (shwBase - 1)) + 2) + 2)))),
    by omega, ?_, ?_, ?_⟩
  · rw [hrun]; exact p16
  · rw [hrun]; exact h16'
  · rw [hrun]; exact htc16

/-- **Pass, source half** (L8–L16): the two source quarters composed. -/
theorem valuePush_passSrc {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (vend shwBase k i : Nat) (hik : i < k) (hvpos : 1 ≤ vend) (hD : vend + k + 4 ≤ shwBase)
    (hL : shwBase + k + 4 ≤ valuePushProgram.toPhased.toTM.tapeLength L)
    (hphase : (c.state.fst : Nat) = 28) (hhead : (c.head : Nat) = shwBase)
    (hleft : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = shwBase - 1 → c.tape p = false)
    (hanchor : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = shwBase → c.tape p = true)
    (hsrc : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      shwBase + 1 ≤ (p : Nat) → (p : Nat) < shwBase + 1 + (k - i) → c.tape p = true)
    (hgap : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      shwBase + 1 + (k - i) ≤ (p : Nat) → (p : Nat) < shwBase + k + 3 - i → c.tape p = false) :
    ∃ T : Nat, T ≤ 2 * k + 24
      ∧ (((TM.runConfig (M := valuePushProgram.toPhased.toTM) c T).state).fst : Nat) = 12
      ∧ ((TM.runConfig (M := valuePushProgram.toPhased.toTM) c T).head : Nat) = shwBase
      ∧ (TM.runConfig (M := valuePushProgram.toPhased.toTM) c T).tape
          = writeBlockTape (writeBlockTape c.tape (shwBase + (k - i)) [false])
              (shwBase + (k - i) + 2) [true] := by
  obtain ⟨TA, hTA, pA, hA, tA⟩ := valuePush_passSrcA c shwBase k i hik (by omega) hL hphase hhead
    hsrc hgap
  set cA := TM.runConfig (M := valuePushProgram.toPhased.toTM) c TA with hcA
  obtain ⟨TB, hTB, pB, hB, tB⟩ := valuePush_passSrcB cA shwBase k i hik (by omega) hL pA hA
    (fun p hp => by
      rw [tA, writeBlockTape_singleton_ne _ _ _ _ (by omega),
        writeBlockTape_singleton_ne _ _ _ _ (by omega)]; exact hleft p hp)
    (fun p hp => by
      rw [tA, writeBlockTape_singleton_ne _ _ _ _ (by omega),
        writeBlockTape_singleton_ne _ _ _ _ (by omega)]; exact hanchor p hp)
    (fun p hp1 hp2 => by
      rw [tA, writeBlockTape_singleton_ne _ _ _ _ (by omega),
        writeBlockTape_singleton_ne _ _ _ _ (by omega)]; exact hsrc p hp1 (by omega))
  refine ⟨TA + TB, by omega, ?_, ?_, ?_⟩
  · rw [TM.runConfig_add, ← hcA]; exact pB
  · rw [TM.runConfig_add, ← hcA]; exact hB
  · rw [TM.runConfig_add, ← hcA, tB, tA]

set_option maxHeartbeats 1200000 in
/-- **One fan-out pass** (`i < k`): in `T ≤ 2·shwBase + 2·k + 38` steps the layout holds at
`i + 1`, and the tape changed in exactly the three cells (appended value unit, erased source unit,
re-deposited rebuilt unit). -/
theorem valuePush_pass {L : Nat}
    (c0 : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (vend shwBase k i : Nat) (hlay : ValuePushLayout c0 vend shwBase k i) (hik : i < k) :
    ∃ T : Nat, T ≤ 2 * shwBase + 2 * k + 38
      ∧ ValuePushLayout (TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 T)
          vend shwBase k (i + 1)
      ∧ ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
          (p : Nat) ≠ vend + 3 + i → (p : Nat) ≠ shwBase + (k - i) →
          (p : Nat) ≠ shwBase + (k - i) + 2 →
          (TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 T).tape p = c0.tape p := by
  have hlay' := hlay
  obtain ⟨hphase, hhead, hik', hvpos, hD, hL, hvend, hframe, hentry, hcorr, hanchor, hsrc,
    hgap, hrebuilt, hterm⟩ := hlay
  obtain ⟨TA, hTA, pA, hA, tA⟩ := valuePush_passVal c0 vend shwBase k i hlay' hik
  set cA := TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 TA with hcA
  obtain ⟨TB, hTB, pB, hB, tB⟩ := valuePush_passSrc cA vend shwBase k i hik hvpos hD hL pA hA
    (fun p hp => by
      rw [tA, writeBlockTape_singleton_ne _ _ _ _ (by omega)]; exact hcorr p (by omega) (by omega))
    (fun p hp => by
      rw [tA, writeBlockTape_singleton_ne _ _ _ _ (by omega)]; exact hanchor p hp)
    (fun p hp1 hp2 => by
      rw [tA, writeBlockTape_singleton_ne _ _ _ _ (by omega)]; exact hsrc p hp1 hp2)
    (fun p hp1 hp2 => by
      rw [tA, writeBlockTape_singleton_ne _ _ _ _ (by omega)]; exact hgap p hp1 hp2)
  set cB := TM.runConfig (M := valuePushProgram.toPhased.toTM) cA TB with hcB
  have hrun : TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 (TA + TB) = cB := by
    rw [TM.runConfig_add, ← hcA, ← hcB]
  have htB : cB.tape = writeBlockTape (writeBlockTape (writeBlockTape c0.tape (vend + 3 + i) [true])
      (shwBase + (k - i)) [false]) (shwBase + (k - i) + 2) [true] := by
    rw [tB, tA]
  have hcell : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      (p : Nat) ≠ vend + 3 + i → (p : Nat) ≠ shwBase + (k - i) →
      (p : Nat) ≠ shwBase + (k - i) + 2 → cB.tape p = c0.tape p := by
    intro p hne1 hne2 hne3
    rw [htB, writeBlockTape_singleton_ne _ _ _ _ hne3,
      writeBlockTape_singleton_ne _ _ _ _ hne2, writeBlockTape_singleton_ne _ _ _ _ hne1]
  have hval : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = vend + 3 + i → cB.tape p = true := by
    intro p hp
    rw [htB, writeBlockTape_singleton_ne _ _ _ _ (by omega),
      writeBlockTape_singleton_ne _ _ _ _ (by omega), writeBlockTape_singleton_eq _ _ _ _ hp]
  have herase : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = shwBase + (k - i) → cB.tape p = false := by
    intro p hp
    rw [htB, writeBlockTape_singleton_ne _ _ _ _ (by omega), writeBlockTape_singleton_eq _ _ _ _ hp]
  have hdep : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = shwBase + (k - i) + 2 → cB.tape p = true := by
    intro p hp
    rw [htB, writeBlockTape_singleton_eq _ _ _ _ hp]
  refine ⟨TA + TB, by omega, ?_, ?_⟩
  · rw [hrun]
    refine ⟨pB, hB, by omega, hvpos, hD, hL, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp; rw [hcell p (by omega) (by omega) (by omega)]; exact hvend p hp
    · intro p hp; rw [hcell p (by omega) (by omega) (by omega)]; exact hframe p hp
    · intro p hp1 hp2
      by_cases hp : (p : Nat) = vend + 3 + i
      · exact hval p hp
      · rw [hcell p hp (by omega) (by omega)]; exact hentry p hp1 (by omega)
    · intro p hp1 hp2; rw [hcell p (by omega) (by omega) (by omega)]; exact hcorr p (by omega) hp2
    · intro p hp; rw [hcell p (by omega) (by omega) (by omega)]; exact hanchor p hp
    · intro p hp1 hp2; rw [hcell p (by omega) (by omega) (by omega)]; exact hsrc p hp1 (by omega)
    · intro p hp1 hp2
      by_cases hp : (p : Nat) = shwBase + (k - i)
      · exact herase p hp
      · rw [hcell p (by omega) hp (by omega)]; exact hgap p (by omega) (by omega)
    · intro p hp1 hp2
      by_cases hp : (p : Nat) = shwBase + (k - i) + 2
      · exact hdep p hp
      · rw [hcell p (by omega) (by omega) hp]; exact hrebuilt p (by omega) hp2
    · intro p hp; rw [hcell p (by omega) (by omega) (by omega)]; exact hterm p hp
  · rw [hrun]; exact hcell

end ContractExpansion
end Frontier
end Pnp4
