import Pnp4.Frontier.ContractExpansion.TreeMCSPValuePushRun

/-!
# `valuePush` mid-round confinement — D2t-5b (A5m-V, M2 confinement, part 3)

The drain loop's mid-round safety stream, split at a **mid-round cut** to fit the elaborator's
memory budget (the monolithic replay of all twenty legs exceeds it — the same remedy as the
`DrainFinalCut` split of the final round):

* `DrainMidCut` — the round's state after the entry deposit and the return across the anchor
  (offset `2·(aPos − opBase) − e` into the round): phase φ11 one right of the anchor, entry
  extended, erased prefix grown, scratch not yet extended;
* `valuePush_drain_mid_cut` — the front half reaches the cut, with its safety stream;
* `valuePush_drain_mid_back_confined` — the back half's safety stream from the cut;
* `valuePush_drain_mid_confined` — the assembled per-step stream for the whole round, the
  companion to `valuePush_drain_mid` that the region-embedding transfer
  (`RegionEmbeddedMulti.run_track`) consumes.

The streamed safety predicate is `phase ≠ 34 ∧ head ≤ aPos + 2k + 2`: φ34 is `valuePush`'s
**only** exit phase (the region embedding redirects exactly `exitAt 34`), so `phase ≠ 34` per
step is precisely `run_track`'s "no early exit" obligation — if `valuePush` ever grew a second
exit phase, every `_confined` stream here and in the Headline would need the extra disjunct.

**Progress classification (AGENTS.md): Infrastructure** — per-step safety facts for a staging
machine's verified run; proves no separation.  Standard `[propext, Classical.choice, Quot.sound]`
triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **The mid-round cut state** (after the entry deposit and the return across the anchor, at
offset `2·(aPos − opBase) − e` into the round): phase φ11 one right of the anchor, the entry
already extended to `e + 1` deposits, the erased prefix grown by the round's unit, the scratch
still at `e`. -/
structure DrainMidCut {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (opBase aPos k e : Nat) : Prop where
  hphase : ((c.state).fst : Nat) = 11
  hhead : (c.head : Nat) = aPos + 1
  hgeom : opBase + k + 4 ≤ aPos
  hbound : aPos + 2 * k + 3 ≤ valuePushProgram.toPhased.toTM.tapeLength L
  he2 : e + 1 < k
  hhome : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    (p : Nat) = opBase → c.tape p = false
  hentry : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    opBase + 1 ≤ (p : Nat) → (p : Nat) < opBase + 3 + (e + 1) → c.tape p = true
  hgapL : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    opBase + 3 + (e + 1) ≤ (p : Nat) → (p : Nat) < aPos → c.tape p = false
  hanchor : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    (p : Nat) = aPos → c.tape p = true
  hpre : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    aPos < (p : Nat) → (p : Nat) < aPos + 1 + (e + 1) → c.tape p = false
  hrest : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    aPos + 1 + (e + 1) ≤ (p : Nat) → (p : Nat) < aPos + 1 + k → c.tape p = true
  hterm : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    (p : Nat) = aPos + 1 + k → c.tape p = false
  hscr : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    aPos + 2 + k ≤ (p : Nat) → (p : Nat) < aPos + 2 + k + e → c.tape p = true
  hzr : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    aPos + 2 + k + e ≤ (p : Nat) → (p : Nat) ≤ aPos + 2 * k + 2 → c.tape p = false

set_option maxHeartbeats 4000000 in
/-- **Mid-round front half** (`e + 1 < k`): the round's first `2·(aPos − opBase) − e` steps reach
the cut state, and along the way the phase never reaches the accept and the head stays
≤ `aPos + 2k + 2` (the front of the round's safety stream). -/
theorem valuePush_drain_mid_cut {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (opBase aPos k e : Nat) (hds : DrainState c opBase aPos k e) (he2 : e + 1 < k) :
    DrainMidCut
      (TM.runConfig (M := valuePushProgram.toPhased.toTM) c (2 * (aPos - opBase) - e))
      opBase aPos k e
    ∧ (∀ s : Nat, s < 2 * (aPos - opBase) - e →
        (((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).state).fst : Nat) ≠ 34
        ∧ ((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).head : Nat)
            ≤ aPos + 2 * k + 2) := by
  obtain ⟨hphase, hhead, hgeom, hbound, _, hhome, hentry, hgapL, hanchor, hpre, hrest,
    hterm, hscr, hzr⟩ := hds
  obtain ⟨h1p, h1h, h1t⟩ := valuePush_step c (valuePush_state_eta c (by omega) hphase)
    (valuePushProgram_t5 (c.tape c.head))
  set c1 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c with hc1
  have h1p' : ((c1.state).fst : Nat) = 6 := h1p
  have h1h' : (c1.head : Nat) = aPos + 2 + e := by
    rw [hc1, h1h]
    simp only [Configuration.moveHead, dif_pos (show (c.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have h1t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c1.tape p = if (p : Nat) = aPos + 1 + e then false else c.tape p := by
    intro p
    rw [hc1, h1t]
    exact valuePush_write_char c false hhead p
  have hb1 : c1.tape c1.head = true := by
    rw [h1t' c1.head, if_neg (by omega)]
    exact hrest c1.head (by omega) (by omega)
  obtain ⟨h2p, h2h, h2t⟩ := valuePush_step c1 (valuePush_state_eta c1 (by omega) h1p)
    (by rw [hb1]; exact valuePushProgram_t6_one)
  set c2 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c1 with hc2
  have h2p' : ((c2.state).fst : Nat) = 7 := h2p
  have h2h' : (c2.head : Nat) = aPos + 1 + e := by
    rw [hc2, h2h, Configuration.moveHead_left_val_of_pos c1 (by omega)]
    omega
  have hwf1 : c1.write c1.head true = c1.tape := by
    rw [← hb1]; exact write_self_eq c1
  have h2t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c2.tape p = if (p : Nat) = aPos + 1 + e then false else c.tape p := by
    intro p
    rw [hc2, h2t, hwf1, h1t' p]
  obtain ⟨h3p, h3h, h3t⟩ := valuePush_run_scanL0 7 (by omega) rfl c2 h2p (e + 1)
    (by omega)
    (fun p hp1 hp2 => by
      rw [h2t' p]
      by_cases hq : (p : Nat) = aPos + 1 + e
      · rw [if_pos hq]
      · rw [if_neg hq]
        exact hpre p (by omega) (by omega))
  set c3 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c2 (e + 1) with hc3
  have h3h' : (c3.head : Nat) = aPos := by omega
  have hb3 : c3.tape c3.head = true := by
    rw [h3t, h2t' c3.head, if_neg (by omega)]
    exact hanchor c3.head (by omega)
  obtain ⟨h4p, h4h, h4t⟩ := valuePush_step c3 (valuePush_state_eta c3 (by omega) h3p)
    (by rw [hb3]; exact valuePushProgram_t7_one)
  set c4 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c3 with hc4
  have h4p' : ((c4.state).fst : Nat) = 8 := h4p
  have h4h' : (c4.head : Nat) = aPos - 1 := by
    rw [hc4, h4h, Configuration.moveHead_left_val_of_pos c3 (by omega)]
    omega
  have hwf3 : c3.write c3.head true = c3.tape := by
    rw [← hb3]; exact write_self_eq c3
  have h4t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c4.tape p = if (p : Nat) = aPos + 1 + e then false else c.tape p := by
    intro p
    rw [hc4, h4t, hwf3, h3t, h2t' p]
  obtain ⟨h5p, h5h, h5t⟩ := valuePush_run_scanL0 8 (by omega) rfl c4 h4p
    (aPos - opBase - e - 3)
    (by omega)
    (fun p hp1 hp2 => by
      rw [h4t' p, if_neg (by omega)]
      exact hgapL p (by omega) (by omega))
  set c5 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c4 (aPos - opBase - e - 3)
    with hc5
  have h5h' : (c5.head : Nat) = opBase + 2 + e := by omega
  have hb5 : c5.tape c5.head = true := by
    rw [h5t, h4t' c5.head, if_neg (by omega)]
    exact hentry c5.head (by omega) (by omega)
  obtain ⟨h6p, h6h, h6t⟩ := valuePush_step c5 (valuePush_state_eta c5 (by omega) h5p)
    (by rw [hb5]; exact valuePushProgram_t8_one)
  set c6 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c5 with hc6
  have h6p' : ((c6.state).fst : Nat) = 9 := h6p
  have h6h' : (c6.head : Nat) = opBase + 3 + e := by
    rw [hc6, h6h]
    simp only [Configuration.moveHead, dif_pos (show (c5.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have hwf5 : c5.write c5.head true = c5.tape := by
    rw [← hb5]; exact write_self_eq c5
  have h6t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c6.tape p = if (p : Nat) = aPos + 1 + e then false else c.tape p := by
    intro p
    rw [hc6, h6t, hwf5, h5t, h4t' p]
  obtain ⟨h7p, h7h, h7t⟩ := valuePush_step c6 (valuePush_state_eta c6 (by omega) h6p)
    (valuePushProgram_t9 (c6.tape c6.head))
  set c7 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c6 with hc7
  have h7p' : ((c7.state).fst : Nat) = 10 := h7p
  have h7h' : (c7.head : Nat) = opBase + 4 + e := by
    rw [hc7, h7h]
    simp only [Configuration.moveHead, dif_pos (show (c6.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have h7t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c7.tape p = if (p : Nat) = opBase + 3 + e then true
        else if (p : Nat) = aPos + 1 + e then false else c.tape p := by
    intro p
    rw [hc7, h7t, valuePush_write_char c6 true h6h' p, h6t' p]
  obtain ⟨h8p, h8h, h8t⟩ := valuePush_run_scanR0 10 (by omega) rfl c7 h7p
    (aPos - opBase - e - 4)
    (by omega)
    (fun p hp1 hp2 => by
      rw [h7t' p, if_neg (by omega), if_neg (by omega)]
      exact hgapL p (by omega) (by omega))
  set c8 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c7 (aPos - opBase - e - 4)
    with hc8
  have h8h' : (c8.head : Nat) = aPos := by omega
  have hb8 : c8.tape c8.head = true := by
    rw [h8t, h7t' c8.head, if_neg (by omega), if_neg (by omega)]
    exact hanchor c8.head (by omega)
  obtain ⟨h9p, h9h, h9t⟩ := valuePush_step c8 (valuePush_state_eta c8 (by omega) h8p)
    (by rw [hb8]; exact valuePushProgram_t10_one)
  set c9 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c8 with hc9
  have h9p' : ((c9.state).fst : Nat) = 11 := h9p
  have h9h' : (c9.head : Nat) = aPos + 1 := by
    rw [hc9, h9h]
    simp only [Configuration.moveHead, dif_pos (show (c8.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have hwf8 : c8.write c8.head true = c8.tape := by
    rw [← hb8]; exact write_self_eq c8
  have h9t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c9.tape p = if (p : Nat) = opBase + 3 + e then true
        else if (p : Nat) = aPos + 1 + e then false else c.tape p := by
    intro p
    rw [hc9, h9t, hwf8, h8t, h7t' p]
  have hcfg1 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c 1 = c1 := by
    rw [valuePush_runConfig_one, ← hc1]
  have hcfg2 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c 2 = c2 := by
    rw [show (2 : Nat) = 1 + 1 from rfl, TM.runConfig_add, hcfg1,
      valuePush_runConfig_one, ← hc2]
  have hcfg3 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c (2 + (e + 1)) = c3 := by
    rw [TM.runConfig_add, hcfg2, ← hc3]
  have hcfg4 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c (2 + (e + 1) + 1) = c4 := by
    rw [TM.runConfig_succ, hcfg3, ← hc4]
  have hcfg5 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c
      (2 + (e + 1) + 1 + (aPos - opBase - e - 3)) = c5 := by
    rw [TM.runConfig_add, hcfg4, ← hc5]
  have hcfg6 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c
      (2 + (e + 1) + 1 + (aPos - opBase - e - 3) + 1) = c6 := by
    rw [TM.runConfig_succ, hcfg5, ← hc6]
  have hcfg7 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c
      (2 + (e + 1) + 1 + (aPos - opBase - e - 3) + 2) = c7 := by
    rw [show 2 + (e + 1) + 1 + (aPos - opBase - e - 3) + 2
        = 2 + (e + 1) + 1 + (aPos - opBase - e - 3) + 1 + 1 from by omega,
      TM.runConfig_succ, hcfg6, ← hc7]
  have hcfg8 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c
      (2 + (e + 1) + 1 + (aPos - opBase - e - 3) + 2 + (aPos - opBase - e - 4)) = c8 := by
    rw [TM.runConfig_add, hcfg7, ← hc8]
  have hcfg9 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c
      (2 + (e + 1) + 1 + (aPos - opBase - e - 3) + 2 + (aPos - opBase - e - 4) + 1) = c9 := by
    rw [TM.runConfig_succ, hcfg8, ← hc9]
  constructor
  · -- the cut state at o₉ = 2·(aPos − opBase) − e
    rw [show 2 * (aPos - opBase) - e
        = 2 + (e + 1) + 1 + (aPos - opBase - e - 3) + 2 + (aPos - opBase - e - 4) + 1
        from by omega, hcfg9]
    refine ⟨h9p', h9h', hgeom, hbound, he2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      rw [h9t' p, if_neg (by omega), if_neg (by omega)]
      exact hhome p hp
    · intro p hp1 hp2
      rw [h9t' p]
      by_cases hq : (p : Nat) = opBase + 3 + e
      · rw [if_pos hq]
      · rw [if_neg hq, if_neg (by omega)]
        exact hentry p (by omega) (by omega)
    · intro p hp1 hp2
      rw [h9t' p, if_neg (by omega), if_neg (by omega)]
      exact hgapL p (by omega) (by omega)
    · intro p hp
      rw [h9t' p, if_neg (by omega), if_neg (by omega)]
      exact hanchor p hp
    · intro p hp1 hp2
      rw [h9t' p, if_neg (by omega)]
      by_cases hq : (p : Nat) = aPos + 1 + e
      · rw [if_pos hq]
      · rw [if_neg hq]
        exact hpre p (by omega) (by omega)
    · intro p hp1 hp2
      rw [h9t' p, if_neg (by omega), if_neg (by omega)]
      exact hrest p (by omega) (by omega)
    · intro p hp
      rw [h9t' p, if_neg (by omega), if_neg (by omega)]
      exact hterm p hp
    · intro p hp1 hp2
      rw [h9t' p, if_neg (by omega), if_neg (by omega)]
      exact hscr p (by omega) (by omega)
    · intro p hp1 hp2
      rw [h9t' p, if_neg (by omega), if_neg (by omega)]
      exact hzr p (by omega) (by omega)
  · -- the front safety stream
    intro s hs
    by_cases hA : s = 0
    · subst hA
      rw [TM.runConfig_zero]
      exact ⟨by omega, by omega⟩
    by_cases hB : s = 1
    · subst hB
      rw [hcfg1]
      exact ⟨by omega, by omega⟩
    by_cases hC : s < 2 + (e + 1)
    · obtain ⟨hrp, hrh, _⟩ := valuePush_run_scanL0 7 (by omega) rfl c2 h2p (s - 2)
        (by omega)
        (fun p hp1 hp2 => by
          rw [h2t' p]
          by_cases hq : (p : Nat) = aPos + 1 + e
          · rw [if_pos hq]
          · rw [if_neg hq]
            exact hpre p (by omega) (by omega))
      rw [show s = 2 + (s - 2) from by omega, TM.runConfig_add, hcfg2]
      exact ⟨by omega, by omega⟩
    by_cases hD : s = 2 + (e + 1)
    · subst hD
      rw [hcfg3]
      exact ⟨by omega, by omega⟩
    by_cases hE : s < 2 + (e + 1) + 1 + (aPos - opBase - e - 3)
    · obtain ⟨hrp, hrh, _⟩ := valuePush_run_scanL0 8 (by omega) rfl c4 h4p
        (s - (2 + (e + 1) + 1))
        (by omega)
        (fun p hp1 hp2 => by
          rw [h4t' p, if_neg (by omega)]
          exact hgapL p (by omega) (by omega))
      rw [show s = (2 + (e + 1) + 1) + (s - (2 + (e + 1) + 1)) from by omega,
        TM.runConfig_add, hcfg4]
      exact ⟨by omega, by omega⟩
    by_cases hF : s = 2 + (e + 1) + 1 + (aPos - opBase - e - 3)
    · subst hF
      rw [hcfg5]
      exact ⟨by omega, by omega⟩
    by_cases hG : s = 2 + (e + 1) + 1 + (aPos - opBase - e - 3) + 1
    · subst hG
      rw [hcfg6]
      exact ⟨by omega, by omega⟩
    by_cases hH : s < 2 + (e + 1) + 1 + (aPos - opBase - e - 3) + 2 + (aPos - opBase - e - 4)
    · obtain ⟨hrp, hrh, _⟩ := valuePush_run_scanR0 10 (by omega) rfl c7 h7p
        (s - (2 + (e + 1) + 1 + (aPos - opBase - e - 3) + 2))
        (by omega)
        (fun p hp1 hp2 => by
          rw [h7t' p, if_neg (by omega), if_neg (by omega)]
          exact hgapL p (by omega) (by omega))
      rw [show s = (2 + (e + 1) + 1 + (aPos - opBase - e - 3) + 2)
          + (s - (2 + (e + 1) + 1 + (aPos - opBase - e - 3) + 2)) from by omega,
        TM.runConfig_add, hcfg7]
      exact ⟨by omega, by omega⟩
    -- s = o₈ (the anchor cell, φ10)
    · have hI : s = 2 + (e + 1) + 1 + (aPos - opBase - e - 3) + 2 + (aPos - opBase - e - 4) := by
        omega
      subst hI
      rw [hcfg8]
      exact ⟨by omega, by omega⟩

end ContractExpansion
end Frontier
end Pnp4

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

set_option maxHeartbeats 4000000 in
/-- **Mid-round back half**: from the cut state, the remaining `2k + e + 3` steps of the round
stay safe (phase never the accept, head ≤ `aPos + 2k + 2`). -/
theorem valuePush_drain_mid_back_confined {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (opBase aPos k e : Nat) (hcut : DrainMidCut c opBase aPos k e) :
    ∀ s : Nat, s < 2 * k + e + 3 →
      (((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).state).fst : Nat) ≠ 34
      ∧ ((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).head : Nat)
          ≤ aPos + 2 * k + 2 := by
  obtain ⟨hphase, hhead, hgeom, hbound, he2, hhome, hentry, hgapL, hanchor, hpre, hrest,
    hterm, hscr, hzr⟩ := hcut
  obtain ⟨h1p, h1h, h1t⟩ := valuePush_run_scanR0 11 (by omega) rfl c hphase (e + 1)
    (by omega)
    (fun p hp1 hp2 => by
      exact hpre p (by omega) (by omega))
  set d1 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c (e + 1) with hd1
  have h1h' : (d1.head : Nat) = aPos + 2 + e := by omega
  have hb1 : d1.tape d1.head = true := by
    rw [h1t]
    exact hrest d1.head (by omega) (by omega)
  obtain ⟨h2p, h2h, h2t⟩ := valuePush_step d1 (valuePush_state_eta d1 (by omega) h1p)
    (by rw [hb1]; exact valuePushProgram_t11_one)
  set d2 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) d1 with hd2
  have h2p' : ((d2.state).fst : Nat) = 12 := h2p
  have h2h' : (d2.head : Nat) = aPos + 3 + e := by
    rw [hd2, h2h]
    simp only [Configuration.moveHead, dif_pos (show (d1.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have hwf1 : d1.write d1.head true = d1.tape := by
    rw [← hb1]; exact write_self_eq d1
  have h2t' : d2.tape = c.tape := by
    rw [hd2, h2t, hwf1, h1t]
  obtain ⟨h3p, h3h, h3t⟩ := valuePush_run_walkR1 12 (by omega) rfl d2 h2p (k - e - 2)
    (by omega)
    (fun p hp1 hp2 => by
      rw [h2t']
      exact hrest p (by omega) (by omega))
  set d3 := TM.runConfig (M := valuePushProgram.toPhased.toTM) d2 (k - e - 2) with hd3
  have h3h' : (d3.head : Nat) = aPos + 1 + k := by omega
  have hb3 : d3.tape d3.head = false := by
    rw [h3t, h2t']
    exact hterm d3.head (by omega)
  obtain ⟨h4p, h4h, h4t⟩ := valuePush_step d3 (valuePush_state_eta d3 (by omega) h3p)
    (by rw [hb3]; exact valuePushProgram_t12_zero)
  set d4 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) d3 with hd4
  have h4p' : ((d4.state).fst : Nat) = 13 := h4p
  have h4h' : (d4.head : Nat) = aPos + 2 + k := by
    rw [hd4, h4h]
    simp only [Configuration.moveHead, dif_pos (show (d3.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have hwf3 : d3.write d3.head false = d3.tape := by
    rw [← hb3]; exact write_self_eq d3
  have h4t' : d4.tape = c.tape := by
    rw [hd4, h4t, hwf3, h3t, h2t']
  obtain ⟨h5p, h5h, h5t⟩ := valuePush_run_walkR1 13 (by omega) rfl d4 h4p e
    (by omega)
    (fun p hp1 hp2 => by
      rw [h4t']
      exact hscr p (by omega) (by omega))
  set d5 := TM.runConfig (M := valuePushProgram.toPhased.toTM) d4 e with hd5
  have h5h' : (d5.head : Nat) = aPos + 2 + k + e := by omega
  have hb5 : d5.tape d5.head = false := by
    rw [h5t, h4t']
    exact hzr d5.head (by omega) (by omega)
  obtain ⟨h6p, h6h, h6t⟩ := valuePush_step d5 (valuePush_state_eta d5 (by omega) h5p)
    (by rw [hb5]; exact valuePushProgram_t13_zero)
  set d6 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) d5 with hd6
  have h6p' : ((d6.state).fst : Nat) = 14 := h6p
  have h6h' : (d6.head : Nat) = aPos + 1 + k + e := by
    rw [hd6, h6h, Configuration.moveHead_left_val_of_pos d5 (by omega)]
    omega
  have h6t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      d6.tape p = if (p : Nat) = aPos + 2 + k + e then true else c.tape p := by
    intro p
    rw [hd6, h6t, valuePush_write_char d5 true h5h' p, h5t, h4t']
  obtain ⟨h7p, h7h, h7t⟩ := valuePush_run_walkL1 14 (by omega) rfl d6 h6p e
    (by omega)
    (fun p hp1 hp2 => by
      rw [h6t' p, if_neg (by omega)]
      exact hscr p (by omega) (by omega))
  set d7 := TM.runConfig (M := valuePushProgram.toPhased.toTM) d6 e with hd7
  have h7h' : (d7.head : Nat) = aPos + 1 + k := by omega
  have hb7 : d7.tape d7.head = false := by
    rw [h7t, h6t' d7.head, if_neg (by omega)]
    exact hterm d7.head (by omega)
  obtain ⟨h8p, h8h, h8t⟩ := valuePush_step d7 (valuePush_state_eta d7 (by omega) h7p)
    (by rw [hb7]; exact valuePushProgram_t14_zero)
  set d8 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) d7 with hd8
  have h8p' : ((d8.state).fst : Nat) = 15 := h8p
  have h8h' : (d8.head : Nat) = aPos + k := by
    rw [hd8, h8h, Configuration.moveHead_left_val_of_pos d7 (by omega)]
    omega
  have hwf7 : d7.write d7.head false = d7.tape := by
    rw [← hb7]; exact write_self_eq d7
  have h8t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      d8.tape p = if (p : Nat) = aPos + 2 + k + e then true else c.tape p := by
    intro p
    rw [hd8, h8t, hwf7, h7t, h6t' p]
  obtain ⟨h9p, h9h, h9t⟩ := valuePush_run_walkL1 15 (by omega) rfl d8 h8p (k - e - 1)
    (by omega)
    (fun p hp1 hp2 => by
      rw [h8t' p, if_neg (by omega)]
      exact hrest p (by omega) (by omega))
  set d9 := TM.runConfig (M := valuePushProgram.toPhased.toTM) d8 (k - e - 1) with hd9
  have h9h' : (d9.head : Nat) = aPos + 1 + e := by omega
  have hcfg1 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c (e + 1) = d1 := hd1.symm
  have hcfg2 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c (e + 1 + 1) = d2 := by
    rw [TM.runConfig_succ, hcfg1, ← hd2]
  have hcfg3 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c
      (e + 1 + 1 + (k - e - 2)) = d3 := by
    rw [TM.runConfig_add, hcfg2, ← hd3]
  have hcfg4 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c
      (e + 1 + 1 + (k - e - 2) + 1) = d4 := by
    rw [TM.runConfig_succ, hcfg3, ← hd4]
  have hcfg5 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c
      (e + 1 + 1 + (k - e - 2) + 1 + e) = d5 := by
    rw [TM.runConfig_add, hcfg4, ← hd5]
  have hcfg6 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c
      (e + 1 + 1 + (k - e - 2) + 1 + e + 1) = d6 := by
    rw [TM.runConfig_succ, hcfg5, ← hd6]
  have hcfg7 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c
      (e + 1 + 1 + (k - e - 2) + 1 + e + 1 + e) = d7 := by
    rw [TM.runConfig_add, hcfg6, ← hd7]
  have hcfg8 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c
      (e + 1 + 1 + (k - e - 2) + 1 + e + 1 + e + 1) = d8 := by
    rw [TM.runConfig_succ, hcfg7, ← hd8]
  intro s hs
  by_cases hA : s < e + 1
  · obtain ⟨hrp, hrh, _⟩ := valuePush_run_scanR0 11 (by omega) rfl c hphase s
      (by omega)
      (fun p hp1 hp2 => by
        exact hpre p (by omega) (by omega))
    exact ⟨by omega, by omega⟩
  by_cases hB : s = e + 1
  · subst hB
    rw [hcfg1]
    exact ⟨by omega, by omega⟩
  by_cases hC : s < e + 1 + 1 + (k - e - 2)
  · obtain ⟨hrp, hrh, _⟩ := valuePush_run_walkR1 12 (by omega) rfl d2 h2p
      (s - (e + 1 + 1))
      (by omega)
      (fun p hp1 hp2 => by
        rw [h2t']
        exact hrest p (by omega) (by omega))
    rw [show s = (e + 1 + 1) + (s - (e + 1 + 1)) from by omega, TM.runConfig_add, hcfg2]
    exact ⟨by omega, by omega⟩
  by_cases hD : s = e + 1 + 1 + (k - e - 2)
  · subst hD
    rw [hcfg3]
    exact ⟨by omega, by omega⟩
  by_cases hE : s < e + 1 + 1 + (k - e - 2) + 1 + e
  · obtain ⟨hrp, hrh, _⟩ := valuePush_run_walkR1 13 (by omega) rfl d4 h4p
      (s - (e + 1 + 1 + (k - e - 2) + 1))
      (by omega)
      (fun p hp1 hp2 => by
        rw [h4t']
        exact hscr p (by omega) (by omega))
    rw [show s = (e + 1 + 1 + (k - e - 2) + 1)
        + (s - (e + 1 + 1 + (k - e - 2) + 1)) from by omega,
      TM.runConfig_add, hcfg4]
    exact ⟨by omega, by omega⟩
  by_cases hF : s = e + 1 + 1 + (k - e - 2) + 1 + e
  · subst hF
    rw [hcfg5]
    exact ⟨by omega, by omega⟩
  by_cases hG : s < e + 1 + 1 + (k - e - 2) + 1 + e + 1 + e
  · obtain ⟨hrp, hrh, _⟩ := valuePush_run_walkL1 14 (by omega) rfl d6 h6p
      (s - (e + 1 + 1 + (k - e - 2) + 1 + e + 1))
      (by omega)
      (fun p hp1 hp2 => by
        rw [h6t' p, if_neg (by omega)]
        exact hscr p (by omega) (by omega))
    rw [show s = (e + 1 + 1 + (k - e - 2) + 1 + e + 1)
        + (s - (e + 1 + 1 + (k - e - 2) + 1 + e + 1)) from by omega,
      TM.runConfig_add, hcfg6]
    exact ⟨by omega, by omega⟩
  by_cases hH : s = e + 1 + 1 + (k - e - 2) + 1 + e + 1 + e
  · subst hH
    rw [hcfg7]
    exact ⟨by omega, by omega⟩
  -- the φ15 back walk, r := s − (… + 1) ≤ k − e − 1
  · obtain ⟨hrp, hrh, _⟩ := valuePush_run_walkL1 15 (by omega) rfl d8 h8p
      (s - (e + 1 + 1 + (k - e - 2) + 1 + e + 1 + e + 1))
      (by omega)
      (fun p hp1 hp2 => by
        rw [h8t' p, if_neg (by omega)]
        exact hrest p (by omega) (by omega))
    rw [show s = (e + 1 + 1 + (k - e - 2) + 1 + e + 1 + e + 1)
        + (s - (e + 1 + 1 + (k - e - 2) + 1 + e + 1 + e + 1)) from by omega,
      TM.runConfig_add, hcfg8]
    exact ⟨by omega, by omega⟩

set_option maxHeartbeats 400000 in
/-- **Mid-round confinement** (`e + 1 < k`): along the round's `2·(aPos − opBase) + 2·k + 3` steps
the phase never reaches the accept and the head stays ≤ `aPos + 2k + 2` — the per-step safety
stream for the region-embedding transfer, assembled from the two halves at the
`DrainMidCut`. -/
theorem valuePush_drain_mid_confined {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (opBase aPos k e : Nat) (hds : DrainState c opBase aPos k e) (he2 : e + 1 < k) :
    ∀ s : Nat, s < 2 * (aPos - opBase) + 2 * k + 3 →
      (((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).state).fst : Nat) ≠ 34
      ∧ ((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).head : Nat)
          ≤ aPos + 2 * k + 2 := by
  have hgeom := hds.hgeom
  obtain ⟨hcut, hfront⟩ := valuePush_drain_mid_cut c opBase aPos k e hds he2
  intro s hs
  by_cases hA : s < 2 * (aPos - opBase) - e
  · exact hfront s hA
  · have hback := valuePush_drain_mid_back_confined _ opBase aPos k e hcut
      (s - (2 * (aPos - opBase) - e)) (by omega)
    rw [show s = (2 * (aPos - opBase) - e) + (s - (2 * (aPos - opBase) - e)) from by omega,
      TM.runConfig_add]
    exact hback

end ContractExpansion
end Frontier
end Pnp4
