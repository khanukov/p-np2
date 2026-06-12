import Pnp4.Frontier.ContractExpansion.TreeMCSPValuePushRun
import Pnp4.Frontier.ContractExpansion.TreeMCSPValuePushConfined
import Mathlib.Tactic.Ring
import Pnp4.Frontier.ContractExpansion.TreeMCSPValPush
import Mathlib.Tactic.Ring

/-!
# `valuePushProgram` — the final drain round, the restore loop, and the M1 headline

Continuation of `TreeMCSPValuePushRun.lean` (split for elaboration-memory reasons): the final
drain round (`valuePush_drain_final`), the restore-loop state and rounds (the `unaryTransferBody`
clone), the park chain, the two strong inductions, and the M1 headline `valuePush_pushes`.

**Progress classification (AGENTS.md): Infrastructure** — verifier machine component run lemmas;
builds no verifier and proves no separation.  Standard `[propext, Classical.choice, Quot.sound]`
triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram


/-- **The restore-loop state** after `j` restored units: phase φ22 on the anchor (the restore
HOME), the entry complete, the destination block `anchor + 1^j`, the constant-width sliding gap,
and the scratch rest `1^(k-j)` (`unaryTransfer`'s `TransferLayout` with `d = 1`, `γ = k + 1`,
`m = k`). -/
structure CloneState {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (opBase aPos k j : Nat) : Prop where
  hphase : (c.state.fst : Nat) = 22
  hhead : (c.head : Nat) = aPos
  hgeom : opBase + k + 4 ≤ aPos
  hbound : aPos + 2 * k + 3 ≤ valuePushProgram.toPhased.toTM.tapeLength L
  hj : j ≤ k
  hhome : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    (p : Nat) = opBase → c.tape p = false
  hentry : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    opBase + 1 ≤ (p : Nat) → (p : Nat) < opBase + 3 + k → c.tape p = true
  hgapL : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    opBase + 3 + k ≤ (p : Nat) → (p : Nat) < aPos → c.tape p = false
  hdst : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    aPos ≤ (p : Nat) → (p : Nat) < aPos + 1 + j → c.tape p = true
  hgap : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    aPos + 1 + j ≤ (p : Nat) → (p : Nat) < aPos + 2 + j + k → c.tape p = false
  hscr : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    aPos + 2 + j + k ≤ (p : Nat) → (p : Nat) < aPos + 2 + 2 * k → c.tape p = true
  hbeyond : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    aPos + 2 + 2 * k ≤ (p : Nat) → (p : Nat) ≤ aPos + 2 * k + 2 → c.tape p = false

/-- **The final-round cut state**: after the last erase and the `k`-th scratch deposit the head
sits on the zeroed source's right end in φ18; the source zone and terminator are all `0`, the
scratch holds `k` ones, the entry still holds `k + 1` ones. -/
structure DrainFinalCut {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (opBase aPos k : Nat) : Prop where
  hphase : (c.state.fst : Nat) = 18
  hhead : (c.head : Nat) = aPos + k
  hgeom : opBase + k + 4 ≤ aPos
  hbound : aPos + 2 * k + 3 ≤ valuePushProgram.toPhased.toTM.tapeLength L
  hk : 0 < k
  hhome : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    (p : Nat) = opBase → c.tape p = false
  hentry : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    opBase + 1 ≤ (p : Nat) → (p : Nat) < opBase + 2 + k → c.tape p = true
  hgapL : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    opBase + 2 + k ≤ (p : Nat) → (p : Nat) < aPos → c.tape p = false
  hanchor : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    (p : Nat) = aPos → c.tape p = true
  hsrcz : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    aPos < (p : Nat) → (p : Nat) ≤ aPos + 1 + k → c.tape p = false
  hscr : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    aPos + 2 + k ≤ (p : Nat) → (p : Nat) < aPos + 2 + 2 * k → c.tape p = true
  hbeyond : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    aPos + 2 + 2 * k ≤ (p : Nat) → (p : Nat) ≤ aPos + 2 * k + 2 → c.tape p = false

set_option maxHeartbeats 4000000 in
/-- **Final round, first half** (from `DrainState (k-1)`): erase the last unit, deposit the `k`-th
scratch one, walk back onto the source zone — `2·k + 2` steps to the cut state. -/
theorem valuePush_drain_final_A {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (opBase aPos k : Nat) (hds : DrainState c opBase aPos k (k - 1)) (hk : 0 < k) :
    DrainFinalCut
      (TM.runConfig (M := valuePushProgram.toPhased.toTM) c (2 * k + 2))
      opBase aPos k
    ∧ ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
        ((p : Nat) < opBase ∨ aPos + 2 * k + 2 < (p : Nat)) →
        (TM.runConfig (M := valuePushProgram.toPhased.toTM) c (2 * k + 2)).tape p = c.tape p := by
  obtain ⟨hphase, hhead, hgeom, hbound, _, hhome, hentry, hgapL, hanchor, hpre, hrest,
    hterm, hscr, hzr⟩ := hds
  have hhead' : (c.head : Nat) = aPos + k := by omega
  -- φ5 erase the last unit (aPos+k), step right onto the terminator
  obtain ⟨h1p, h1h, h1t⟩ := valuePush_step c (valuePush_state_eta c (by omega) hphase)
    (valuePushProgram_t5 (c.tape c.head))
  set c1 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c with hc1
  have h1h' : (c1.head : Nat) = aPos + 1 + k := by
    rw [hc1, h1h]
    simp only [Configuration.moveHead, dif_pos (show (c.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have h1t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c1.tape p = if (p : Nat) = aPos + k then false else c.tape p := by
    intro p
    rw [hc1, h1t]
    exact valuePush_write_char c false hhead' p
  -- φ6 probe: the terminator — the final route; step right onto the scratch base
  have hb1 : c1.tape c1.head = false := by
    rw [h1t' c1.head, if_neg (by omega)]
    exact hterm c1.head (by omega)
  obtain ⟨h2p, h2h, h2t⟩ := valuePush_step c1 (valuePush_state_eta c1 (by omega) h1p)
    (by rw [hb1]; exact valuePushProgram_t6_zero)
  set c2 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c1 with hc2
  have h2h' : (c2.head : Nat) = aPos + 2 + k := by
    rw [hc2, h2h]
    simp only [Configuration.moveHead, dif_pos (show (c1.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have hwf1 : c1.write c1.head false = c1.tape := by
    rw [← hb1]; exact write_self_eq c1
  have h2t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c2.tape p = if (p : Nat) = aPos + k then false else c.tape p := by
    intro p
    rw [hc2, h2t, hwf1, h1t' p]
  -- φ16 walk the k−1 scratch ones, write the k-th at the frontier, turn left
  obtain ⟨h3p, h3h, h3t⟩ := valuePush_run_walkR1 16 (by omega) rfl c2 h2p (k - 1)
    (by omega)
    (fun p hp1 hp2 => by
      rw [h2t' p, if_neg (by omega)]
      exact hscr p (by omega) (by omega))
  set c3 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c2 (k - 1) with hc3
  have h3h' : (c3.head : Nat) = aPos + 1 + 2 * k := by omega
  have hb3 : c3.tape c3.head = false := by
    rw [h3t, h2t' c3.head, if_neg (by omega)]
    exact hzr c3.head (by omega) (by omega)
  obtain ⟨h4p, h4h, h4t⟩ := valuePush_step c3 (valuePush_state_eta c3 (by omega) h3p)
    (by rw [hb3]; exact valuePushProgram_t16_zero)
  set c4 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c3 with hc4
  have h4h' : (c4.head : Nat) = aPos + 2 * k := by
    rw [hc4, h4h, Configuration.moveHead_left_val_of_pos c3 (by omega)]
    omega
  have h4t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c4.tape p = if (p : Nat) = aPos + 1 + 2 * k then true
        else if (p : Nat) = aPos + k then false else c.tape p := by
    intro p
    rw [hc4, h4t, valuePush_write_char c3 true h3h' p, h3t, h2t' p]
  -- φ17 walk the scratch back left onto the terminator, step left onto the source zone
  obtain ⟨h5p, h5h, h5t⟩ := valuePush_run_walkL1 17 (by omega) rfl c4 h4p (k - 1)
    (by omega)
    (fun p hp1 hp2 => by
      rw [h4t' p, if_neg (by omega), if_neg (by omega)]
      exact hscr p (by omega) (by omega))
  set c5 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c4 (k - 1) with hc5
  have h5h' : (c5.head : Nat) = aPos + 1 + k := by omega
  have hb5 : c5.tape c5.head = false := by
    rw [h5t, h4t' c5.head, if_neg (by omega), if_neg (by omega)]
    exact hterm c5.head (by omega)
  obtain ⟨h6p, h6h, h6t⟩ := valuePush_step c5 (valuePush_state_eta c5 (by omega) h5p)
    (by rw [hb5]; exact valuePushProgram_t17_zero)
  set c6 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c5 with hc6
  have h6h' : (c6.head : Nat) = aPos + k := by
    rw [hc6, h6h, Configuration.moveHead_left_val_of_pos c5 (by omega)]
    omega
  have hwf5 : c5.write c5.head false = c5.tape := by
    rw [← hb5]; exact write_self_eq c5
  have h6t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c6.tape p = if (p : Nat) = aPos + 1 + 2 * k then true
        else if (p : Nat) = aPos + k then false else c.tape p := by
    intro p
    rw [hc6, h6t, hwf5, h5t, h4t' p]
  have htotal : TM.runConfig (M := valuePushProgram.toPhased.toTM) c (2 * k + 2) = c6 := by
    have et : 2 * k + 2
        = 1 + (1 + ((k - 1) + (1 + ((k - 1) + 1)))) := by
      omega
    rw [et, TM.runConfig_add, valuePush_runConfig_one, ← hc1,
      TM.runConfig_add, valuePush_runConfig_one, ← hc2,
      TM.runConfig_add, ← hc3,
      TM.runConfig_add, valuePush_runConfig_one, ← hc4,
      TM.runConfig_add, ← hc5,
      valuePush_runConfig_one, ← hc6]
  have g1 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = opBase → c6.tape p = false := by
    intro p hp
    rw [h6t' p, if_neg (by omega), if_neg (by omega)]
    exact hhome p hp
  have g2 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      opBase + 1 ≤ (p : Nat) → (p : Nat) < opBase + 2 + k → c6.tape p = true := by
    intro p hp1 hp2
    rw [h6t' p, if_neg (by omega), if_neg (by omega)]
    exact hentry p (by omega) (by omega)
  have g3 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      opBase + 2 + k ≤ (p : Nat) → (p : Nat) < aPos → c6.tape p = false := by
    intro p hp1 hp2
    rw [h6t' p, if_neg (by omega), if_neg (by omega)]
    exact hgapL p (by omega) (by omega)
  have g4 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = aPos → c6.tape p = true := by
    intro p hp
    rw [h6t' p, if_neg (by omega), if_neg (by omega)]
    exact hanchor p hp
  have g5 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      aPos < (p : Nat) → (p : Nat) ≤ aPos + 1 + k → c6.tape p = false := by
    intro p hp1 hp2
    rw [h6t' p, if_neg (by omega)]
    by_cases hq : (p : Nat) = aPos + k
    · rw [if_pos hq]
    · rw [if_neg hq]
      by_cases hq2 : (p : Nat) = aPos + 1 + k
      · exact hterm p hq2
      · exact hpre p (by omega) (by omega)
  have g6 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      aPos + 2 + k ≤ (p : Nat) → (p : Nat) < aPos + 2 + 2 * k → c6.tape p = true := by
    intro p hp1 hp2
    rw [h6t' p]
    by_cases hq : (p : Nat) = aPos + 1 + 2 * k
    · rw [if_pos hq]
    · rw [if_neg hq, if_neg (by omega)]
      exact hscr p (by omega) (by omega)
  have g7 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      aPos + 2 + 2 * k ≤ (p : Nat) → (p : Nat) ≤ aPos + 2 * k + 2 → c6.tape p = false := by
    intro p hp1 hp2
    rw [h6t' p, if_neg (by omega), if_neg (by omega)]
    exact hzr p (by omega) (by omega)
  have hcut : DrainFinalCut c6 opBase aPos k :=
    ⟨h6p, h6h', hgeom, hbound, hk, g1, g2, g3, g4, g5, g6, g7⟩
  have hOut : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      ((p : Nat) < opBase ∨ aPos + 2 * k + 2 < (p : Nat)) → c6.tape p = c.tape p := by
    intro p hp
    rw [h6t' p, if_neg (by omega), if_neg (by omega)]
  rw [htotal]
  exact ⟨hcut, hOut⟩

set_option maxHeartbeats 4000000 in
/-- **Final round, second half** (from the cut): cross the anchor, deposit the `k`-th entry one,
return onto the anchor in the restore phase — `2·(aPos − opBase) − k − 1` steps. -/
theorem valuePush_drain_final_B {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (opBase aPos k : Nat) (hcut : DrainFinalCut c opBase aPos k) :
    CloneState
      (TM.runConfig (M := valuePushProgram.toPhased.toTM) c
        (2 * (aPos - opBase) - k - 1))
      opBase aPos k 0
    ∧ ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
        ((p : Nat) < opBase ∨ aPos + 2 * k + 2 < (p : Nat)) →
        (TM.runConfig (M := valuePushProgram.toPhased.toTM) c
          (2 * (aPos - opBase) - k - 1)).tape p = c.tape p := by
  obtain ⟨hphase, hhead, hgeom, hbound, hk, hhome, hentry, hgapL, hanchor, hsrcz,
    hscr, hbeyond⟩ := hcut
  -- φ18 scan the zeroed source left onto the anchor, hop over it
  obtain ⟨h7p, h7h, h7t⟩ := valuePush_run_scanL0 18 (by omega) rfl c hphase k
    (by omega)
    (fun p hp1 hp2 => by
      exact hsrcz p (by omega) (by omega))
  set c7 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c k with hc7
  have h7h' : (c7.head : Nat) = aPos := by omega
  have hb7 : c7.tape c7.head = true := by
    rw [h7t]
    exact hanchor c7.head (by omega)
  obtain ⟨h8p, h8h, h8t⟩ := valuePush_step c7 (valuePush_state_eta c7 (by omega) h7p)
    (by rw [hb7]; exact valuePushProgram_t18_one)
  set c8 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c7 with hc8
  have h8h' : (c8.head : Nat) = aPos - 1 := by
    rw [hc8, h8h, Configuration.moveHead_left_val_of_pos c7 (by omega)]
    omega
  have hwf7 : c7.write c7.head true = c7.tape := by
    rw [← hb7]; exact write_self_eq c7
  have h8t' : c8.tape = c.tape := by
    rw [hc8, h8t, hwf7, h7t]
  -- φ19 scan gap₁ left onto the entry's rightmost one, turn right onto the frontier
  obtain ⟨h9p, h9h, h9t⟩ := valuePush_run_scanL0 19 (by omega) rfl c8 h8p
    (aPos - opBase - k - 2)
    (by omega)
    (fun p hp1 hp2 => by
      rw [h8t']
      exact hgapL p (by omega) (by omega))
  set c9 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c8 (aPos - opBase - k - 2)
    with hc9
  have h9h' : (c9.head : Nat) = opBase + 1 + k := by omega
  have hb9 : c9.tape c9.head = true := by
    rw [h9t, h8t']
    exact hentry c9.head (by omega) (by omega)
  obtain ⟨h10p, h10h, h10t⟩ := valuePush_step c9 (valuePush_state_eta c9 (by omega) h9p)
    (by rw [hb9]; exact valuePushProgram_t19_one)
  set c10 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c9 with hc10
  have h10h' : (c10.head : Nat) = opBase + 2 + k := by
    rw [hc10, h10h]
    simp only [Configuration.moveHead, dif_pos (show (c9.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have hwf9 : c9.write c9.head true = c9.tape := by
    rw [← hb9]; exact write_self_eq c9
  have h10t' : c10.tape = c.tape := by
    rw [hc10, h10t, hwf9, h9t, h8t']
  -- φ20 write the k-th entry one (the entry is complete), head right
  obtain ⟨h11p, h11h, h11t⟩ := valuePush_step c10 (valuePush_state_eta c10 (by omega) h10p)
    (valuePushProgram_t20 (c10.tape c10.head))
  set c11 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c10 with hc11
  have h11h' : (c11.head : Nat) = opBase + 3 + k := by
    rw [hc11, h11h]
    simp only [Configuration.moveHead, dif_pos (show (c10.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have h11t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c11.tape p = if (p : Nat) = opBase + 2 + k then true else c.tape p := by
    intro p
    rw [hc11, h11t, valuePush_write_char c10 true h10h' p, h10t']
  -- φ21 scan gap₁ right onto the anchor — the restore HOME
  obtain ⟨h12p, h12h, h12t⟩ := valuePush_run_scanR0 21 (by omega) rfl c11 h11p
    (aPos - opBase - k - 3)
    (by omega)
    (fun p hp1 hp2 => by
      rw [h11t' p, if_neg (by omega)]
      exact hgapL p (by omega) (by omega))
  set c12 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c11 (aPos - opBase - k - 3)
    with hc12
  have h12h' : (c12.head : Nat) = aPos := by omega
  have hb12 : c12.tape c12.head = true := by
    rw [h12t, h11t' c12.head, if_neg (by omega)]
    exact hanchor c12.head (by omega)
  obtain ⟨h13p, h13h, h13t⟩ := valuePush_step c12 (valuePush_state_eta c12 (by omega) h12p)
    (by rw [hb12]; exact valuePushProgram_t21_one)
  set c13 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c12 with hc13
  have h13h' : (c13.head : Nat) = aPos := by
    rw [hc13, h13h, Configuration.moveHead_stay]
    exact h12h'
  have hwf12 : c12.write c12.head true = c12.tape := by
    rw [← hb12]; exact write_self_eq c12
  have h13t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c13.tape p = if (p : Nat) = opBase + 2 + k then true else c.tape p := by
    intro p
    rw [hc13, h13t, hwf12, h12t, h11t' p]
  have htotal : TM.runConfig (M := valuePushProgram.toPhased.toTM) c
      (2 * (aPos - opBase) - k - 1) = c13 := by
    have et : 2 * (aPos - opBase) - k - 1
        = k + (1 + ((aPos - opBase - k - 2)
          + (1 + (1 + ((aPos - opBase - k - 3) + 1))))) := by
      omega
    rw [et, TM.runConfig_add, ← hc7,
      TM.runConfig_add, valuePush_runConfig_one, ← hc8,
      TM.runConfig_add, ← hc9,
      TM.runConfig_add, valuePush_runConfig_one, ← hc10,
      TM.runConfig_add, valuePush_runConfig_one, ← hc11,
      TM.runConfig_add, ← hc12,
      valuePush_runConfig_one, ← hc13]
  have g1 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = opBase → c13.tape p = false := by
    intro p hp
    rw [h13t' p, if_neg (by omega)]
    exact hhome p hp
  have g2 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      opBase + 1 ≤ (p : Nat) → (p : Nat) < opBase + 3 + k → c13.tape p = true := by
    intro p hp1 hp2
    rw [h13t' p]
    by_cases hq : (p : Nat) = opBase + 2 + k
    · rw [if_pos hq]
    · rw [if_neg hq]
      exact hentry p (by omega) (by omega)
  have g3 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      opBase + 3 + k ≤ (p : Nat) → (p : Nat) < aPos → c13.tape p = false := by
    intro p hp1 hp2
    rw [h13t' p, if_neg (by omega)]
    exact hgapL p (by omega) (by omega)
  have g4 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      aPos ≤ (p : Nat) → (p : Nat) < aPos + 1 + 0 → c13.tape p = true := by
    intro p hp1 hp2
    rw [h13t' p, if_neg (by omega)]
    exact hanchor p (by omega)
  have g5 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      aPos + 1 + 0 ≤ (p : Nat) → (p : Nat) < aPos + 2 + 0 + k → c13.tape p = false := by
    intro p hp1 hp2
    rw [h13t' p, if_neg (by omega)]
    exact hsrcz p (by omega) (by omega)
  have g6 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      aPos + 2 + 0 + k ≤ (p : Nat) → (p : Nat) < aPos + 2 + 2 * k → c13.tape p = true := by
    intro p hp1 hp2
    rw [h13t' p, if_neg (by omega)]
    exact hscr p (by omega) (by omega)
  have g7 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      aPos + 2 + 2 * k ≤ (p : Nat) → (p : Nat) ≤ aPos + 2 * k + 2 → c13.tape p = false := by
    intro p hp1 hp2
    rw [h13t' p, if_neg (by omega)]
    exact hbeyond p (by omega) (by omega)
  have hCS : CloneState c13 opBase aPos k 0 :=
    ⟨h13p, h13h', hgeom, hbound, by omega, g1, g2, g3, g4, g5, g6, g7⟩
  have hOut : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      ((p : Nat) < opBase ∨ aPos + 2 * k + 2 < (p : Nat)) → c13.tape p = c.tape p := by
    intro p hp
    rw [h13t' p, if_neg (by omega)]
  rw [htotal]
  exact ⟨hCS, hOut⟩

/-- **The final drain round** (from `DrainState (k-1)`): the two halves combined — exactly
`2·(aPos − opBase) + k + 1` steps to the restore HOME. -/
theorem valuePush_drain_final {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (opBase aPos k : Nat) (hds : DrainState c opBase aPos k (k - 1)) (hk : 0 < k) :
    CloneState
      (TM.runConfig (M := valuePushProgram.toPhased.toTM) c
        (2 * (aPos - opBase) + k + 1))
      opBase aPos k 0
    ∧ ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
        ((p : Nat) < opBase ∨ aPos + 2 * k + 2 < (p : Nat)) →
        (TM.runConfig (M := valuePushProgram.toPhased.toTM) c
          (2 * (aPos - opBase) + k + 1)).tape p = c.tape p := by
  have hgeom := hds.hgeom
  obtain ⟨hcut, hOutA⟩ := valuePush_drain_final_A c opBase aPos k hds hk
  obtain ⟨hCS, hOutB⟩ := valuePush_drain_final_B _ opBase aPos k hcut
  have hsum : 2 * (aPos - opBase) + k + 1
      = (2 * k + 2) + (2 * (aPos - opBase) - k - 1) := by
    omega
  rw [hsum, TM.runConfig_add]
  refine ⟨hCS, ?_⟩
  intro p hp
  rw [hOutB p hp]
  exact hOutA p hp

end ContractExpansion
end Frontier
end Pnp4

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

set_option maxHeartbeats 4000000 in
/-- **One mid restore round** (`j + 1 < k`): append a restored unit at the destination frontier,
erase the scratch's leftmost one, return to the anchor — `CloneState j` steps to
`CloneState (j+1)` in exactly `2·j + 2·k + 12` steps, with the tape touched only inside the zone. -/
theorem valuePush_clone_mid {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (opBase aPos k j : Nat) (hcs : CloneState c opBase aPos k j) (hj2 : j + 1 < k) :
    CloneState
      (TM.runConfig (M := valuePushProgram.toPhased.toTM) c (2 * j + 2 * k + 12))
      opBase aPos k (j + 1)
    ∧ ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
        ((p : Nat) < opBase ∨ aPos + 2 * k + 2 < (p : Nat)) →
        (TM.runConfig (M := valuePushProgram.toPhased.toTM) c
          (2 * j + 2 * k + 12)).tape p = c.tape p := by
  obtain ⟨hphase, hhead, hgeom, hbound, _, hhome, hentry, hgapL, hdst, hgap, hscr,
    hbeyond⟩ := hcs
  -- φ22 walk the destination ones (anchor + j restored) onto the frontier, write, move on
  obtain ⟨h1p, h1h, h1t⟩ := valuePush_run_walkR1 22 (by omega) rfl c hphase (1 + j)
    (by omega)
    (fun p hp1 hp2 => by
      exact hdst p (by omega) (by omega))
  set c1 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c (1 + j) with hc1
  have h1h' : (c1.head : Nat) = aPos + 1 + j := by omega
  have hb1 : c1.tape c1.head = false := by
    rw [h1t]
    exact hgap c1.head (by omega) (by omega)
  obtain ⟨h2p, h2h, h2t⟩ := valuePush_step c1 (valuePush_state_eta c1 (by omega) h1p)
    (by rw [hb1]; exact valuePushProgram_t22_zero)
  set c2 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c1 with hc2
  have h2h' : (c2.head : Nat) = aPos + 2 + j := by
    rw [hc2, h2h]
    simp only [Configuration.moveHead, dif_pos (show (c1.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have h2t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c2.tape p = if (p : Nat) = aPos + 1 + j then true else c.tape p := by
    intro p
    rw [hc2, h2t, valuePush_write_char c1 true h1h' p, h1t]
  -- φ23 scan the sliding gap right onto the scratch's head
  obtain ⟨h3p, h3h, h3t⟩ := valuePush_run_scanR0 23 (by omega) rfl c2 h2p k
    (by omega)
    (fun p hp1 hp2 => by
      rw [h2t' p, if_neg (by omega)]
      exact hgap p (by omega) (by omega))
  set c3 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c2 k with hc3
  have h3h' : (c3.head : Nat) = aPos + 2 + j + k := by omega
  have hb3 : c3.tape c3.head = true := by
    rw [h3t, h2t' c3.head, if_neg (by omega)]
    exact hscr c3.head (by omega) (by omega)
  obtain ⟨h4p, h4h, h4t⟩ := valuePush_step c3 (valuePush_state_eta c3 (by omega) h3p)
    (by rw [hb3]; exact valuePushProgram_t23_one)
  set c4 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c3 with hc4
  have h4h' : (c4.head : Nat) = aPos + 2 + j + k := by
    rw [hc4, h4h, Configuration.moveHead_stay]
    exact h3h'
  have hwf3 : c3.write c3.head true = c3.tape := by
    rw [← hb3]; exact write_self_eq c3
  have h4t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c4.tape p = if (p : Nat) = aPos + 1 + j then true else c.tape p := by
    intro p
    rw [hc4, h4t, hwf3, h3t, h2t' p]
  -- φ24 erase the scratch unit, step right to peek
  obtain ⟨h5p, h5h, h5t⟩ := valuePush_step c4 (valuePush_state_eta c4 (by omega) h4p)
    (valuePushProgram_t24 (c4.tape c4.head))
  set c5 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c4 with hc5
  have h5h' : (c5.head : Nat) = aPos + 3 + j + k := by
    rw [hc5, h5h]
    simp only [Configuration.moveHead, dif_pos (show (c4.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have h5t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c5.tape p = if (p : Nat) = aPos + 2 + j + k then false
        else if (p : Nat) = aPos + 1 + j then true else c.tape p := by
    intro p
    rw [hc5, h5t, valuePush_write_char c4 false h4h' p, h4t' p]
  -- φ25 peek: more scratch units remain — return leftward
  have hb5 : c5.tape c5.head = true := by
    rw [h5t' c5.head, if_neg (by omega), if_neg (by omega)]
    exact hscr c5.head (by omega) (by omega)
  obtain ⟨h6p, h6h, h6t⟩ := valuePush_step c5 (valuePush_state_eta c5 (by omega) h5p)
    (by rw [hb5]; exact valuePushProgram_t25_one)
  set c6 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c5 with hc6
  have h6h' : (c6.head : Nat) = aPos + 2 + j + k := by
    rw [hc6, h6h, Configuration.moveHead_left_val_of_pos c5 (by omega)]
    omega
  have hwf5 : c5.write c5.head true = c5.tape := by
    rw [← hb5]; exact write_self_eq c5
  have h6t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c6.tape p = if (p : Nat) = aPos + 2 + j + k then false
        else if (p : Nat) = aPos + 1 + j then true else c.tape p := by
    intro p
    rw [hc6, h6t, hwf5, h5t' p]
  -- φ26 scan the slid gap left onto the destination's right end
  obtain ⟨h7p, h7h, h7t⟩ := valuePush_run_scanL0 26 (by omega) rfl c6 h6p (k + 1)
    (by omega)
    (fun p hp1 hp2 => by
      rw [h6t' p]
      by_cases hq : (p : Nat) = aPos + 2 + j + k
      · rw [if_pos hq]
      · rw [if_neg hq, if_neg (by omega)]
        exact hgap p (by omega) (by omega))
  set c7 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c6 (k + 1) with hc7
  have h7h' : (c7.head : Nat) = aPos + 1 + j := by omega
  have hb7 : c7.tape c7.head = true := by
    rw [h7t, h6t' c7.head, if_neg (by omega)]
    rw [if_pos (show ((c7.head : Fin (valuePushProgram.toPhased.toTM.tapeLength L)) : Nat)
      = aPos + 1 + j by omega)]
  obtain ⟨h8p, h8h, h8t⟩ := valuePush_step c7 (valuePush_state_eta c7 (by omega) h7p)
    (by rw [hb7]; exact valuePushProgram_t26_one)
  set c8 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c7 with hc8
  have h8h' : (c8.head : Nat) = aPos + 1 + j := by
    rw [hc8, h8h, Configuration.moveHead_stay]
    exact h7h'
  have hwf7 : c7.write c7.head true = c7.tape := by
    rw [← hb7]; exact write_self_eq c7
  have h8t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c8.tape p = if (p : Nat) = aPos + 2 + j + k then false
        else if (p : Nat) = aPos + 1 + j then true else c.tape p := by
    intro p
    rw [hc8, h8t, hwf7, h7t, h6t' p]
  -- φ27 walk the destination block left; the 0 left of the anchor delimits
  obtain ⟨h9p, h9h, h9t⟩ := valuePush_run_walkL1 27 (by omega) rfl c8 h8p (j + 2)
    (by omega)
    (fun p hp1 hp2 => by
      rw [h8t' p, if_neg (by omega)]
      by_cases hq : (p : Nat) = aPos + 1 + j
      · rw [if_pos hq]
      · rw [if_neg hq]
        exact hdst p (by omega) (by omega))
  set c9 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c8 (j + 2) with hc9
  have h9h' : (c9.head : Nat) = aPos - 1 := by omega
  have hb9 : c9.tape c9.head = false := by
    rw [h9t, h8t' c9.head, if_neg (by omega), if_neg (by omega)]
    exact hgapL c9.head (by omega) (by omega)
  obtain ⟨h10p, h10h, h10t⟩ := valuePush_step c9 (valuePush_state_eta c9 (by omega) h9p)
    (by rw [hb9]; exact valuePushProgram_t27_zero)
  set c10 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c9 with hc10
  have h10h' : (c10.head : Nat) = aPos - 1 := by
    rw [hc10, h10h, Configuration.moveHead_stay]
    exact h9h'
  have hwf9 : c9.write c9.head false = c9.tape := by
    rw [← hb9]; exact write_self_eq c9
  have h10t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c10.tape p = if (p : Nat) = aPos + 2 + j + k then false
        else if (p : Nat) = aPos + 1 + j then true else c.tape p := by
    intro p
    rw [hc10, h10t, hwf9, h9t, h8t' p]
  -- φ28 re-home one step right onto the anchor; φ29 back-edge into φ22
  obtain ⟨h11p, h11h, h11t⟩ := valuePush_step c10 (valuePush_state_eta c10 (by omega) h10p)
    (valuePushProgram_t28 (c10.tape c10.head))
  set c11 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c10 with hc11
  have h11h' : (c11.head : Nat) = aPos := by
    rw [hc11, h11h]
    simp only [Configuration.moveHead, dif_pos (show (c10.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have h11t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c11.tape p = if (p : Nat) = aPos + 2 + j + k then false
        else if (p : Nat) = aPos + 1 + j then true else c.tape p := by
    intro p
    rw [hc11, h11t, write_self_eq, h10t' p]
  obtain ⟨h12p, h12h, h12t⟩ := valuePush_step c11 (valuePush_state_eta c11 (by omega) h11p)
    (valuePushProgram_t29 (c11.tape c11.head))
  set c12 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c11 with hc12
  have h12h' : (c12.head : Nat) = aPos := by
    rw [hc12, h12h, Configuration.moveHead_stay]
    exact h11h'
  have h12t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c12.tape p = if (p : Nat) = aPos + 2 + j + k then false
        else if (p : Nat) = aPos + 1 + j then true else c.tape p := by
    intro p
    rw [hc12, h12t, write_self_eq, h11t' p]
  have htotal : TM.runConfig (M := valuePushProgram.toPhased.toTM) c
      (2 * j + 2 * k + 12) = c12 := by
    have et : 2 * j + 2 * k + 12
        = (1 + j) + (1 + (k + (1 + (1 + (1 + ((k + 1) + (1 + ((j + 2)
          + (1 + (1 + 1)))))))))) := by
      omega
    rw [et, TM.runConfig_add, ← hc1,
      TM.runConfig_add, valuePush_runConfig_one, ← hc2,
      TM.runConfig_add, ← hc3,
      TM.runConfig_add, valuePush_runConfig_one, ← hc4,
      TM.runConfig_add, valuePush_runConfig_one, ← hc5,
      TM.runConfig_add, valuePush_runConfig_one, ← hc6,
      TM.runConfig_add, ← hc7,
      TM.runConfig_add, valuePush_runConfig_one, ← hc8,
      TM.runConfig_add, ← hc9,
      TM.runConfig_add, valuePush_runConfig_one, ← hc10,
      TM.runConfig_succ, valuePush_runConfig_one, ← hc11, ← hc12]
  have h12head : (c12.head : Nat) = aPos := h12h'
  have g1 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = opBase → c12.tape p = false := by
    intro p hp
    rw [h12t' p, if_neg (by omega), if_neg (by omega)]
    exact hhome p hp
  have g2 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      opBase + 1 ≤ (p : Nat) → (p : Nat) < opBase + 3 + k → c12.tape p = true := by
    intro p hp1 hp2
    rw [h12t' p, if_neg (by omega), if_neg (by omega)]
    exact hentry p (by omega) (by omega)
  have g3 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      opBase + 3 + k ≤ (p : Nat) → (p : Nat) < aPos → c12.tape p = false := by
    intro p hp1 hp2
    rw [h12t' p, if_neg (by omega), if_neg (by omega)]
    exact hgapL p (by omega) (by omega)
  have g4 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      aPos ≤ (p : Nat) → (p : Nat) < aPos + 1 + (j + 1) → c12.tape p = true := by
    intro p hp1 hp2
    rw [h12t' p, if_neg (by omega)]
    by_cases hq : (p : Nat) = aPos + 1 + j
    · rw [if_pos hq]
    · rw [if_neg hq]
      exact hdst p (by omega) (by omega)
  have g5 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      aPos + 1 + (j + 1) ≤ (p : Nat) → (p : Nat) < aPos + 2 + (j + 1) + k →
      c12.tape p = false := by
    intro p hp1 hp2
    rw [h12t' p]
    by_cases hq : (p : Nat) = aPos + 2 + j + k
    · rw [if_pos hq]
    · rw [if_neg hq, if_neg (by omega)]
      exact hgap p (by omega) (by omega)
  have g6 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      aPos + 2 + (j + 1) + k ≤ (p : Nat) → (p : Nat) < aPos + 2 + 2 * k →
      c12.tape p = true := by
    intro p hp1 hp2
    rw [h12t' p, if_neg (by omega), if_neg (by omega)]
    exact hscr p (by omega) (by omega)
  have g7 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      aPos + 2 + 2 * k ≤ (p : Nat) → (p : Nat) ≤ aPos + 2 * k + 2 → c12.tape p = false := by
    intro p hp1 hp2
    rw [h12t' p, if_neg (by omega), if_neg (by omega)]
    exact hbeyond p (by omega) (by omega)
  have hCS : CloneState c12 opBase aPos k (j + 1) :=
    ⟨h12p, h12head, hgeom, hbound, by omega, g1, g2, g3, g4, g5, g6, g7⟩
  have hOut : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      ((p : Nat) < opBase ∨ aPos + 2 * k + 2 < (p : Nat)) → c12.tape p = c.tape p := by
    intro p hp
    rw [h12t' p, if_neg (by omega), if_neg (by omega)]
  rw [htotal]
  exact ⟨hCS, hOut⟩

end ContractExpansion
end Frontier
end Pnp4

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **The park-entry state**: phase φ30 right of the restored block, with the zone fully
restored — the entry complete, the block `anchor + 1^k` back in place, zeros elsewhere. -/
structure ParkReady {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (opBase aPos k p0 : Nat) : Prop where
  hphase : (c.state.fst : Nat) = 30
  hhead : (c.head : Nat) = p0
  hp0l : aPos + k < p0
  hp0r : p0 ≤ aPos + 2 * k + 2
  hgeom : opBase + k + 4 ≤ aPos
  hbound : aPos + 2 * k + 3 ≤ valuePushProgram.toPhased.toTM.tapeLength L
  hhome : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    (p : Nat) = opBase → c.tape p = false
  hentry : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    opBase + 1 ≤ (p : Nat) → (p : Nat) < opBase + 3 + k → c.tape p = true
  hgapL : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    opBase + 3 + k ≤ (p : Nat) → (p : Nat) < aPos → c.tape p = false
  hblk : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    aPos ≤ (p : Nat) → (p : Nat) < aPos + 1 + k → c.tape p = true
  hz : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    aPos + k < (p : Nat) → (p : Nat) ≤ aPos + 2 * k + 2 → c.tape p = false

set_option maxHeartbeats 4000000 in
/-- **The last restore round** (`j = k - 1`): append the final restored unit, erase the last
scratch one, and exit to the park chain — `2·k + 4` steps. -/
theorem valuePush_clone_last {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (opBase aPos k : Nat) (hcs : CloneState c opBase aPos k (k - 1)) (hk : 0 < k) :
    ParkReady
      (TM.runConfig (M := valuePushProgram.toPhased.toTM) c (2 * k + 4))
      opBase aPos k (aPos + 2 * k + 1)
    ∧ ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
        ((p : Nat) < opBase ∨ aPos + 2 * k + 2 < (p : Nat)) →
        (TM.runConfig (M := valuePushProgram.toPhased.toTM) c
          (2 * k + 4)).tape p = c.tape p := by
  obtain ⟨hphase, hhead, hgeom, hbound, _, hhome, hentry, hgapL, hdst, hgap, hscr,
    hbeyond⟩ := hcs
  -- φ22 walk the destination (anchor + (k−1) restored) onto the frontier, write the k-th unit
  obtain ⟨h1p, h1h, h1t⟩ := valuePush_run_walkR1 22 (by omega) rfl c hphase k
    (by omega)
    (fun p hp1 hp2 => by
      exact hdst p (by omega) (by omega))
  set c1 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c k with hc1
  have h1h' : (c1.head : Nat) = aPos + k := by omega
  have hb1 : c1.tape c1.head = false := by
    rw [h1t]
    exact hgap c1.head (by omega) (by omega)
  obtain ⟨h2p, h2h, h2t⟩ := valuePush_step c1 (valuePush_state_eta c1 (by omega) h1p)
    (by rw [hb1]; exact valuePushProgram_t22_zero)
  set c2 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c1 with hc2
  have h2h' : (c2.head : Nat) = aPos + 1 + k := by
    rw [hc2, h2h]
    simp only [Configuration.moveHead, dif_pos (show (c1.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have h2t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c2.tape p = if (p : Nat) = aPos + k then true else c.tape p := by
    intro p
    rw [hc2, h2t, valuePush_write_char c1 true h1h' p, h1t]
  -- φ23 scan the sliding gap right onto the scratch's last unit
  obtain ⟨h3p, h3h, h3t⟩ := valuePush_run_scanR0 23 (by omega) rfl c2 h2p k
    (by omega)
    (fun p hp1 hp2 => by
      rw [h2t' p, if_neg (by omega)]
      exact hgap p (by omega) (by omega))
  set c3 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c2 k with hc3
  have h3h' : (c3.head : Nat) = aPos + 2 * k + 1 := by omega
  have hb3 : c3.tape c3.head = true := by
    rw [h3t, h2t' c3.head, if_neg (by omega)]
    exact hscr c3.head (by omega) (by omega)
  obtain ⟨h4p, h4h, h4t⟩ := valuePush_step c3 (valuePush_state_eta c3 (by omega) h3p)
    (by rw [hb3]; exact valuePushProgram_t23_one)
  set c4 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c3 with hc4
  have h4h' : (c4.head : Nat) = aPos + 2 * k + 1 := by
    rw [hc4, h4h, Configuration.moveHead_stay]
    exact h3h'
  have hwf3 : c3.write c3.head true = c3.tape := by
    rw [← hb3]; exact write_self_eq c3
  have h4t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c4.tape p = if (p : Nat) = aPos + k then true else c.tape p := by
    intro p
    rw [hc4, h4t, hwf3, h3t, h2t' p]
  -- φ24 erase the last scratch unit, step right; φ25 peeks the empty zone — park
  obtain ⟨h5p, h5h, h5t⟩ := valuePush_step c4 (valuePush_state_eta c4 (by omega) h4p)
    (valuePushProgram_t24 (c4.tape c4.head))
  set c5 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c4 with hc5
  have h5h' : (c5.head : Nat) = aPos + 2 * k + 2 := by
    rw [hc5, h5h]
    simp only [Configuration.moveHead, dif_pos (show (c4.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have h5t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c5.tape p = if (p : Nat) = aPos + 2 * k + 1 then false
        else if (p : Nat) = aPos + k then true else c.tape p := by
    intro p
    rw [hc5, h5t, valuePush_write_char c4 false h4h' p, h4t' p]
  have hb5 : c5.tape c5.head = false := by
    rw [h5t' c5.head, if_neg (by omega), if_neg (by omega)]
    exact hbeyond c5.head (by omega) (by omega)
  obtain ⟨h6p, h6h, h6t⟩ := valuePush_step c5 (valuePush_state_eta c5 (by omega) h5p)
    (by rw [hb5]; exact valuePushProgram_t25_zero)
  set c6 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c5 with hc6
  have h6h' : (c6.head : Nat) = aPos + 2 * k + 1 := by
    rw [hc6, h6h, Configuration.moveHead_left_val_of_pos c5 (by omega)]
    omega
  have hwf5 : c5.write c5.head false = c5.tape := by
    rw [← hb5]; exact write_self_eq c5
  have h6t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c6.tape p = if (p : Nat) = aPos + 2 * k + 1 then false
        else if (p : Nat) = aPos + k then true else c.tape p := by
    intro p
    rw [hc6, h6t, hwf5, h5t' p]
  have htotal : TM.runConfig (M := valuePushProgram.toPhased.toTM) c (2 * k + 4) = c6 := by
    have et : 2 * k + 4 = k + (1 + (k + (1 + (1 + 1)))) := by omega
    rw [et, TM.runConfig_add, ← hc1,
      TM.runConfig_add, valuePush_runConfig_one, ← hc2,
      TM.runConfig_add, ← hc3,
      TM.runConfig_add, valuePush_runConfig_one, ← hc4,
      TM.runConfig_succ, valuePush_runConfig_one, ← hc5, ← hc6]
  have g1 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = opBase → c6.tape p = false := by
    intro p hp
    rw [h6t' p, if_neg (by omega), if_neg (by omega)]
    exact hhome p hp
  have g2 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      opBase + 1 ≤ (p : Nat) → (p : Nat) < opBase + 3 + k → c6.tape p = true := by
    intro p hp1 hp2
    rw [h6t' p, if_neg (by omega), if_neg (by omega)]
    exact hentry p (by omega) (by omega)
  have g3 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      opBase + 3 + k ≤ (p : Nat) → (p : Nat) < aPos → c6.tape p = false := by
    intro p hp1 hp2
    rw [h6t' p, if_neg (by omega), if_neg (by omega)]
    exact hgapL p (by omega) (by omega)
  have g4 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      aPos ≤ (p : Nat) → (p : Nat) < aPos + 1 + k → c6.tape p = true := by
    intro p hp1 hp2
    rw [h6t' p, if_neg (by omega)]
    by_cases hq : (p : Nat) = aPos + k
    · rw [if_pos hq]
    · rw [if_neg hq]
      exact hdst p (by omega) (by omega)
  have g5 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      aPos + k < (p : Nat) → (p : Nat) ≤ aPos + 2 * k + 2 → c6.tape p = false := by
    intro p hp1 hp2
    rw [h6t' p]
    by_cases hq : (p : Nat) = aPos + 2 * k + 1
    · rw [if_pos hq]
    · rw [if_neg hq, if_neg (by omega)]
      by_cases hq2 : (p : Nat) = aPos + 2 * k + 2
      · exact hbeyond p (by omega) (by omega)
      · exact hgap p (by omega) (by omega)
  have hPR : ParkReady c6 opBase aPos k (aPos + 2 * k + 1) :=
    ⟨h6p, h6h', by omega, by omega, hgeom, hbound, g1, g2, g3, g4, g5⟩
  have hOut : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      ((p : Nat) < opBase ∨ aPos + 2 * k + 2 < (p : Nat)) → c6.tape p = c.tape p := by
    intro p hp
    rw [h6t' p, if_neg (by omega), if_neg (by omega)]
  rw [htotal]
  exact ⟨hPR, hOut⟩

set_option maxHeartbeats 1000000 in
/-- **Prologue, empty source** (`k = 0`): the probe sees the terminator and exits directly to the
park chain — `aPos − opBase + 2` steps, the two framing ones written. -/
theorem valuePush_prologue_k0 {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (opBase aPos : Nat) (hlay : ValuePushLayout c opBase aPos 0) :
    ParkReady
      (TM.runConfig (M := valuePushProgram.toPhased.toTM) c (aPos - opBase + 2))
      opBase aPos 0 (aPos + 1)
    ∧ ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
        ¬ (opBase + 1 ≤ (p : Nat) ∧ (p : Nat) < opBase + 3) →
        (TM.runConfig (M := valuePushProgram.toPhased.toTM) c (aPos - opBase + 2)).tape p
          = c.tape p := by
  obtain ⟨hphase, hhead, hgeom, hbound, hzeroL, hanchor, hsrc, hzeroR⟩ := hlay
  obtain ⟨h1p, h1h, h1t⟩ := valuePush_step c (valuePush_state_eta c (by omega) hphase)
    (valuePushProgram_t0 (c.tape c.head))
  set c1 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c with hc1
  have h1h' : (c1.head : Nat) = opBase + 1 := by
    rw [hc1, h1h]
    simp only [Configuration.moveHead, dif_pos (show (c.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have h1t' : c1.tape = c.tape := by
    rw [hc1, h1t, write_self_eq]
  obtain ⟨h2p, h2h, h2t⟩ := valuePush_step c1 (valuePush_state_eta c1 (by omega) h1p)
    (valuePushProgram_t1 (c1.tape c1.head))
  set c2 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c1 with hc2
  have h2h' : (c2.head : Nat) = opBase + 2 := by
    rw [hc2, h2h]
    simp only [Configuration.moveHead, dif_pos (show (c1.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have h2t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c2.tape p = if (p : Nat) = opBase + 1 then true else c.tape p := by
    intro p
    rw [hc2, h2t, valuePush_write_char c1 true h1h' p, h1t']
  obtain ⟨h3p, h3h, h3t⟩ := valuePush_step c2 (valuePush_state_eta c2 (by omega) h2p)
    (valuePushProgram_t2 (c2.tape c2.head))
  set c3 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c2 with hc3
  have h3h' : (c3.head : Nat) = opBase + 3 := by
    rw [hc3, h3h]
    simp only [Configuration.moveHead, dif_pos (show (c2.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have h3t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c3.tape p = if (p : Nat) = opBase + 2 then true
        else if (p : Nat) = opBase + 1 then true else c.tape p := by
    intro p
    rw [hc3, h3t, valuePush_write_char c2 true h2h' p, h2t' p]
  obtain ⟨h4p, h4h, h4t⟩ := valuePush_run_scanR0 3 (by omega) rfl c3 h3p
    (aPos - opBase - 3)
    (by omega)
    (fun p hp1 hp2 => by
      rw [h3t' p, if_neg (by omega), if_neg (by omega)]
      exact hzeroL p (by omega) (by omega))
  set c4 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c3 (aPos - opBase - 3) with hc4
  have h4h' : (c4.head : Nat) = aPos := by omega
  have hb4 : c4.tape c4.head = true := by
    rw [h4t, h3t' c4.head, if_neg (by omega), if_neg (by omega)]
    exact hanchor c4.head (by omega)
  obtain ⟨h5p, h5h, h5t⟩ := valuePush_step c4 (valuePush_state_eta c4 (by omega) h4p)
    (by rw [hb4]; exact valuePushProgram_t3_one)
  set c5 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c4 with hc5
  have h5h' : (c5.head : Nat) = aPos + 1 := by
    rw [hc5, h5h]
    simp only [Configuration.moveHead, dif_pos (show (c4.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have hwf4 : c4.write c4.head true = c4.tape := by
    rw [← hb4]; exact write_self_eq c4
  have h5t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c5.tape p = if (p : Nat) = opBase + 2 then true
        else if (p : Nat) = opBase + 1 then true else c.tape p := by
    intro p
    rw [hc5, h5t, hwf4, h4t, h3t' p]
  -- φ4 probes the terminator (k = 0): exit straight to the park chain
  have hb5 : c5.tape c5.head = false := by
    rw [h5t' c5.head, if_neg (by omega), if_neg (by omega)]
    exact hzeroR c5.head (by omega) (by omega)
  obtain ⟨h6p, h6h, h6t⟩ := valuePush_step c5 (valuePush_state_eta c5 (by omega) h5p)
    (by rw [hb5]; exact valuePushProgram_t4_zero)
  set c6 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c5 with hc6
  have h6h' : (c6.head : Nat) = aPos + 1 := by
    rw [hc6, h6h, Configuration.moveHead_stay]
    exact h5h'
  have hwf5 : c5.write c5.head false = c5.tape := by
    rw [← hb5]; exact write_self_eq c5
  have h6t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c6.tape p = if (p : Nat) = opBase + 2 then true
        else if (p : Nat) = opBase + 1 then true else c.tape p := by
    intro p
    rw [hc6, h6t, hwf5, h5t' p]
  have htotal : TM.runConfig (M := valuePushProgram.toPhased.toTM) c (aPos - opBase + 2) = c6 := by
    have e : aPos - opBase + 2 = 1 + (1 + (1 + ((aPos - opBase - 3) + (1 + 1)))) := by omega
    rw [e, TM.runConfig_add, valuePush_runConfig_one, ← hc1,
      TM.runConfig_add, valuePush_runConfig_one, ← hc2,
      TM.runConfig_add, valuePush_runConfig_one, ← hc3,
      TM.runConfig_add, ← hc4,
      TM.runConfig_succ, valuePush_runConfig_one, ← hc5, ← hc6]
  have g1 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = opBase → c6.tape p = false := by
    intro p hp
    rw [h6t' p, if_neg (by omega), if_neg (by omega)]
    exact hzeroL p (by omega) (by omega)
  have g2 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      opBase + 1 ≤ (p : Nat) → (p : Nat) < opBase + 3 + 0 → c6.tape p = true := by
    intro p hp1 hp2
    rw [h6t' p]
    by_cases h2 : (p : Nat) = opBase + 2
    · rw [if_pos h2]
    · rw [if_neg h2, if_pos (by omega)]
  have g3 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      opBase + 3 + 0 ≤ (p : Nat) → (p : Nat) < aPos → c6.tape p = false := by
    intro p hp1 hp2
    rw [h6t' p, if_neg (by omega), if_neg (by omega)]
    exact hzeroL p (by omega) (by omega)
  have g4 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      aPos ≤ (p : Nat) → (p : Nat) < aPos + 1 + 0 → c6.tape p = true := by
    intro p hp1 hp2
    rw [h6t' p, if_neg (by omega), if_neg (by omega)]
    exact hanchor p (by omega)
  have g5 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      aPos + 0 < (p : Nat) → (p : Nat) ≤ aPos + 2 * 0 + 2 → c6.tape p = false := by
    intro p hp1 hp2
    rw [h6t' p, if_neg (by omega), if_neg (by omega)]
    exact hzeroR p (by omega) (by omega)
  have hPR : ParkReady c6 opBase aPos 0 (aPos + 1) :=
    ⟨h6p, h6h', by omega, by omega, by omega, by omega, g1, g2, g3, g4, g5⟩
  have hOut : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      ¬ (opBase + 1 ≤ (p : Nat) ∧ (p : Nat) < opBase + 3) → c6.tape p = c.tape p := by
    intro p hp
    rw [h6t' p, if_neg (by omega), if_neg (by omega)]
  rw [htotal]
  exact ⟨hPR, hOut⟩

end ContractExpansion
end Frontier
end Pnp4

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

set_option maxHeartbeats 4000000 in
/-- **The park chain**: from `ParkReady`, walk home left across the restored zone and idle in the
accept phase φ34 with the head back at `opBase` — `(p0 − aPos − k) + (aPos − opBase) + k + 2`
steps, the tape untouched. -/
theorem valuePush_park {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (opBase aPos k p0 : Nat) (hpr : ParkReady c opBase aPos k p0) :
    (((TM.runConfig (M := valuePushProgram.toPhased.toTM) c
        ((p0 - aPos - k) + (aPos - opBase) + k + 2)).state).fst : Nat) = 34
    ∧ ((TM.runConfig (M := valuePushProgram.toPhased.toTM) c
        ((p0 - aPos - k) + (aPos - opBase) + k + 2)).head : Nat) = opBase
    ∧ (TM.runConfig (M := valuePushProgram.toPhased.toTM) c
        ((p0 - aPos - k) + (aPos - opBase) + k + 2)).tape = c.tape := by
  obtain ⟨hphase, hhead, hp0l, hp0r, hgeom, hbound, hhome, hentry, hgapL, hblk, hz⟩ := hpr
  -- φ30 scan the zeros left onto the block's rightmost one
  obtain ⟨h1p, h1h, h1t⟩ := valuePush_run_scanL0 30 (by omega) rfl c hphase
    (p0 - aPos - k)
    (by omega)
    (fun p hp1 hp2 => by
      exact hz p (by omega) (by omega))
  set c1 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c (p0 - aPos - k) with hc1
  have h1h' : (c1.head : Nat) = aPos + k := by omega
  have hb1 : c1.tape c1.head = true := by
    rw [h1t]
    exact hblk c1.head (by omega) (by omega)
  obtain ⟨h2p, h2h, h2t⟩ := valuePush_step c1 (valuePush_state_eta c1 (by omega) h1p)
    (by rw [hb1]; exact valuePushProgram_t30_one)
  set c2 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c1 with hc2
  have h2h' : (c2.head : Nat) = aPos + k - 1 := by
    rw [hc2, h2h, Configuration.moveHead_left_val_of_pos c1 (by omega)]
    omega
  have hwf1 : c1.write c1.head true = c1.tape := by
    rw [← hb1]; exact write_self_eq c1
  have h2t' : c2.tape = c.tape := by
    rw [hc2, h2t, hwf1, h1t]
  -- φ31 walk the rest of the block (k more ones, ending left of the anchor)
  obtain ⟨h3p, h3h, h3t⟩ := valuePush_run_walkL1 31 (by omega) rfl c2 h2p k
    (by omega)
    (fun p hp1 hp2 => by
      rw [h2t']
      exact hblk p (by omega) (by omega))
  set c3 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c2 k with hc3
  have h3h' : (c3.head : Nat) = aPos - 1 := by omega
  have hb3 : c3.tape c3.head = false := by
    rw [h3t, h2t']
    exact hgapL c3.head (by omega) (by omega)
  obtain ⟨h4p, h4h, h4t⟩ := valuePush_step c3 (valuePush_state_eta c3 (by omega) h3p)
    (by rw [hb3]; exact valuePushProgram_t31_zero)
  set c4 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c3 with hc4
  have h4h' : (c4.head : Nat) = aPos - 1 := by
    rw [hc4, h4h, Configuration.moveHead_stay]
    exact h3h'
  have hwf3 : c3.write c3.head false = c3.tape := by
    rw [← hb3]; exact write_self_eq c3
  have h4t' : c4.tape = c.tape := by
    rw [hc4, h4t, hwf3, h3t, h2t']
  -- φ32 scan gap₁ left onto the entry's rightmost one
  obtain ⟨h5p, h5h, h5t⟩ := valuePush_run_scanL0 32 (by omega) rfl c4 h4p
    (aPos - opBase - k - 3)
    (by omega)
    (fun p hp1 hp2 => by
      rw [h4t']
      exact hgapL p (by omega) (by omega))
  set c5 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c4 (aPos - opBase - k - 3)
    with hc5
  have h5h' : (c5.head : Nat) = opBase + 2 + k := by omega
  have hb5 : c5.tape c5.head = true := by
    rw [h5t, h4t']
    exact hentry c5.head (by omega) (by omega)
  obtain ⟨h6p, h6h, h6t⟩ := valuePush_step c5 (valuePush_state_eta c5 (by omega) h5p)
    (by rw [hb5]; exact valuePushProgram_t32_one)
  set c6 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c5 with hc6
  have h6h' : (c6.head : Nat) = opBase + 1 + k := by
    rw [hc6, h6h, Configuration.moveHead_left_val_of_pos c5 (by omega)]
    omega
  have hwf5 : c5.write c5.head true = c5.tape := by
    rw [← hb5]; exact write_self_eq c5
  have h6t' : c6.tape = c.tape := by
    rw [hc6, h6t, hwf5, h5t, h4t']
  -- φ33 walk the entry ones left onto HOME, idle in φ34
  obtain ⟨h7p, h7h, h7t⟩ := valuePush_run_walkL1 33 (by omega) rfl c6 h6p (k + 1)
    (by omega)
    (fun p hp1 hp2 => by
      rw [h6t']
      exact hentry p (by omega) (by omega))
  set c7 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c6 (k + 1) with hc7
  have h7h' : (c7.head : Nat) = opBase := by omega
  have hb7 : c7.tape c7.head = false := by
    rw [h7t, h6t']
    exact hhome c7.head (by omega)
  obtain ⟨h8p, h8h, h8t⟩ := valuePush_step c7 (valuePush_state_eta c7 (by omega) h7p)
    (by rw [hb7]; exact valuePushProgram_t33_zero)
  set c8 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c7 with hc8
  have h8h' : (c8.head : Nat) = opBase := by
    rw [hc8, h8h, Configuration.moveHead_stay]
    exact h7h'
  have hwf7 : c7.write c7.head false = c7.tape := by
    rw [← hb7]; exact write_self_eq c7
  have h8t' : c8.tape = c.tape := by
    rw [hc8, h8t, hwf7, h7t, h6t']
  have htotal : TM.runConfig (M := valuePushProgram.toPhased.toTM) c
      ((p0 - aPos - k) + (aPos - opBase) + k + 2) = c8 := by
    have et : (p0 - aPos - k) + (aPos - opBase) + k + 2
        = (p0 - aPos - k) + (1 + (k + (1 + ((aPos - opBase - k - 3)
          + (1 + ((k + 1) + 1)))))) := by
      omega
    rw [et, TM.runConfig_add, ← hc1,
      TM.runConfig_add, valuePush_runConfig_one, ← hc2,
      TM.runConfig_add, ← hc3,
      TM.runConfig_add, valuePush_runConfig_one, ← hc4,
      TM.runConfig_add, ← hc5,
      TM.runConfig_add, valuePush_runConfig_one, ← hc6,
      TM.runConfig_add, ← hc7,
      valuePush_runConfig_one, ← hc8]
  rw [htotal]
  exact ⟨h8p, h8h', h8t'⟩

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

set_option maxHeartbeats 4000000 in
/-- **Final-round first-half confinement**: along the `2k + 2` steps the phase never reaches the
accept and the head stays ≤ `aPos + 2k + 2` — additive companion to `valuePush_drain_final_A`. -/
theorem valuePush_drain_final_A_confined {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (opBase aPos k : Nat) (hds : DrainState c opBase aPos k (k - 1)) (hk : 0 < k) :
    ∀ s : Nat, s < 2 * k + 2 →
      (((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).state).fst : Nat) ≠ 34
      ∧ ((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).head : Nat)
          ≤ aPos + 2 * k + 2 := by
  obtain ⟨hphase, hhead, hgeom, hbound, _, hhome, hentry, hgapL, hanchor, hpre, hrest,
    hterm, hscr, hzr⟩ := hds
  have hhead' : (c.head : Nat) = aPos + k := by omega
  obtain ⟨h1p, h1h, h1t⟩ := valuePush_step c (valuePush_state_eta c (by omega) hphase)
    (valuePushProgram_t5 (c.tape c.head))
  set c1 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c with hc1
  have h1p' : ((c1.state).fst : Nat) = 6 := h1p
  have h1h' : (c1.head : Nat) = aPos + 1 + k := by
    rw [hc1, h1h]
    simp only [Configuration.moveHead, dif_pos (show (c.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have h1t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c1.tape p = if (p : Nat) = aPos + k then false else c.tape p := by
    intro p
    rw [hc1, h1t]
    exact valuePush_write_char c false hhead' p
  have hb1 : c1.tape c1.head = false := by
    rw [h1t' c1.head, if_neg (by omega)]
    exact hterm c1.head (by omega)
  obtain ⟨h2p, h2h, h2t⟩ := valuePush_step c1 (valuePush_state_eta c1 (by omega) h1p)
    (by rw [hb1]; exact valuePushProgram_t6_zero)
  set c2 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c1 with hc2
  have h2p' : ((c2.state).fst : Nat) = 16 := h2p
  have h2h' : (c2.head : Nat) = aPos + 2 + k := by
    rw [hc2, h2h]
    simp only [Configuration.moveHead, dif_pos (show (c1.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have hwf1 : c1.write c1.head false = c1.tape := by
    rw [← hb1]; exact write_self_eq c1
  have h2t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c2.tape p = if (p : Nat) = aPos + k then false else c.tape p := by
    intro p
    rw [hc2, h2t, hwf1, h1t' p]
  obtain ⟨h3p, h3h, h3t⟩ := valuePush_run_walkR1 16 (by omega) rfl c2 h2p (k - 1)
    (by omega)
    (fun p hp1 hp2 => by
      rw [h2t' p, if_neg (by omega)]
      exact hscr p (by omega) (by omega))
  set c3 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c2 (k - 1) with hc3
  have h3h' : (c3.head : Nat) = aPos + 1 + 2 * k := by omega
  have hb3 : c3.tape c3.head = false := by
    rw [h3t, h2t' c3.head, if_neg (by omega)]
    exact hzr c3.head (by omega) (by omega)
  obtain ⟨h4p, h4h, h4t⟩ := valuePush_step c3 (valuePush_state_eta c3 (by omega) h3p)
    (by rw [hb3]; exact valuePushProgram_t16_zero)
  set c4 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c3 with hc4
  have h4p' : ((c4.state).fst : Nat) = 17 := h4p
  have h4h' : (c4.head : Nat) = aPos + 2 * k := by
    rw [hc4, h4h, Configuration.moveHead_left_val_of_pos c3 (by omega)]
    omega
  have h4t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c4.tape p = if (p : Nat) = aPos + 1 + 2 * k then true
        else if (p : Nat) = aPos + k then false else c.tape p := by
    intro p
    rw [hc4, h4t, valuePush_write_char c3 true h3h' p, h3t, h2t' p]
  have hcfg1 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c 1 = c1 := by
    rw [valuePush_runConfig_one, ← hc1]
  have hcfg2 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c 2 = c2 := by
    rw [show (2 : Nat) = 1 + 1 from rfl, TM.runConfig_add, hcfg1,
      valuePush_runConfig_one, ← hc2]
  have hcfg3 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c (2 + (k - 1)) = c3 := by
    rw [TM.runConfig_add, hcfg2, ← hc3]
  have hcfg4 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c (2 + (k - 1) + 1) = c4 := by
    rw [TM.runConfig_succ, hcfg3, ← hc4]
  intro s hs
  by_cases hA : s = 0
  · subst hA
    rw [TM.runConfig_zero]
    exact ⟨by omega, by omega⟩
  by_cases hB : s = 1
  · subst hB
    rw [hcfg1]
    exact ⟨by omega, by omega⟩
  by_cases hC : s < 2 + (k - 1)
  · -- φ16 scratch walk right, r := s − 2
    obtain ⟨hrp, hrh, _⟩ := valuePush_run_walkR1 16 (by omega) rfl c2 h2p (s - 2)
      (by omega)
      (fun p hp1 hp2 => by
        rw [h2t' p, if_neg (by omega)]
        exact hscr p (by omega) (by omega))
    rw [show s = 2 + (s - 2) from by omega, TM.runConfig_add, hcfg2]
    exact ⟨by omega, by omega⟩
  by_cases hD : s = 2 + (k - 1)
  · subst hD
    rw [hcfg3]
    exact ⟨by omega, by omega⟩
  -- φ17 scratch walk left, r := s − (2 + (k − 1) + 1) ≤ k − 1
  · obtain ⟨hrp, hrh, _⟩ := valuePush_run_walkL1 17 (by omega) rfl c4 h4p
      (s - (2 + (k - 1) + 1))
      (by omega)
      (fun p hp1 hp2 => by
        rw [h4t' p, if_neg (by omega), if_neg (by omega)]
        exact hscr p (by omega) (by omega))
    rw [show s = (2 + (k - 1) + 1) + (s - (2 + (k - 1) + 1)) from by omega,
      TM.runConfig_add, hcfg4]
    exact ⟨by omega, by omega⟩

set_option maxHeartbeats 4000000 in
/-- **Final-round second-half confinement**: along the `2·(aPos − opBase) − k − 1` steps the phase
never reaches the accept and the head stays ≤ `aPos + 2k + 2` — additive companion to
`valuePush_drain_final_B`. -/
theorem valuePush_drain_final_B_confined {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (opBase aPos k : Nat) (hcut : DrainFinalCut c opBase aPos k) :
    ∀ s : Nat, s < 2 * (aPos - opBase) - k - 1 →
      (((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).state).fst : Nat) ≠ 34
      ∧ ((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).head : Nat)
          ≤ aPos + 2 * k + 2 := by
  obtain ⟨hphase, hhead, hgeom, hbound, hk, hhome, hentry, hgapL, hanchor, hsrcz,
    hscr, hbeyond⟩ := hcut
  obtain ⟨h7p, h7h, h7t⟩ := valuePush_run_scanL0 18 (by omega) rfl c hphase k
    (by omega)
    (fun p hp1 hp2 => by
      exact hsrcz p (by omega) (by omega))
  set c7 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c k with hc7
  have h7h' : (c7.head : Nat) = aPos := by omega
  have hb7 : c7.tape c7.head = true := by
    rw [h7t]
    exact hanchor c7.head (by omega)
  obtain ⟨h8p, h8h, h8t⟩ := valuePush_step c7 (valuePush_state_eta c7 (by omega) h7p)
    (by rw [hb7]; exact valuePushProgram_t18_one)
  set c8 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c7 with hc8
  have h8p' : ((c8.state).fst : Nat) = 19 := h8p
  have h8h' : (c8.head : Nat) = aPos - 1 := by
    rw [hc8, h8h, Configuration.moveHead_left_val_of_pos c7 (by omega)]
    omega
  have hwf7 : c7.write c7.head true = c7.tape := by
    rw [← hb7]; exact write_self_eq c7
  have h8t' : c8.tape = c.tape := by
    rw [hc8, h8t, hwf7, h7t]
  obtain ⟨h9p, h9h, h9t⟩ := valuePush_run_scanL0 19 (by omega) rfl c8 h8p
    (aPos - opBase - k - 2)
    (by omega)
    (fun p hp1 hp2 => by
      rw [h8t']
      exact hgapL p (by omega) (by omega))
  set c9 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c8 (aPos - opBase - k - 2)
    with hc9
  have h9h' : (c9.head : Nat) = opBase + 1 + k := by omega
  have hb9 : c9.tape c9.head = true := by
    rw [h9t, h8t']
    exact hentry c9.head (by omega) (by omega)
  obtain ⟨h10p, h10h, h10t⟩ := valuePush_step c9 (valuePush_state_eta c9 (by omega) h9p)
    (by rw [hb9]; exact valuePushProgram_t19_one)
  set c10 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c9 with hc10
  have h10p' : ((c10.state).fst : Nat) = 20 := h10p
  have h10h' : (c10.head : Nat) = opBase + 2 + k := by
    rw [hc10, h10h]
    simp only [Configuration.moveHead, dif_pos (show (c9.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have hwf9 : c9.write c9.head true = c9.tape := by
    rw [← hb9]; exact write_self_eq c9
  have h10t' : c10.tape = c.tape := by
    rw [hc10, h10t, hwf9, h9t, h8t']
  obtain ⟨h11p, h11h, h11t⟩ := valuePush_step c10 (valuePush_state_eta c10 (by omega) h10p)
    (valuePushProgram_t20 (c10.tape c10.head))
  set c11 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c10 with hc11
  have h11p' : ((c11.state).fst : Nat) = 21 := h11p
  have h11h' : (c11.head : Nat) = opBase + 3 + k := by
    rw [hc11, h11h]
    simp only [Configuration.moveHead, dif_pos (show (c10.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have h11t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c11.tape p = if (p : Nat) = opBase + 2 + k then true else c.tape p := by
    intro p
    rw [hc11, h11t, valuePush_write_char c10 true h10h' p, h10t']
  have hcfg7 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c k = c7 := hc7.symm
  have hcfg8 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c (k + 1) = c8 := by
    rw [TM.runConfig_succ, hcfg7, ← hc8]
  have hcfg9 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c
      (k + 1 + (aPos - opBase - k - 2)) = c9 := by
    rw [TM.runConfig_add, hcfg8, ← hc9]
  have hcfg10 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c
      (k + 1 + (aPos - opBase - k - 2) + 1) = c10 := by
    rw [TM.runConfig_succ, hcfg9, ← hc10]
  have hcfg11 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c
      (k + 1 + (aPos - opBase - k - 2) + 2) = c11 := by
    rw [show k + 1 + (aPos - opBase - k - 2) + 2
        = k + 1 + (aPos - opBase - k - 2) + 1 + 1 from by omega,
      TM.runConfig_succ, hcfg10, ← hc11]
  intro s hs
  by_cases hA : s < k
  · -- φ18 zeroed-source scan left, r := s
    obtain ⟨hrp, hrh, _⟩ := valuePush_run_scanL0 18 (by omega) rfl c hphase s
      (by omega)
      (fun p hp1 hp2 => by
        exact hsrcz p (by omega) (by omega))
    exact ⟨by omega, by omega⟩
  by_cases hB : s = k
  · subst hB
    rw [hcfg7]
    exact ⟨by omega, by omega⟩
  by_cases hC : s < k + 1 + (aPos - opBase - k - 2)
  · -- φ19 gap scan left, r := s − (k + 1)
    obtain ⟨hrp, hrh, _⟩ := valuePush_run_scanL0 19 (by omega) rfl c8 h8p (s - (k + 1))
      (by omega)
      (fun p hp1 hp2 => by
        rw [h8t']
        exact hgapL p (by omega) (by omega))
    rw [show s = (k + 1) + (s - (k + 1)) from by omega, TM.runConfig_add, hcfg8]
    exact ⟨by omega, by omega⟩
  by_cases hD : s = k + 1 + (aPos - opBase - k - 2)
  · subst hD
    rw [hcfg9]
    exact ⟨by omega, by omega⟩
  by_cases hE : s = k + 1 + (aPos - opBase - k - 2) + 1
  · subst hE
    rw [hcfg10]
    exact ⟨by omega, by omega⟩
  -- φ21 gap scan right, r := s − (k + 1 + (aPos − opBase − k − 2) + 2)
  · obtain ⟨hrp, hrh, _⟩ := valuePush_run_scanR0 21 (by omega) rfl c11 h11p
      (s - (k + 1 + (aPos - opBase - k - 2) + 2))
      (by omega)
      (fun p hp1 hp2 => by
        rw [h11t' p, if_neg (by omega)]
        exact hgapL p (by omega) (by omega))
    rw [show s = (k + 1 + (aPos - opBase - k - 2) + 2)
        + (s - (k + 1 + (aPos - opBase - k - 2) + 2)) from by omega,
      TM.runConfig_add, hcfg11]
    exact ⟨by omega, by omega⟩



open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

set_option maxHeartbeats 4000000 in
/-- **Mid restore-round confinement** (`j + 1 < k`): along the round's `2j + 2k + 12` steps the
phase never reaches the accept and the head stays ≤ `aPos + 2k + 2` — additive companion to
`valuePush_clone_mid`. -/
theorem valuePush_clone_mid_confined {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (opBase aPos k j : Nat) (hcs : CloneState c opBase aPos k j) (hj2 : j + 1 < k) :
    ∀ s : Nat, s < 2 * j + 2 * k + 12 →
      (((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).state).fst : Nat) ≠ 34
      ∧ ((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).head : Nat)
          ≤ aPos + 2 * k + 2 := by
  obtain ⟨hphase, hhead, hgeom, hbound, _, hhome, hentry, hgapL, hdst, hgap, hscr,
    hbeyond⟩ := hcs
  obtain ⟨h1p, h1h, h1t⟩ := valuePush_run_walkR1 22 (by omega) rfl c hphase (1 + j)
    (by omega)
    (fun p hp1 hp2 => by
      exact hdst p (by omega) (by omega))
  set c1 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c (1 + j) with hc1
  have h1h' : (c1.head : Nat) = aPos + 1 + j := by omega
  have hb1 : c1.tape c1.head = false := by
    rw [h1t]
    exact hgap c1.head (by omega) (by omega)
  obtain ⟨h2p, h2h, h2t⟩ := valuePush_step c1 (valuePush_state_eta c1 (by omega) h1p)
    (by rw [hb1]; exact valuePushProgram_t22_zero)
  set c2 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c1 with hc2
  have h2p' : ((c2.state).fst : Nat) = 23 := h2p
  have h2h' : (c2.head : Nat) = aPos + 2 + j := by
    rw [hc2, h2h]
    simp only [Configuration.moveHead, dif_pos (show (c1.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have h2t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c2.tape p = if (p : Nat) = aPos + 1 + j then true else c.tape p := by
    intro p
    rw [hc2, h2t, valuePush_write_char c1 true h1h' p, h1t]
  obtain ⟨h3p, h3h, h3t⟩ := valuePush_run_scanR0 23 (by omega) rfl c2 h2p k
    (by omega)
    (fun p hp1 hp2 => by
      rw [h2t' p, if_neg (by omega)]
      exact hgap p (by omega) (by omega))
  set c3 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c2 k with hc3
  have h3h' : (c3.head : Nat) = aPos + 2 + j + k := by omega
  have hb3 : c3.tape c3.head = true := by
    rw [h3t, h2t' c3.head, if_neg (by omega)]
    exact hscr c3.head (by omega) (by omega)
  obtain ⟨h4p, h4h, h4t⟩ := valuePush_step c3 (valuePush_state_eta c3 (by omega) h3p)
    (by rw [hb3]; exact valuePushProgram_t23_one)
  set c4 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c3 with hc4
  have h4p' : ((c4.state).fst : Nat) = 24 := h4p
  have h4h' : (c4.head : Nat) = aPos + 2 + j + k := by
    rw [hc4, h4h, Configuration.moveHead_stay]
    exact h3h'
  have hwf3 : c3.write c3.head true = c3.tape := by
    rw [← hb3]; exact write_self_eq c3
  have h4t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c4.tape p = if (p : Nat) = aPos + 1 + j then true else c.tape p := by
    intro p
    rw [hc4, h4t, hwf3, h3t, h2t' p]
  obtain ⟨h5p, h5h, h5t⟩ := valuePush_step c4 (valuePush_state_eta c4 (by omega) h4p)
    (valuePushProgram_t24 (c4.tape c4.head))
  set c5 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c4 with hc5
  have h5p' : ((c5.state).fst : Nat) = 25 := h5p
  have h5h' : (c5.head : Nat) = aPos + 3 + j + k := by
    rw [hc5, h5h]
    simp only [Configuration.moveHead, dif_pos (show (c4.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have h5t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c5.tape p = if (p : Nat) = aPos + 2 + j + k then false
        else if (p : Nat) = aPos + 1 + j then true else c.tape p := by
    intro p
    rw [hc5, h5t, valuePush_write_char c4 false h4h' p, h4t' p]
  have hb5 : c5.tape c5.head = true := by
    rw [h5t' c5.head, if_neg (by omega), if_neg (by omega)]
    exact hscr c5.head (by omega) (by omega)
  obtain ⟨h6p, h6h, h6t⟩ := valuePush_step c5 (valuePush_state_eta c5 (by omega) h5p)
    (by rw [hb5]; exact valuePushProgram_t25_one)
  set c6 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c5 with hc6
  have h6p' : ((c6.state).fst : Nat) = 26 := h6p
  have h6h' : (c6.head : Nat) = aPos + 2 + j + k := by
    rw [hc6, h6h, Configuration.moveHead_left_val_of_pos c5 (by omega)]
    omega
  have hwf5 : c5.write c5.head true = c5.tape := by
    rw [← hb5]; exact write_self_eq c5
  have h6t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c6.tape p = if (p : Nat) = aPos + 2 + j + k then false
        else if (p : Nat) = aPos + 1 + j then true else c.tape p := by
    intro p
    rw [hc6, h6t, hwf5, h5t' p]
  obtain ⟨h7p, h7h, h7t⟩ := valuePush_run_scanL0 26 (by omega) rfl c6 h6p (k + 1)
    (by omega)
    (fun p hp1 hp2 => by
      rw [h6t' p]
      by_cases hq : (p : Nat) = aPos + 2 + j + k
      · rw [if_pos hq]
      · rw [if_neg hq, if_neg (by omega)]
        exact hgap p (by omega) (by omega))
  set c7 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c6 (k + 1) with hc7
  have h7h' : (c7.head : Nat) = aPos + 1 + j := by omega
  have hb7 : c7.tape c7.head = true := by
    rw [h7t, h6t' c7.head, if_neg (by omega)]
    rw [if_pos (show ((c7.head : Fin (valuePushProgram.toPhased.toTM.tapeLength L)) : Nat)
      = aPos + 1 + j by omega)]
  obtain ⟨h8p, h8h, h8t⟩ := valuePush_step c7 (valuePush_state_eta c7 (by omega) h7p)
    (by rw [hb7]; exact valuePushProgram_t26_one)
  set c8 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c7 with hc8
  have h8p' : ((c8.state).fst : Nat) = 27 := h8p
  have h8h' : (c8.head : Nat) = aPos + 1 + j := by
    rw [hc8, h8h, Configuration.moveHead_stay]
    exact h7h'
  have hwf7 : c7.write c7.head true = c7.tape := by
    rw [← hb7]; exact write_self_eq c7
  have h8t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c8.tape p = if (p : Nat) = aPos + 2 + j + k then false
        else if (p : Nat) = aPos + 1 + j then true else c.tape p := by
    intro p
    rw [hc8, h8t, hwf7, h7t, h6t' p]
  obtain ⟨h9p, h9h, h9t⟩ := valuePush_run_walkL1 27 (by omega) rfl c8 h8p (j + 2)
    (by omega)
    (fun p hp1 hp2 => by
      rw [h8t' p, if_neg (by omega)]
      by_cases hq : (p : Nat) = aPos + 1 + j
      · rw [if_pos hq]
      · rw [if_neg hq]
        exact hdst p (by omega) (by omega))
  set c9 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c8 (j + 2) with hc9
  have h9h' : (c9.head : Nat) = aPos - 1 := by omega
  have hb9 : c9.tape c9.head = false := by
    rw [h9t, h8t' c9.head, if_neg (by omega), if_neg (by omega)]
    exact hgapL c9.head (by omega) (by omega)
  obtain ⟨h10p, h10h, h10t⟩ := valuePush_step c9 (valuePush_state_eta c9 (by omega) h9p)
    (by rw [hb9]; exact valuePushProgram_t27_zero)
  set c10 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c9 with hc10
  have h10p' : ((c10.state).fst : Nat) = 28 := h10p
  have h10h' : (c10.head : Nat) = aPos - 1 := by
    rw [hc10, h10h, Configuration.moveHead_stay]
    exact h9h'
  have hwf9 : c9.write c9.head false = c9.tape := by
    rw [← hb9]; exact write_self_eq c9
  have h10t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c10.tape p = if (p : Nat) = aPos + 2 + j + k then false
        else if (p : Nat) = aPos + 1 + j then true else c.tape p := by
    intro p
    rw [hc10, h10t, hwf9, h9t, h8t' p]
  obtain ⟨h11p, h11h, h11t⟩ := valuePush_step c10 (valuePush_state_eta c10 (by omega) h10p)
    (valuePushProgram_t28 (c10.tape c10.head))
  set c11 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c10 with hc11
  have h11p' : ((c11.state).fst : Nat) = 29 := h11p
  have h11h' : (c11.head : Nat) = aPos := by
    rw [hc11, h11h]
    simp only [Configuration.moveHead, dif_pos (show (c10.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have hcfg1 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c (1 + j) = c1 := hc1.symm
  have hcfg2 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c (1 + j + 1) = c2 := by
    rw [TM.runConfig_succ, hcfg1, ← hc2]
  have hcfg3 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c (1 + j + 1 + k) = c3 := by
    rw [TM.runConfig_add, hcfg2, ← hc3]
  have hcfg4 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c (1 + j + 1 + k + 1)
      = c4 := by
    rw [TM.runConfig_succ, hcfg3, ← hc4]
  have hcfg5 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c (1 + j + 1 + k + 2)
      = c5 := by
    rw [show 1 + j + 1 + k + 2 = 1 + j + 1 + k + 1 + 1 from by omega,
      TM.runConfig_succ, hcfg4, ← hc5]
  have hcfg6 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c (1 + j + 1 + k + 3)
      = c6 := by
    rw [show 1 + j + 1 + k + 3 = 1 + j + 1 + k + 2 + 1 from by omega,
      TM.runConfig_succ, hcfg5, ← hc6]
  have hcfg7 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c
      (1 + j + 1 + k + 3 + (k + 1)) = c7 := by
    rw [TM.runConfig_add, hcfg6, ← hc7]
  have hcfg8 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c
      (1 + j + 1 + k + 3 + (k + 1) + 1) = c8 := by
    rw [TM.runConfig_succ, hcfg7, ← hc8]
  have hcfg9 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c
      (1 + j + 1 + k + 3 + (k + 1) + 1 + (j + 2)) = c9 := by
    rw [TM.runConfig_add, hcfg8, ← hc9]
  have hcfg10 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c
      (1 + j + 1 + k + 3 + (k + 1) + 1 + (j + 2) + 1) = c10 := by
    rw [TM.runConfig_succ, hcfg9, ← hc10]
  have hcfg11 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c
      (1 + j + 1 + k + 3 + (k + 1) + 1 + (j + 2) + 2) = c11 := by
    rw [show 1 + j + 1 + k + 3 + (k + 1) + 1 + (j + 2) + 2
        = 1 + j + 1 + k + 3 + (k + 1) + 1 + (j + 2) + 1 + 1 from by omega,
      TM.runConfig_succ, hcfg10, ← hc11]
  intro s hs
  by_cases hA : s < 1 + j
  · -- φ22 destination walk right, r := s
    obtain ⟨hrp, hrh, _⟩ := valuePush_run_walkR1 22 (by omega) rfl c hphase s
      (by omega)
      (fun p hp1 hp2 => by
        exact hdst p (by omega) (by omega))
    exact ⟨by omega, by omega⟩
  by_cases hB : s = 1 + j
  · subst hB
    rw [hcfg1]
    exact ⟨by omega, by omega⟩
  by_cases hC : s < 1 + j + 1 + k
  · -- φ23 sliding-gap scan right, r := s − (1 + j + 1)
    obtain ⟨hrp, hrh, _⟩ := valuePush_run_scanR0 23 (by omega) rfl c2 h2p (s - (1 + j + 1))
      (by omega)
      (fun p hp1 hp2 => by
        rw [h2t' p, if_neg (by omega)]
        exact hgap p (by omega) (by omega))
    rw [show s = (1 + j + 1) + (s - (1 + j + 1)) from by omega, TM.runConfig_add, hcfg2]
    exact ⟨by omega, by omega⟩
  by_cases hD : s = 1 + j + 1 + k
  · subst hD
    rw [hcfg3]
    exact ⟨by omega, by omega⟩
  by_cases hE : s = 1 + j + 1 + k + 1
  · subst hE
    rw [hcfg4]
    exact ⟨by omega, by omega⟩
  by_cases hF : s = 1 + j + 1 + k + 2
  · subst hF
    rw [hcfg5]
    exact ⟨by omega, by omega⟩
  by_cases hG : s < 1 + j + 1 + k + 3 + (k + 1)
  · -- φ26 slid-gap scan left, r := s − (1 + j + 1 + k + 3)
    obtain ⟨hrp, hrh, _⟩ := valuePush_run_scanL0 26 (by omega) rfl c6 h6p
      (s - (1 + j + 1 + k + 3))
      (by omega)
      (fun p hp1 hp2 => by
        rw [h6t' p]
        by_cases hq : (p : Nat) = aPos + 2 + j + k
        · rw [if_pos hq]
        · rw [if_neg hq, if_neg (by omega)]
          exact hgap p (by omega) (by omega))
    rw [show s = (1 + j + 1 + k + 3) + (s - (1 + j + 1 + k + 3)) from by omega,
      TM.runConfig_add, hcfg6]
    exact ⟨by omega, by omega⟩
  by_cases hH : s = 1 + j + 1 + k + 3 + (k + 1)
  · subst hH
    rw [hcfg7]
    exact ⟨by omega, by omega⟩
  by_cases hI : s < 1 + j + 1 + k + 3 + (k + 1) + 1 + (j + 2)
  · -- φ27 destination walk left, r := s − (1 + j + 1 + k + 3 + (k + 1) + 1)
    obtain ⟨hrp, hrh, _⟩ := valuePush_run_walkL1 27 (by omega) rfl c8 h8p
      (s - (1 + j + 1 + k + 3 + (k + 1) + 1))
      (by omega)
      (fun p hp1 hp2 => by
        rw [h8t' p, if_neg (by omega)]
        by_cases hq : (p : Nat) = aPos + 1 + j
        · rw [if_pos hq]
        · rw [if_neg hq]
          exact hdst p (by omega) (by omega))
    rw [show s = (1 + j + 1 + k + 3 + (k + 1) + 1)
        + (s - (1 + j + 1 + k + 3 + (k + 1) + 1)) from by omega,
      TM.runConfig_add, hcfg8]
    exact ⟨by omega, by omega⟩
  by_cases hJ : s = 1 + j + 1 + k + 3 + (k + 1) + 1 + (j + 2)
  · subst hJ
    rw [hcfg9]
    exact ⟨by omega, by omega⟩
  by_cases hK : s = 1 + j + 1 + k + 3 + (k + 1) + 1 + (j + 2) + 1
  · subst hK
    rw [hcfg10]
    exact ⟨by omega, by omega⟩
  -- s = … + 2 (φ29, the back-edge step)
  · have hKK : s = 1 + j + 1 + k + 3 + (k + 1) + 1 + (j + 2) + 2 := by omega
    subst hKK
    rw [hcfg11]
    exact ⟨by omega, by omega⟩



open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

set_option maxHeartbeats 4000000 in
/-- **Last restore-round confinement** (`j = k − 1`): along the `2k + 4` steps the phase never
reaches the accept and the head stays ≤ `aPos + 2k + 2` — additive companion to
`valuePush_clone_last`. -/
theorem valuePush_clone_last_confined {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (opBase aPos k : Nat) (hcs : CloneState c opBase aPos k (k - 1)) (hk : 0 < k) :
    ∀ s : Nat, s < 2 * k + 4 →
      (((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).state).fst : Nat) ≠ 34
      ∧ ((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).head : Nat)
          ≤ aPos + 2 * k + 2 := by
  obtain ⟨hphase, hhead, hgeom, hbound, _, hhome, hentry, hgapL, hdst, hgap, hscr,
    hbeyond⟩ := hcs
  obtain ⟨h1p, h1h, h1t⟩ := valuePush_run_walkR1 22 (by omega) rfl c hphase k
    (by omega)
    (fun p hp1 hp2 => by
      exact hdst p (by omega) (by omega))
  set c1 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c k with hc1
  have h1h' : (c1.head : Nat) = aPos + k := by omega
  have hb1 : c1.tape c1.head = false := by
    rw [h1t]
    exact hgap c1.head (by omega) (by omega)
  obtain ⟨h2p, h2h, h2t⟩ := valuePush_step c1 (valuePush_state_eta c1 (by omega) h1p)
    (by rw [hb1]; exact valuePushProgram_t22_zero)
  set c2 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c1 with hc2
  have h2p' : ((c2.state).fst : Nat) = 23 := h2p
  have h2h' : (c2.head : Nat) = aPos + 1 + k := by
    rw [hc2, h2h]
    simp only [Configuration.moveHead, dif_pos (show (c1.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have h2t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c2.tape p = if (p : Nat) = aPos + k then true else c.tape p := by
    intro p
    rw [hc2, h2t, valuePush_write_char c1 true h1h' p, h1t]
  obtain ⟨h3p, h3h, h3t⟩ := valuePush_run_scanR0 23 (by omega) rfl c2 h2p k
    (by omega)
    (fun p hp1 hp2 => by
      rw [h2t' p, if_neg (by omega)]
      exact hgap p (by omega) (by omega))
  set c3 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c2 k with hc3
  have h3h' : (c3.head : Nat) = aPos + 2 * k + 1 := by omega
  have hb3 : c3.tape c3.head = true := by
    rw [h3t, h2t' c3.head, if_neg (by omega)]
    exact hscr c3.head (by omega) (by omega)
  obtain ⟨h4p, h4h, h4t⟩ := valuePush_step c3 (valuePush_state_eta c3 (by omega) h3p)
    (by rw [hb3]; exact valuePushProgram_t23_one)
  set c4 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c3 with hc4
  have h4p' : ((c4.state).fst : Nat) = 24 := h4p
  have h4h' : (c4.head : Nat) = aPos + 2 * k + 1 := by
    rw [hc4, h4h, Configuration.moveHead_stay]
    exact h3h'
  have hwf3 : c3.write c3.head true = c3.tape := by
    rw [← hb3]; exact write_self_eq c3
  have h4t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c4.tape p = if (p : Nat) = aPos + k then true else c.tape p := by
    intro p
    rw [hc4, h4t, hwf3, h3t, h2t' p]
  obtain ⟨h5p, h5h, h5t⟩ := valuePush_step c4 (valuePush_state_eta c4 (by omega) h4p)
    (valuePushProgram_t24 (c4.tape c4.head))
  set c5 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c4 with hc5
  have h5p' : ((c5.state).fst : Nat) = 25 := h5p
  have h5h' : (c5.head : Nat) = aPos + 2 * k + 2 := by
    rw [hc5, h5h]
    simp only [Configuration.moveHead, dif_pos (show (c4.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have hcfg1 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c k = c1 := hc1.symm
  have hcfg2 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c (k + 1) = c2 := by
    rw [TM.runConfig_succ, hcfg1, ← hc2]
  have hcfg3 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c (k + 1 + k) = c3 := by
    rw [TM.runConfig_add, hcfg2, ← hc3]
  have hcfg4 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c (k + 1 + k + 1) = c4 := by
    rw [TM.runConfig_succ, hcfg3, ← hc4]
  have hcfg5 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c (k + 1 + k + 2) = c5 := by
    rw [show k + 1 + k + 2 = k + 1 + k + 1 + 1 from by omega,
      TM.runConfig_succ, hcfg4, ← hc5]
  intro s hs
  by_cases hA : s < k
  · obtain ⟨hrp, hrh, _⟩ := valuePush_run_walkR1 22 (by omega) rfl c hphase s
      (by omega)
      (fun p hp1 hp2 => by
        exact hdst p (by omega) (by omega))
    exact ⟨by omega, by omega⟩
  by_cases hB : s = k
  · subst hB
    rw [hcfg1]
    exact ⟨by omega, by omega⟩
  by_cases hC : s < k + 1 + k
  · obtain ⟨hrp, hrh, _⟩ := valuePush_run_scanR0 23 (by omega) rfl c2 h2p (s - (k + 1))
      (by omega)
      (fun p hp1 hp2 => by
        rw [h2t' p, if_neg (by omega)]
        exact hgap p (by omega) (by omega))
    rw [show s = (k + 1) + (s - (k + 1)) from by omega, TM.runConfig_add, hcfg2]
    exact ⟨by omega, by omega⟩
  by_cases hD : s = k + 1 + k
  · subst hD
    rw [hcfg3]
    exact ⟨by omega, by omega⟩
  by_cases hE : s = k + 1 + k + 1
  · subst hE
    rw [hcfg4]
    exact ⟨by omega, by omega⟩
  -- s = 2k + 3 (φ25 on the empty zone, the park hand-off step)
  · have hF : s = k + 1 + k + 2 := by omega
    subst hF
    rw [hcfg5]
    exact ⟨by omega, by omega⟩

set_option maxHeartbeats 4000000 in
/-- **Empty-source prologue confinement** (`k = 0`): along the `aPos − opBase + 2` steps the phase
never reaches the accept and the head stays ≤ `aPos + 2` — additive companion to
`valuePush_prologue_k0`. -/
theorem valuePush_prologue_k0_confined {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (opBase aPos : Nat) (hlay : ValuePushLayout c opBase aPos 0) :
    ∀ s : Nat, s < aPos - opBase + 2 →
      (((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).state).fst : Nat) ≠ 34
      ∧ ((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).head : Nat)
          ≤ aPos + 2 * 0 + 2 := by
  obtain ⟨hphase, hhead, hgeom, hbound, hzeroL, hanchor, hsrc, hzeroR⟩ := hlay
  obtain ⟨h1p, h1h, h1t⟩ := valuePush_step c (valuePush_state_eta c (by omega) hphase)
    (valuePushProgram_t0 (c.tape c.head))
  set c1 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c with hc1
  have h1p' : ((c1.state).fst : Nat) = 1 := h1p
  have h1h' : (c1.head : Nat) = opBase + 1 := by
    rw [hc1, h1h]
    simp only [Configuration.moveHead, dif_pos (show (c.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have h1t' : c1.tape = c.tape := by
    rw [hc1, h1t, write_self_eq]
  obtain ⟨h2p, h2h, h2t⟩ := valuePush_step c1 (valuePush_state_eta c1 (by omega) h1p)
    (valuePushProgram_t1 (c1.tape c1.head))
  set c2 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c1 with hc2
  have h2p' : ((c2.state).fst : Nat) = 2 := h2p
  have h2h' : (c2.head : Nat) = opBase + 2 := by
    rw [hc2, h2h]
    simp only [Configuration.moveHead, dif_pos (show (c1.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have h2t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c2.tape p = if (p : Nat) = opBase + 1 then true else c.tape p := by
    intro p
    rw [hc2, h2t, valuePush_write_char c1 true h1h' p, h1t']
  obtain ⟨h3p, h3h, h3t⟩ := valuePush_step c2 (valuePush_state_eta c2 (by omega) h2p)
    (valuePushProgram_t2 (c2.tape c2.head))
  set c3 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c2 with hc3
  have h3p' : ((c3.state).fst : Nat) = 3 := h3p
  have h3h' : (c3.head : Nat) = opBase + 3 := by
    rw [hc3, h3h]
    simp only [Configuration.moveHead, dif_pos (show (c2.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have h3t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c3.tape p = if (p : Nat) = opBase + 2 then true
        else if (p : Nat) = opBase + 1 then true else c.tape p := by
    intro p
    rw [hc3, h3t, valuePush_write_char c2 true h2h' p, h2t' p]
  have hcfg1 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c 1 = c1 := by
    rw [valuePush_runConfig_one, ← hc1]
  have hcfg2 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c 2 = c2 := by
    rw [show (2 : Nat) = 1 + 1 from rfl, TM.runConfig_add, hcfg1,
      valuePush_runConfig_one, ← hc2]
  have hcfg3 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c 3 = c3 := by
    rw [show (3 : Nat) = 2 + 1 from rfl, TM.runConfig_add, hcfg2,
      valuePush_runConfig_one, ← hc3]
  intro s hs
  by_cases hs0 : s = 0
  · subst hs0
    rw [TM.runConfig_zero]
    exact ⟨by omega, by omega⟩
  by_cases hs1 : s = 1
  · subst hs1
    rw [hcfg1]
    exact ⟨by omega, by omega⟩
  by_cases hs2 : s = 2
  · subst hs2
    rw [hcfg2]
    exact ⟨by omega, by omega⟩
  have hs3 : 3 ≤ s := by omega
  by_cases hslast : s = aPos - opBase + 1
  · obtain ⟨h4p, h4h, h4t⟩ := valuePush_run_scanR0 3 (by omega) rfl c3 h3p
      (aPos - opBase - 3)
      (by omega)
      (fun p hp1 hp2 => by
        rw [h3t' p, if_neg (by omega), if_neg (by omega)]
        exact hzeroL p (by omega) (by omega))
    set c4 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c3 (aPos - opBase - 3) with hc4
    have h4h' : (c4.head : Nat) = aPos := by omega
    have hb4 : c4.tape c4.head = true := by
      rw [h4t, h3t' c4.head, if_neg (by omega), if_neg (by omega)]
      exact hanchor c4.head (by omega)
    obtain ⟨h5p, h5h, _⟩ := valuePush_step c4 (valuePush_state_eta c4 (by omega) h4p)
      (by rw [hb4]; exact valuePushProgram_t3_one)
    set c5 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c4 with hc5
    have h5p' : ((c5.state).fst : Nat) = 4 := h5p
    have h5h' : (c5.head : Nat) = aPos + 1 := by
      rw [hc5, h5h]
      simp only [Configuration.moveHead, dif_pos (show (c4.head : Nat) + 1
        < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
      omega
    have hcfg4 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c (aPos - opBase) = c4 := by
      rw [show aPos - opBase = 3 + (aPos - opBase - 3) from by omega, TM.runConfig_add, hcfg3,
        ← hc4]
    have hcfg5 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c (aPos - opBase + 1)
        = c5 := by
      rw [TM.runConfig_succ, hcfg4, ← hc5]
    rw [hslast, hcfg5]
    exact ⟨by omega, by omega⟩
  · have hsr : s = 3 + (s - 3) := by omega
    obtain ⟨hrp, hrh, _⟩ := valuePush_run_scanR0 3 (by omega) rfl c3 h3p
      (s - 3)
      (by omega)
      (fun p hp1 hp2 => by
        rw [h3t' p, if_neg (by omega), if_neg (by omega)]
        exact hzeroL p (by omega) (by omega))
    rw [hsr, TM.runConfig_add, hcfg3]
    exact ⟨by omega, by omega⟩

set_option maxHeartbeats 4000000 in
/-- **Park-chain confinement**: along the `(p0 − aPos − k) + (aPos − opBase) + k + 2` steps the
phase never reaches the accept and the head stays ≤ `p0` — additive companion to
`valuePush_park` (the accept is entered only at the final step). -/
theorem valuePush_park_confined {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (opBase aPos k p0 : Nat) (hpr : ParkReady c opBase aPos k p0) :
    ∀ s : Nat, s < (p0 - aPos - k) + (aPos - opBase) + k + 2 →
      (((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).state).fst : Nat) ≠ 34
      ∧ ((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).head : Nat) ≤ p0 := by
  obtain ⟨hphase, hhead, hp0l, hp0r, hgeom, hbound, hhome, hentry, hgapL, hblk, hz⟩ := hpr
  obtain ⟨h1p, h1h, h1t⟩ := valuePush_run_scanL0 30 (by omega) rfl c hphase
    (p0 - aPos - k)
    (by omega)
    (fun p hp1 hp2 => by
      exact hz p (by omega) (by omega))
  set c1 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c (p0 - aPos - k) with hc1
  have h1h' : (c1.head : Nat) = aPos + k := by omega
  have hb1 : c1.tape c1.head = true := by
    rw [h1t]
    exact hblk c1.head (by omega) (by omega)
  obtain ⟨h2p, h2h, h2t⟩ := valuePush_step c1 (valuePush_state_eta c1 (by omega) h1p)
    (by rw [hb1]; exact valuePushProgram_t30_one)
  set c2 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c1 with hc2
  have h2p' : ((c2.state).fst : Nat) = 31 := h2p
  have h2h' : (c2.head : Nat) = aPos + k - 1 := by
    rw [hc2, h2h, Configuration.moveHead_left_val_of_pos c1 (by omega)]
    omega
  have hwf1 : c1.write c1.head true = c1.tape := by
    rw [← hb1]; exact write_self_eq c1
  have h2t' : c2.tape = c.tape := by
    rw [hc2, h2t, hwf1, h1t]
  obtain ⟨h3p, h3h, h3t⟩ := valuePush_run_walkL1 31 (by omega) rfl c2 h2p k
    (by omega)
    (fun p hp1 hp2 => by
      rw [h2t']
      exact hblk p (by omega) (by omega))
  set c3 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c2 k with hc3
  have h3h' : (c3.head : Nat) = aPos - 1 := by omega
  have hb3 : c3.tape c3.head = false := by
    rw [h3t, h2t']
    exact hgapL c3.head (by omega) (by omega)
  obtain ⟨h4p, h4h, h4t⟩ := valuePush_step c3 (valuePush_state_eta c3 (by omega) h3p)
    (by rw [hb3]; exact valuePushProgram_t31_zero)
  set c4 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c3 with hc4
  have h4p' : ((c4.state).fst : Nat) = 32 := h4p
  have h4h' : (c4.head : Nat) = aPos - 1 := by
    rw [hc4, h4h, Configuration.moveHead_stay]
    exact h3h'
  have hwf3 : c3.write c3.head false = c3.tape := by
    rw [← hb3]; exact write_self_eq c3
  have h4t' : c4.tape = c.tape := by
    rw [hc4, h4t, hwf3, h3t, h2t']
  obtain ⟨h5p, h5h, h5t⟩ := valuePush_run_scanL0 32 (by omega) rfl c4 h4p
    (aPos - opBase - k - 3)
    (by omega)
    (fun p hp1 hp2 => by
      rw [h4t']
      exact hgapL p (by omega) (by omega))
  set c5 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c4 (aPos - opBase - k - 3)
    with hc5
  have h5h' : (c5.head : Nat) = opBase + 2 + k := by omega
  have hb5 : c5.tape c5.head = true := by
    rw [h5t, h4t']
    exact hentry c5.head (by omega) (by omega)
  obtain ⟨h6p, h6h, h6t⟩ := valuePush_step c5 (valuePush_state_eta c5 (by omega) h5p)
    (by rw [hb5]; exact valuePushProgram_t32_one)
  set c6 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c5 with hc6
  have h6p' : ((c6.state).fst : Nat) = 33 := h6p
  have h6h' : (c6.head : Nat) = opBase + 1 + k := by
    rw [hc6, h6h, Configuration.moveHead_left_val_of_pos c5 (by omega)]
    omega
  have hwf5 : c5.write c5.head true = c5.tape := by
    rw [← hb5]; exact write_self_eq c5
  have h6t' : c6.tape = c.tape := by
    rw [hc6, h6t, hwf5, h5t, h4t']
  obtain ⟨h7p, h7h, h7t⟩ := valuePush_run_walkL1 33 (by omega) rfl c6 h6p (k + 1)
    (by omega)
    (fun p hp1 hp2 => by
      rw [h6t']
      exact hentry p (by omega) (by omega))
  set c7 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c6 (k + 1) with hc7
  have h7h' : (c7.head : Nat) = opBase := by omega
  have hcfg1 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c (p0 - aPos - k) = c1 :=
    hc1.symm
  have hcfg2 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c (p0 - aPos - k + 1)
      = c2 := by
    rw [TM.runConfig_succ, hcfg1, ← hc2]
  have hcfg3 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c (p0 - aPos - k + 1 + k)
      = c3 := by
    rw [TM.runConfig_add, hcfg2, ← hc3]
  have hcfg4 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c (p0 - aPos - k + 1 + k + 1)
      = c4 := by
    rw [TM.runConfig_succ, hcfg3, ← hc4]
  have hcfg5 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c
      (p0 - aPos - k + 1 + k + 1 + (aPos - opBase - k - 3)) = c5 := by
    rw [TM.runConfig_add, hcfg4, ← hc5]
  have hcfg6 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c
      (p0 - aPos - k + 1 + k + 1 + (aPos - opBase - k - 3) + 1) = c6 := by
    rw [TM.runConfig_succ, hcfg5, ← hc6]
  intro s hs
  by_cases hA : s < p0 - aPos - k
  · obtain ⟨hrp, hrh, _⟩ := valuePush_run_scanL0 30 (by omega) rfl c hphase s
      (by omega)
      (fun p hp1 hp2 => by
        exact hz p (by omega) (by omega))
    exact ⟨by omega, by omega⟩
  by_cases hB : s = p0 - aPos - k
  · subst hB
    rw [hcfg1]
    exact ⟨by omega, by omega⟩
  by_cases hC : s < p0 - aPos - k + 1 + k
  · obtain ⟨hrp, hrh, _⟩ := valuePush_run_walkL1 31 (by omega) rfl c2 h2p
      (s - (p0 - aPos - k + 1))
      (by omega)
      (fun p hp1 hp2 => by
        rw [h2t']
        exact hblk p (by omega) (by omega))
    rw [show s = (p0 - aPos - k + 1) + (s - (p0 - aPos - k + 1)) from by omega,
      TM.runConfig_add, hcfg2]
    exact ⟨by omega, by omega⟩
  by_cases hD : s = p0 - aPos - k + 1 + k
  · subst hD
    rw [hcfg3]
    exact ⟨by omega, by omega⟩
  by_cases hE : s < p0 - aPos - k + 1 + k + 1 + (aPos - opBase - k - 3)
  · obtain ⟨hrp, hrh, _⟩ := valuePush_run_scanL0 32 (by omega) rfl c4 h4p
      (s - (p0 - aPos - k + 1 + k + 1))
      (by omega)
      (fun p hp1 hp2 => by
        rw [h4t']
        exact hgapL p (by omega) (by omega))
    rw [show s = (p0 - aPos - k + 1 + k + 1) + (s - (p0 - aPos - k + 1 + k + 1)) from by omega,
      TM.runConfig_add, hcfg4]
    exact ⟨by omega, by omega⟩
  by_cases hF : s = p0 - aPos - k + 1 + k + 1 + (aPos - opBase - k - 3)
  · subst hF
    rw [hcfg5]
    exact ⟨by omega, by omega⟩
  -- φ33 entry walk left, r := s − (… + 1) ≤ k + 1
  · obtain ⟨hrp, hrh, _⟩ := valuePush_run_walkL1 33 (by omega) rfl c6 h6p
      (s - (p0 - aPos - k + 1 + k + 1 + (aPos - opBase - k - 3) + 1))
      (by omega)
      (fun p hp1 hp2 => by
        rw [h6t']
        exact hentry p (by omega) (by omega))
    rw [show s = (p0 - aPos - k + 1 + k + 1 + (aPos - opBase - k - 3) + 1)
        + (s - (p0 - aPos - k + 1 + k + 1 + (aPos - opBase - k - 3) + 1)) from by omega,
      TM.runConfig_add, hcfg6]
    exact ⟨by omega, by omega⟩

/-- **The drain loop, discharged**: from any `DrainState e` the machine reaches the restore HOME
(`CloneState 0`) within `(k−e)·(2·(aPos−opBase)+2·k+3) + 2·(aPos−opBase)+k+1` steps. -/
theorem valuePush_drain_all {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (opBase aPos k e : Nat) (hds : DrainState c opBase aPos k e) (hk : 0 < k) :
    ∃ t ≤ (k - e) * (2 * (aPos - opBase) + 2 * k + 3) + (2 * (aPos - opBase) + k + 1),
      CloneState (TM.runConfig (M := valuePushProgram.toPhased.toTM) c t) opBase aPos k 0
      ∧ (∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
          ((p : Nat) < opBase ∨ aPos + 2 * k + 2 < (p : Nat)) →
          (TM.runConfig (M := valuePushProgram.toPhased.toTM) c t).tape p = c.tape p)
      ∧ ∀ s : Nat, s < t →
          (((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).state).fst : Nat) ≠ 34
          ∧ ((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).head : Nat)
              ≤ aPos + 2 * k + 2 := by
  suffices H : ∀ n (c : Configuration (M := valuePushProgram.toPhased.toTM) L) (e : Nat),
      DrainState c opBase aPos k e → k - e = n →
      ∃ t ≤ (k - e) * (2 * (aPos - opBase) + 2 * k + 3) + (2 * (aPos - opBase) + k + 1),
        CloneState (TM.runConfig (M := valuePushProgram.toPhased.toTM) c t) opBase aPos k 0
        ∧ (∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
            ((p : Nat) < opBase ∨ aPos + 2 * k + 2 < (p : Nat)) →
            (TM.runConfig (M := valuePushProgram.toPhased.toTM) c t).tape p = c.tape p)
        ∧ ∀ s : Nat, s < t →
            (((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).state).fst : Nat) ≠ 34
            ∧ ((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).head : Nat)
                ≤ aPos + 2 * k + 2 by
    exact H (k - e) c e hds rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c e hds hn
    have he := hds.he
    by_cases hlast : e + 1 = k
    · -- the final round
      have hds' : DrainState c opBase aPos k (k - 1) := by
        have : e = k - 1 := by omega
        rwa [this] at hds
      obtain ⟨hCS, hOut⟩ := valuePush_drain_final c opBase aPos k hds' hk
      have hgeom := hds'.hgeom
      refine ⟨2 * (aPos - opBase) + k + 1, by omega, hCS, hOut, ?_⟩
      intro s hs
      by_cases hsA : s < 2 * k + 2
      · exact valuePush_drain_final_A_confined c opBase aPos k hds' hk s hsA
      · obtain ⟨hcut, _⟩ := valuePush_drain_final_A c opBase aPos k hds' hk
        have hback := valuePush_drain_final_B_confined _ opBase aPos k hcut
          (s - (2 * k + 2)) (by omega)
        rw [show s = (2 * k + 2) + (s - (2 * k + 2)) from by omega, TM.runConfig_add]
        exact hback
    · -- a mid round, then the induction hypothesis
      have he2 : e + 1 < k := by omega
      obtain ⟨hds', hOut1⟩ := valuePush_drain_mid c opBase aPos k e hds he2
      set c' := TM.runConfig (M := valuePushProgram.toPhased.toTM) c
        (2 * (aPos - opBase) + 2 * k + 3) with hc'
      obtain ⟨t', ht'le, hCS, hOut', hsafe'⟩ := ih (k - (e + 1)) (by omega) c' (e + 1) hds' rfl
      refine ⟨(2 * (aPos - opBase) + 2 * k + 3) + t', ?_, ?_, ?_, ?_⟩
      · have h2 : k - e = (k - (e + 1)) + 1 := by omega
        have hs : ((k - (e + 1)) + 1) * (2 * (aPos - opBase) + 2 * k + 3)
            = (k - (e + 1)) * (2 * (aPos - opBase) + 2 * k + 3)
              + (2 * (aPos - opBase) + 2 * k + 3) := Nat.succ_mul _ _
        rw [h2, hs]
        omega
      · rw [TM.runConfig_add, ← hc']
        exact hCS
      · intro p hp
        rw [TM.runConfig_add, ← hc', hOut' p hp]
        exact hOut1 p hp
      · intro s hs
        by_cases hsA : s < 2 * (aPos - opBase) + 2 * k + 3
        · exact valuePush_drain_mid_confined c opBase aPos k e hds he2 s hsA
        · have hrest := hsafe' (s - (2 * (aPos - opBase) + 2 * k + 3)) (by omega)
          rw [show s = (2 * (aPos - opBase) + 2 * k + 3)
              + (s - (2 * (aPos - opBase) + 2 * k + 3)) from by omega,
            TM.runConfig_add, ← hc']
          exact hrest

/-- **The restore loop, discharged**: from any `CloneState j` the machine reaches the park entry
within `(k−j)·(4·k+12) + 2·k+4` steps. -/
theorem valuePush_clone_all {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (opBase aPos k j : Nat) (hcs : CloneState c opBase aPos k j) (hjk : j < k) :
    ∃ t ≤ (k - j) * (4 * k + 12) + (2 * k + 4),
      ParkReady (TM.runConfig (M := valuePushProgram.toPhased.toTM) c t) opBase aPos k
        (aPos + 2 * k + 1)
      ∧ (∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
          ((p : Nat) < opBase ∨ aPos + 2 * k + 2 < (p : Nat)) →
          (TM.runConfig (M := valuePushProgram.toPhased.toTM) c t).tape p = c.tape p)
      ∧ ∀ s : Nat, s < t →
          (((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).state).fst : Nat) ≠ 34
          ∧ ((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).head : Nat)
              ≤ aPos + 2 * k + 2 := by
  suffices H : ∀ n (c : Configuration (M := valuePushProgram.toPhased.toTM) L) (j : Nat),
      CloneState c opBase aPos k j → j < k → k - j = n →
      ∃ t ≤ (k - j) * (4 * k + 12) + (2 * k + 4),
        ParkReady (TM.runConfig (M := valuePushProgram.toPhased.toTM) c t) opBase aPos k
          (aPos + 2 * k + 1)
        ∧ (∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
            ((p : Nat) < opBase ∨ aPos + 2 * k + 2 < (p : Nat)) →
            (TM.runConfig (M := valuePushProgram.toPhased.toTM) c t).tape p = c.tape p)
        ∧ ∀ s : Nat, s < t →
            (((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).state).fst : Nat) ≠ 34
            ∧ ((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).head : Nat)
                ≤ aPos + 2 * k + 2 by
    exact H (k - j) c j hcs hjk rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c j hcs hjk hn
    by_cases hlast : j + 1 = k
    · have hcs' : CloneState c opBase aPos k (k - 1) := by
        have : j = k - 1 := by omega
        rwa [this] at hcs
      obtain ⟨hPR, hOut⟩ := valuePush_clone_last c opBase aPos k hcs' (by omega)
      refine ⟨2 * k + 4, by omega, hPR, hOut, ?_⟩
      intro s hs
      exact valuePush_clone_last_confined c opBase aPos k hcs' (by omega) s hs
    · have hj2 : j + 1 < k := by omega
      obtain ⟨hcs', hOut1⟩ := valuePush_clone_mid c opBase aPos k j hcs hj2
      set c' := TM.runConfig (M := valuePushProgram.toPhased.toTM) c
        (2 * j + 2 * k + 12) with hc'
      obtain ⟨t', ht'le, hPR, hOut', hsafe'⟩ := ih (k - (j + 1)) (by omega) c' (j + 1) hcs' hj2 rfl
      refine ⟨(2 * j + 2 * k + 12) + t', ?_, ?_, ?_, ?_⟩
      · have h2 : k - j = (k - (j + 1)) + 1 := by omega
        have hs : ((k - (j + 1)) + 1) * (4 * k + 12)
            = (k - (j + 1)) * (4 * k + 12) + (4 * k + 12) := Nat.succ_mul _ _
        rw [h2, hs]
        omega
      · rw [TM.runConfig_add, ← hc']
        exact hPR
      · intro p hp
        rw [TM.runConfig_add, ← hc', hOut' p hp]
        exact hOut1 p hp
      · intro s hs
        by_cases hsA : s < 2 * j + 2 * k + 12
        · exact valuePush_clone_mid_confined c opBase aPos k j hcs hj2 s hsA
        · have hrest := hsafe' (s - (2 * j + 2 * k + 12)) (by omega)
          rw [show s = (2 * j + 2 * k + 12) + (s - (2 * j + 2 * k + 12)) from by omega,
            TM.runConfig_add, ← hc']
          exact hrest

set_option maxHeartbeats 1000000 in
/-- **The M1 headline (§12, A5m-V).**  From a `ValuePushLayout` — source `1^k` anchored at `aPos`
with an all-zero entry/gap/scratch neighbourhood — the machine reaches its accept phase within
`(k+2)·(2·(aPos−opBase)+6·k+20)` steps, with the head back at HOME and the tape changed **exactly**
by the freshly minted value entry: `true` on `[opBase+1, opBase+3+k)` (the `1^(k+2)` of
`encodeNatEntryR k`, whose leading `0` is the untouched `opBase` cell), and **unchanged everywhere
else** — in particular the source block is intact. -/
theorem valuePush_pushes {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (opBase aPos k : Nat) (hlay : ValuePushLayout c opBase aPos k) :
    ∃ t ≤ (k + 2) * (2 * (aPos - opBase) + 6 * k + 20),
      (((TM.runConfig (M := valuePushProgram.toPhased.toTM) c t).state).fst : Nat) = 34
      ∧ ((TM.runConfig (M := valuePushProgram.toPhased.toTM) c t).head : Nat) = opBase
      ∧ (∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
          (TM.runConfig (M := valuePushProgram.toPhased.toTM) c t).tape p
            = if opBase + 1 ≤ (p : Nat) ∧ (p : Nat) < opBase + 3 + k then true
              else c.tape p)
      ∧ ∀ s : Nat, s < t →
          (((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).state).fst : Nat) ≠ 34
          ∧ ((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).head : Nat)
              ≤ aPos + 2 * k + 2 := by
  have hgeom := hlay.hgeom
  have hzeroL := hlay.hzeroL
  have hanchor := hlay.hanchor
  have hsrc := hlay.hsrc
  have hzeroR := hlay.hzeroR
  by_cases hk : 0 < k
  · -- k ≥ 1: prologue, drain, restore, park
    obtain ⟨hds, hOutP⟩ := valuePush_prologue c opBase aPos k hlay hk
    set c1 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c (aPos - opBase + 2)
      with hc1
    obtain ⟨t1, ht1, hCS, hOutD, hsafeD⟩ := valuePush_drain_all c1 opBase aPos k 0 hds hk
    set c2 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c1 t1 with hc2
    obtain ⟨t2, ht2, hPR, hOutC, hsafeC⟩ := valuePush_clone_all c2 opBase aPos k 0 hCS hk
    set c3 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c2 t2 with hc3
    obtain ⟨hp4, hh4, ht4⟩ := valuePush_park c3 opBase aPos k (aPos + 2 * k + 1) hPR
    refine ⟨(aPos - opBase + 2) + (t1 + (t2 + ((aPos + 2 * k + 1 - aPos - k)
      + (aPos - opBase) + k + 2))), ?_, ?_, ?_, ?_, ?_⟩
    · have hk0 : k - 0 = k := by omega
      rw [hk0] at ht1 ht2
      have hb1 : t1 ≤ k * (2 * (aPos - opBase)) + 2 * (k * k) + 3 * k
          + (2 * (aPos - opBase) + k + 1) := by
        calc t1 ≤ k * (2 * (aPos - opBase) + 2 * k + 3)
              + (2 * (aPos - opBase) + k + 1) := ht1
          _ = k * (2 * (aPos - opBase)) + 2 * (k * k) + 3 * k
              + (2 * (aPos - opBase) + k + 1) := by ring
      have hb2 : t2 ≤ 4 * (k * k) + 12 * k + (2 * k + 4) := by
        calc t2 ≤ k * (4 * k + 12) + (2 * k + 4) := ht2
          _ = 4 * (k * k) + 12 * k + (2 * k + 4) := by ring
      have hrhs : (k + 2) * (2 * (aPos - opBase) + 6 * k + 20)
          = k * (2 * (aPos - opBase)) + 6 * (k * k) + 20 * k
            + (4 * (aPos - opBase) + 12 * k + 40) := by ring
      rw [hrhs]
      omega
    · rw [TM.runConfig_add, ← hc1, TM.runConfig_add, ← hc2, TM.runConfig_add, ← hc3]
      exact hp4
    · rw [TM.runConfig_add, ← hc1, TM.runConfig_add, ← hc2, TM.runConfig_add, ← hc3]
      exact hh4
    · rw [TM.runConfig_add, ← hc1, TM.runConfig_add, ← hc2, TM.runConfig_add, ← hc3]
      intro p
      rw [ht4]
      by_cases hin : opBase + 1 ≤ (p : Nat) ∧ (p : Nat) < opBase + 3 + k
      · rw [if_pos hin]
        exact hPR.hentry p hin.1 hin.2
      · rw [if_neg hin]
        by_cases hout : (p : Nat) < opBase ∨ aPos + 2 * k + 2 < (p : Nat)
        · rw [hOutC p hout, hOutD p hout, hc1, hOutP p (by omega)]
        · -- inside the zone but outside the entry: reconstruct from the restored windows
          by_cases hq1 : (p : Nat) = opBase
          · rw [hPR.hhome p hq1]
            exact (hzeroL p (by omega) (by omega)).symm
          · by_cases hq2 : opBase + 3 + k ≤ (p : Nat) ∧ (p : Nat) < aPos
            · rw [hPR.hgapL p hq2.1 hq2.2]
              exact (hzeroL p (by omega) (by omega)).symm
            · by_cases hq3 : (p : Nat) = aPos
              · rw [hPR.hblk p (by omega) (by omega)]
                exact (hanchor p hq3).symm
              · by_cases hq4 : aPos < (p : Nat) ∧ (p : Nat) ≤ aPos + k
                · rw [hPR.hblk p (by omega) (by omega)]
                  exact (hsrc p hq4.1 hq4.2).symm
                · rw [hPR.hz p (by omega) (by omega)]
                  exact (hzeroR p (by omega) (by omega)).symm
    · -- the safety stream: prologue ∪ drain ∪ restore ∪ park, at the round offsets
      intro s hs
      by_cases hsP : s < aPos - opBase + 2
      · exact valuePush_prologue_confined c opBase aPos k hlay hk s hsP
      · by_cases hsD : s < (aPos - opBase + 2) + t1
        · have hstep := hsafeD (s - (aPos - opBase + 2)) (by omega)
          rw [show s = (aPos - opBase + 2) + (s - (aPos - opBase + 2)) from by omega,
            TM.runConfig_add, ← hc1]
          exact hstep
        · by_cases hsC : s < (aPos - opBase + 2) + t1 + t2
          · have hstep := hsafeC (s - ((aPos - opBase + 2) + t1)) (by omega)
            rw [show s = ((aPos - opBase + 2) + t1) + (s - ((aPos - opBase + 2) + t1))
                from by omega,
              TM.runConfig_add, TM.runConfig_add, ← hc1, ← hc2]
            exact hstep
          · have hstep := valuePush_park_confined c3 opBase aPos k (aPos + 2 * k + 1) hPR
              (s - ((aPos - opBase + 2) + t1 + t2)) (by omega)
            rw [show s = ((aPos - opBase + 2) + t1 + t2)
                + (s - ((aPos - opBase + 2) + t1 + t2)) from by omega,
              TM.runConfig_add, TM.runConfig_add, TM.runConfig_add, ← hc1, ← hc2, ← hc3]
            exact ⟨hstep.1, by have := hstep.2; omega⟩
  · -- k = 0: prologue straight to the park chain
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hPR, hOutP⟩ := valuePush_prologue_k0 c opBase aPos hlay
    set c1 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c (aPos - opBase + 2)
      with hc1
    obtain ⟨hp4, hh4, ht4⟩ := valuePush_park c1 opBase aPos 0 (aPos + 1) hPR
    refine ⟨(aPos - opBase + 2) + ((aPos + 1 - aPos - 0) + (aPos - opBase) + 0 + 2),
      by omega, ?_, ?_, ?_, ?_⟩
    · rw [TM.runConfig_add, ← hc1]
      exact hp4
    · rw [TM.runConfig_add, ← hc1]
      exact hh4
    · rw [TM.runConfig_add, ← hc1]
      intro p
      rw [ht4]
      by_cases hin : opBase + 1 ≤ (p : Nat) ∧ (p : Nat) < opBase + 3 + 0
      · rw [if_pos hin]
        exact hPR.hentry p hin.1 hin.2
      · rw [if_neg hin]
        exact hOutP p (by omega)
    · -- the safety stream: the k = 0 prologue ∪ park
      intro s hs
      by_cases hsP : s < aPos - opBase + 2
      · exact valuePush_prologue_k0_confined c opBase aPos hlay s hsP
      · have hstep := valuePush_park_confined c1 opBase aPos 0 (aPos + 1) hPR
          (s - (aPos - opBase + 2)) (by omega)
        rw [show s = (aPos - opBase + 2) + (s - (aPos - opBase + 2)) from by omega,
          TM.runConfig_add, ← hc1]
        exact ⟨hstep.1, by have := hstep.2; omega⟩

end ContractExpansion
end Frontier
end Pnp4

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- **The M1 headline in the §12.3 contract shape**: the final tape **is**
`writeBlockTape c.tape opBase (encodeNatEntryR k)` — the value entry `0 ++ 1^(k+2)` written at the
value-zone top (its leading `0` coincides with the layout's untouched `opBase` cell), everything
else verbatim.  This is the tape transformer the leaf/pop keystones consume. -/
theorem valuePush_pushes_writeBlock {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (opBase aPos k : Nat) (hlay : ValuePushLayout c opBase aPos k) :
    ∃ t ≤ (k + 2) * (2 * (aPos - opBase) + 6 * k + 20),
      (((TM.runConfig (M := valuePushProgram.toPhased.toTM) c t).state).fst : Nat) = 34
      ∧ ((TM.runConfig (M := valuePushProgram.toPhased.toTM) c t).head : Nat) = opBase
      ∧ (TM.runConfig (M := valuePushProgram.toPhased.toTM) c t).tape
          = writeBlockTape c.tape opBase (encodeNatEntryR k)
      ∧ ∀ s : Nat, s < t →
          (((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).state).fst : Nat) ≠ 34
          ∧ ((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).head : Nat)
              ≤ aPos + 2 * k + 2 := by
  obtain ⟨t, ht, hp, hh, htape, hsafe⟩ := valuePush_pushes c opBase aPos k hlay
  have hgeom := hlay.hgeom
  refine ⟨t, ht, hp, hh, funext fun p => ?_, hsafe⟩
  rw [htape p]
  unfold writeBlockTape
  have hlen : (encodeNatEntryR k).length = k + 3 := encodeNatEntryR_length k
  by_cases hin : opBase + 1 ≤ (p : Nat) ∧ (p : Nat) < opBase + 3 + k
  · rw [if_pos hin, if_pos (by omega)]
    -- the written cell is one of the k+2 ones of the entry
    obtain ⟨i, hi⟩ : ∃ i, (p : Nat) - opBase = i + 1 := ⟨(p : Nat) - opBase - 1, by omega⟩
    rw [hi]
    show true = (false :: List.replicate (k + 2) true).getD (i + 1) false
    rw [List.getD_cons_succ]
    have hilt : i < k + 2 := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hilt]
    rfl
  · rw [if_neg hin]
    by_cases hbase : (p : Nat) = opBase
    · rw [if_pos (by omega)]
      have h0 : (p : Nat) - opBase = 0 := by omega
      rw [h0]
      show c.tape p = (false :: List.replicate (k + 2) true).getD 0 false
      rw [List.getD_cons_zero]
      exact hlay.hzeroL p (by omega) (by omega)
    · rw [if_neg (by omega)]

/-! ## Directed regression check: the layout is satisfiable

A concrete configuration (ambient length `20`, entry base `0`, anchor at `5`, a single source
unit) inhabits `ValuePushLayout` — the headline is not vacuous. -/

example : ∃ c : Configuration (M := valuePushProgram.toPhased.toTM) 20,
    ValuePushLayout c 0 5 1 := by
  refine ⟨⟨⟨⟨0, by decide⟩, ()⟩, ⟨0, by decide⟩,
    fun q => decide ((q : Nat) = 5 ∨ (q : Nat) = 6)⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · decide
  · decide
  · intro p hp1 hp2
    simp only [decide_eq_false_iff_not]
    omega
  · intro p hp
    simp only [decide_eq_true_eq]
    omega
  · intro p hp1 hp2
    simp only [decide_eq_true_eq]
    omega
  · intro p hp1 hp2
    simp only [decide_eq_false_iff_not]
    omega

end ContractExpansion
end Frontier
end Pnp4
