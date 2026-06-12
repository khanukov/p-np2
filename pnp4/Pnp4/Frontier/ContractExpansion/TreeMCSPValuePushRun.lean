import Pnp4.Frontier.ContractExpansion.TreeMCSPValuePushProgram

/-!
# `valuePushProgram` — the run behaviour and the M1 headline

Run lemmas for the value-push machine (`TreeMCSPValuePushProgram.lean`), culminating in the §12 M1
headline `valuePush_pushes`: from a `ValuePushLayout` (source `1^k`, anchored and `0`-terminated,
with an all-zero entry/gap/scratch neighbourhood), the machine reaches its accept phase with the
head back at HOME and the tape changed **exactly** by the freshly minted value entry —

> `tape′ p = true` on `[opBase+1, opBase+3+k)` and `tape′ p = c.tape p` everywhere else,

i.e. `tape′ = writeBlockTape c.tape opBase (encodeNatEntryR k)` (the source block is intact: drained
into the entry + scratch fan-out, then restored from the scratch by the cloned transfer loop).

Proof architecture (mirroring `TreeMCSPUnaryTransferRun.lean`): a generic single-step triple, four
phase-generic self-loop segment lemmas (scan/walk × left/right), exact walk-throughs of the
prologue, one mid drain round, the final drain round, one restore round (the `unaryTransferBody`
clone), and the park chain; two strong inductions (drain rounds, restore rounds) assemble the
headline.

**Progress classification (AGENTS.md): Infrastructure** — verifier machine component run lemmas;
builds no verifier and proves no separation.  Standard `[propext, Classical.choice, Quot.sound]`
triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-! ### The generic single-step triple -/

/-- One `stepConfig` of the compiled machine, fully characterized by the transition value. -/
theorem valuePush_step {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    {i : Fin 35} {s : Unit} (hstate : c.state = ⟨i, s⟩)
    {i' : Fin 35} {b' : Bool} {mv : Move}
    (htr : valuePushProgram.transition i s (c.tape c.head) = (i', (), b', mv)) :
    (((TM.stepConfig (M := valuePushProgram.toPhased.toTM) c).state).fst : Nat) = (i' : Nat)
    ∧ (TM.stepConfig (M := valuePushProgram.toPhased.toTM) c).head = c.moveHead mv
    ∧ (TM.stepConfig (M := valuePushProgram.toPhased.toTM) c).tape = c.write c.head b' := by
  refine ⟨?_, ?_, ?_⟩
  · rw [toTM_stepConfig_phase valuePushProgram c hstate, htr]
  · rw [toTM_stepConfig_head valuePushProgram c hstate, htr]
  · rw [toTM_stepConfig_tape valuePushProgram c hstate, htr]

/-- Recover the `Fin` phase from its value, for feeding the transition lemmas. -/
theorem valuePush_state_eta {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    {pv : Nat} (hlt : pv < 35) (hph : (c.state.fst : Nat) = pv) :
    c.state = ⟨(⟨pv, hlt⟩ : Fin 35), c.state.snd⟩ := by
  have h1 : c.state.fst = (⟨pv, hlt⟩ : Fin 35) := Fin.ext hph
  rw [← h1]
  rfl

/-! ### Phase-generic self-loop segments -/

section Segments

variable {L : Nat}

/-- Rightward zero-scan: a phase that self-loops on `0` writing it back and moving right crosses a
zero block leaving the tape unchanged. -/
theorem valuePush_run_scanR0 (pv : Nat) (hlt : pv < 35)
    (hself : valuePushProgram.transition ⟨pv, hlt⟩ () false
      = (⟨pv, hlt⟩, (), false, Move.right))
    (c0 : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = pv) :
    ∀ k : Nat, (c0.head : Nat) + k < valuePushProgram.toPhased.toTM.tapeLength L →
      (∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
        (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + k → c0.tape p = false) →
      (((TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 k).state).fst : Nat) = pv
      ∧ ((TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 k).head : Nat)
          = (c0.head : Nat) + k
      ∧ (TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 k).tape = c0.tape := by
  intro k
  induction k with
  | zero => intro _ _; exact ⟨hphase, by simp, rfl⟩
  | succ k ih =>
      intro hk h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h1 p hp1 (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 k with hc
      have hbit : c.tape c.head = false := by
        rw [htp]; exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      obtain ⟨hsp, hsh, hst⟩ := valuePush_step c (valuePush_state_eta c hlt hph)
        (by rw [hbit]; exact hself)
      have hbnd : (c.head : Nat) + 1 < valuePushProgram.toPhased.toTM.tapeLength L := by
        rw [hhd]; omega
      refine ⟨hsp, ?_, ?_⟩
      · rw [hsh]
        simp only [Configuration.moveHead, dif_pos hbnd]
        omega
      · rw [hst, ← hbit, write_self_eq, htp]

/-- Rightward one-walk: a phase that self-loops on `1` writing it back and moving right crosses a
one block leaving the tape unchanged. -/
theorem valuePush_run_walkR1 (pv : Nat) (hlt : pv < 35)
    (hself : valuePushProgram.transition ⟨pv, hlt⟩ () true
      = (⟨pv, hlt⟩, (), true, Move.right))
    (c0 : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = pv) :
    ∀ k : Nat, (c0.head : Nat) + k < valuePushProgram.toPhased.toTM.tapeLength L →
      (∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
        (c0.head : Nat) ≤ (p : Nat) → (p : Nat) < (c0.head : Nat) + k → c0.tape p = true) →
      (((TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 k).state).fst : Nat) = pv
      ∧ ((TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 k).head : Nat)
          = (c0.head : Nat) + k
      ∧ (TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 k).tape = c0.tape := by
  intro k
  induction k with
  | zero => intro _ _; exact ⟨hphase, by simp, rfl⟩
  | succ k ih =>
      intro hk h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h1 p hp1 (by omega))
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 k with hc
      have hbit : c.tape c.head = true := by
        rw [htp]; exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      obtain ⟨hsp, hsh, hst⟩ := valuePush_step c (valuePush_state_eta c hlt hph)
        (by rw [hbit]; exact hself)
      have hbnd : (c.head : Nat) + 1 < valuePushProgram.toPhased.toTM.tapeLength L := by
        rw [hhd]; omega
      refine ⟨hsp, ?_, ?_⟩
      · rw [hsh]
        simp only [Configuration.moveHead, dif_pos hbnd]
        omega
      · rw [hst, ← hbit, write_self_eq, htp]

/-- Leftward zero-scan: a phase that self-loops on `0` writing it back and moving left crosses a
zero block leaving the tape unchanged. -/
theorem valuePush_run_scanL0 (pv : Nat) (hlt : pv < 35)
    (hself : valuePushProgram.transition ⟨pv, hlt⟩ () false
      = (⟨pv, hlt⟩, (), false, Move.left))
    (c0 : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = pv) :
    ∀ k : Nat, k ≤ (c0.head : Nat) →
      (∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
        (c0.head : Nat) - k < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = false) →
      (((TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 k).state).fst : Nat) = pv
      ∧ ((TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 k).head : Nat)
          = (c0.head : Nat) - k
      ∧ (TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 k).tape = c0.tape := by
  intro k
  induction k with
  | zero => intro _ _; exact ⟨hphase, by simp, rfl⟩
  | succ k ih =>
      intro hk h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h1 p (by omega) hp2)
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 k with hc
      have hbit : c.tape c.head = false := by
        rw [htp]; exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      obtain ⟨hsp, hsh, hst⟩ := valuePush_step c (valuePush_state_eta c hlt hph)
        (by rw [hbit]; exact hself)
      have hpos : 0 < (c.head : Nat) := by rw [hhd]; omega
      refine ⟨hsp, ?_, ?_⟩
      · rw [hsh, Configuration.moveHead_left_val_of_pos c hpos, hhd]; omega
      · rw [hst, ← hbit, write_self_eq, htp]

/-- Leftward one-walk: a phase that self-loops on `1` writing it back and moving left crosses a
one block leaving the tape unchanged. -/
theorem valuePush_run_walkL1 (pv : Nat) (hlt : pv < 35)
    (hself : valuePushProgram.transition ⟨pv, hlt⟩ () true
      = (⟨pv, hlt⟩, (), true, Move.left))
    (c0 : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (hphase : (c0.state.fst : Nat) = pv) :
    ∀ k : Nat, k ≤ (c0.head : Nat) →
      (∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
        (c0.head : Nat) - k < (p : Nat) → (p : Nat) ≤ (c0.head : Nat) → c0.tape p = true) →
      (((TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 k).state).fst : Nat) = pv
      ∧ ((TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 k).head : Nat)
          = (c0.head : Nat) - k
      ∧ (TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 k).tape = c0.tape := by
  intro k
  induction k with
  | zero => intro _ _; exact ⟨hphase, by simp, rfl⟩
  | succ k ih =>
      intro hk h1
      obtain ⟨hph, hhd, htp⟩ := ih (by omega) (fun p hp1 hp2 => h1 p (by omega) hp2)
      rw [TM.runConfig_succ]
      set c := TM.runConfig (M := valuePushProgram.toPhased.toTM) c0 k with hc
      have hbit : c.tape c.head = true := by
        rw [htp]; exact h1 c.head (by rw [hhd]; omega) (by rw [hhd]; omega)
      obtain ⟨hsp, hsh, hst⟩ := valuePush_step c (valuePush_state_eta c hlt hph)
        (by rw [hbit]; exact hself)
      have hpos : 0 < (c.head : Nat) := by rw [hhd]; omega
      refine ⟨hsp, ?_, ?_⟩
      · rw [hsh, Configuration.moveHead_left_val_of_pos c hpos, hhd]; omega
      · rw [hst, ← hbit, write_self_eq, htp]

end Segments

/-- One step of `runConfig` is one `stepConfig`. -/
theorem valuePush_runConfig_one {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L) :
    TM.runConfig (M := valuePushProgram.toPhased.toTM) c 1
      = TM.stepConfig (M := valuePushProgram.toPhased.toTM) c := by
  have h := TM.runConfig_succ (M := valuePushProgram.toPhased.toTM) c 0
  simpa using h

end ContractExpansion
end Frontier
end Pnp4

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

/-- Pointwise characterization of a single tape write at a known head position. -/
theorem valuePush_write_char {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (b : Bool) {pos : Nat} (hpos : (c.head : Nat) = pos) :
    ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      (c.write c.head b) p = if (p : Nat) = pos then b else c.tape p := by
  intro p
  by_cases hp : p = c.head
  · subst hp
    rw [if_pos (by omega)]
    simp [Configuration.write]
  · have hv : (p : Nat) ≠ pos := by
      intro hv
      exact hp (Fin.ext (by omega))
    rw [if_neg hv]
    simp [Configuration.write, hp]

/-! ### The M1 layout and the loop-state predicates -/

/-- **The value-push layout** (see the program file's module docstring).  HOME at `opBase` (a `0`,
the entry delimiter); the future entry zone and gap₁ all `0` up to the permanent anchor `1` at
`aPos`; the source `1^k` on `(aPos, aPos+k]`; then the `0` terminator, the all-`0` scratch zone and
one more `0` cell, through `aPos + 2k + 2`. -/
structure ValuePushLayout {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (opBase aPos k : Nat) : Prop where
  hphase : (c.state.fst : Nat) = 0
  hhead : (c.head : Nat) = opBase
  hgeom : opBase + k + 4 ≤ aPos
  hbound : aPos + 2 * k + 3 ≤ valuePushProgram.toPhased.toTM.tapeLength L
  hzeroL : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    opBase ≤ (p : Nat) → (p : Nat) < aPos → c.tape p = false
  hanchor : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    (p : Nat) = aPos → c.tape p = true
  hsrc : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    aPos < (p : Nat) → (p : Nat) ≤ aPos + k → c.tape p = true
  hzeroR : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    aPos + k < (p : Nat) → (p : Nat) ≤ aPos + 2 * k + 2 → c.tape p = false

/-- **The drain-loop state** after `e` rounds: phase φ5 on the leftmost remaining unit, the entry
holding `2 + e` ones, the erased prefix `(aPos, aPos+1+e)`, the source rest, and `e` scratch ones. -/
structure DrainState {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (opBase aPos k e : Nat) : Prop where
  hphase : (c.state.fst : Nat) = 5
  hhead : (c.head : Nat) = aPos + 1 + e
  hgeom : opBase + k + 4 ≤ aPos
  hbound : aPos + 2 * k + 3 ≤ valuePushProgram.toPhased.toTM.tapeLength L
  he : e < k
  hhome : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    (p : Nat) = opBase → c.tape p = false
  hentry : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    opBase + 1 ≤ (p : Nat) → (p : Nat) < opBase + 3 + e → c.tape p = true
  hgapL : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    opBase + 3 + e ≤ (p : Nat) → (p : Nat) < aPos → c.tape p = false
  hanchor : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    (p : Nat) = aPos → c.tape p = true
  hpre : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    aPos < (p : Nat) → (p : Nat) < aPos + 1 + e → c.tape p = false
  hrest : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    aPos + 1 + e ≤ (p : Nat) → (p : Nat) < aPos + 1 + k → c.tape p = true
  hterm : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    (p : Nat) = aPos + 1 + k → c.tape p = false
  hscr : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    aPos + 2 + k ≤ (p : Nat) → (p : Nat) < aPos + 2 + k + e → c.tape p = true
  hzr : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
    aPos + 2 + k + e ≤ (p : Nat) → (p : Nat) ≤ aPos + 2 * k + 2 → c.tape p = false

/-! ### The prologue walk-through -/

/-- **Prologue** (`k ≥ 1`): from the layout, `aPos − opBase + 2` steps seed the two framing ones
and land on the source head in the drain phase — `DrainState` at `e = 0`.  The tape changes only at
the two seed cells. -/
theorem valuePush_prologue {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (opBase aPos k : Nat) (hlay : ValuePushLayout c opBase aPos k) (hk : 0 < k) :
    DrainState
      (TM.runConfig (M := valuePushProgram.toPhased.toTM) c (aPos - opBase + 2))
      opBase aPos k 0
    ∧ ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
        ¬ (opBase + 1 ≤ (p : Nat) ∧ (p : Nat) < opBase + 3) →
        (TM.runConfig (M := valuePushProgram.toPhased.toTM) c (aPos - opBase + 2)).tape p
          = c.tape p := by
  obtain ⟨hphase, hhead, hgeom, hbound, hzeroL, hanchor, hsrc, hzeroR⟩ := hlay
  have hL : opBase + 6 ≤ valuePushProgram.toPhased.toTM.tapeLength L := by omega
  -- φ0: step right off HOME
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
  -- φ1: write the first framing one
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
  -- φ2: write the second framing one
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
  -- φ3: scan gap₁'s zeros up to the anchor
  obtain ⟨h4p, h4h, h4t⟩ := valuePush_run_scanR0 3 (by omega) rfl c3 h3p
    (aPos - opBase - 3)
    (by omega)
    (fun p hp1 hp2 => by
      rw [h3t' p, if_neg (by omega), if_neg (by omega)]
      exact hzeroL p (by omega) (by omega))
  set c4 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c3 (aPos - opBase - 3) with hc4
  have h4h' : (c4.head : Nat) = aPos := by omega
  -- φ3 on the anchor: step right onto the source head
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
  -- φ4: probe the source head (a one, since k ≥ 1) — enter the drain loop
  have hb5 : c5.tape c5.head = true := by
    rw [h5t' c5.head, if_neg (by omega), if_neg (by omega)]
    exact hsrc c5.head (by omega) (by omega)
  obtain ⟨h6p, h6h, h6t⟩ := valuePush_step c5 (valuePush_state_eta c5 (by omega) h5p)
    (by rw [hb5]; exact valuePushProgram_t4_one)
  set c6 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c5 with hc6
  have h6h' : (c6.head : Nat) = aPos + 1 := by
    rw [hc6, h6h, Configuration.moveHead_stay]
    exact h5h'
  have hwf5 : c5.write c5.head true = c5.tape := by
    rw [← hb5]; exact write_self_eq c5
  have h6t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c6.tape p = if (p : Nat) = opBase + 2 then true
        else if (p : Nat) = opBase + 1 then true else c.tape p := by
    intro p
    rw [hc6, h6t, hwf5, h5t' p]
  -- chain the six segments
  have htotal : TM.runConfig (M := valuePushProgram.toPhased.toTM) c (aPos - opBase + 2) = c6 := by
    have e : aPos - opBase + 2 = 1 + (1 + (1 + ((aPos - opBase - 3) + (1 + 1)))) := by omega
    rw [e, TM.runConfig_add, valuePush_runConfig_one, ← hc1,
      TM.runConfig_add, valuePush_runConfig_one, ← hc2,
      TM.runConfig_add, valuePush_runConfig_one, ← hc3,
      TM.runConfig_add, ← hc4,
      TM.runConfig_succ, valuePush_runConfig_one, ← hc5, ← hc6]
  have h6head : (c6.head : Nat) = aPos + 1 + 0 := by omega
  have f1 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = opBase → c6.tape p = false := by
    intro p hp
    rw [h6t' p, if_neg (by omega), if_neg (by omega)]
    exact hzeroL p (by omega) (by omega)
  have f2 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      opBase + 1 ≤ (p : Nat) → (p : Nat) < opBase + 3 + 0 → c6.tape p = true := by
    intro p hp1 hp2
    rw [h6t' p]
    by_cases h2 : (p : Nat) = opBase + 2
    · rw [if_pos h2]
    · rw [if_neg h2, if_pos (by omega)]
  have f3 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      opBase + 3 + 0 ≤ (p : Nat) → (p : Nat) < aPos → c6.tape p = false := by
    intro p hp1 hp2
    rw [h6t' p, if_neg (by omega), if_neg (by omega)]
    exact hzeroL p (by omega) (by omega)
  have f4 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = aPos → c6.tape p = true := by
    intro p hp
    rw [h6t' p, if_neg (by omega), if_neg (by omega)]
    exact hanchor p hp
  have f5 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      aPos < (p : Nat) → (p : Nat) < aPos + 1 + 0 → c6.tape p = false := by
    intro p hp1 hp2
    omega
  have f6 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      aPos + 1 + 0 ≤ (p : Nat) → (p : Nat) < aPos + 1 + k → c6.tape p = true := by
    intro p hp1 hp2
    rw [h6t' p, if_neg (by omega), if_neg (by omega)]
    exact hsrc p (by omega) (by omega)
  have f7 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = aPos + 1 + k → c6.tape p = false := by
    intro p hp
    rw [h6t' p, if_neg (by omega), if_neg (by omega)]
    exact hzeroR p (by omega) (by omega)
  have f8 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      aPos + 2 + k ≤ (p : Nat) → (p : Nat) < aPos + 2 + k + 0 → c6.tape p = true := by
    intro p hp1 hp2
    omega
  have f9 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      aPos + 2 + k + 0 ≤ (p : Nat) → (p : Nat) ≤ aPos + 2 * k + 2 → c6.tape p = false := by
    intro p hp1 hp2
    rw [h6t' p, if_neg (by omega), if_neg (by omega)]
    exact hzeroR p (by omega) (by omega)
  have hDS : DrainState c6 opBase aPos k 0 :=
    ⟨h6p, h6head, hgeom, hbound, hk, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩
  have hOut : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      ¬ (opBase + 1 ≤ (p : Nat) ∧ (p : Nat) < opBase + 3) → c6.tape p = c.tape p := by
    intro p hp
    rw [h6t' p, if_neg (by omega), if_neg (by omega)]
  rw [htotal]
  exact ⟨hDS, hOut⟩

end ContractExpansion
end Frontier
end Pnp4

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

set_option maxHeartbeats 4000000 in
/-- **One mid drain round** (`e + 1 < k`): erase the leftmost remaining unit, deposit one entry one
and one scratch one, return to the new leftmost unit — `DrainState e` steps to `DrainState (e+1)`
in exactly `2·(aPos − opBase) + 2·k + 3` steps, touching nothing outside `[opBase, aPos+2k+2]`. -/
theorem valuePush_drain_mid {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (opBase aPos k e : Nat) (hds : DrainState c opBase aPos k e) (he2 : e + 1 < k) :
    DrainState
      (TM.runConfig (M := valuePushProgram.toPhased.toTM) c
        (2 * (aPos - opBase) + 2 * k + 3))
      opBase aPos k (e + 1)
    ∧ ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
        ((p : Nat) < opBase ∨ aPos + 2 * k + 2 < (p : Nat)) →
        (TM.runConfig (M := valuePushProgram.toPhased.toTM) c
          (2 * (aPos - opBase) + 2 * k + 3)).tape p = c.tape p := by
  obtain ⟨hphase, hhead, hgeom, hbound, _, hhome, hentry, hgapL, hanchor, hpre, hrest,
    hterm, hscr, hzr⟩ := hds
  -- A: φ5 erase the leftmost unit (aPos+1+e), φ6 probe the next (a one) and step back left
  obtain ⟨h1p, h1h, h1t⟩ := valuePush_step c (valuePush_state_eta c (by omega) hphase)
    (valuePushProgram_t5 (c.tape c.head))
  set c1 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c with hc1
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
  have h2h' : (c2.head : Nat) = aPos + 1 + e := by
    rw [hc2, h2h, Configuration.moveHead_left_val_of_pos c1 (by omega)]
    omega
  have hwf1 : c1.write c1.head true = c1.tape := by
    rw [← hb1]; exact write_self_eq c1
  have h2t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c2.tape p = if (p : Nat) = aPos + 1 + e then false else c.tape p := by
    intro p
    rw [hc2, h2t, hwf1, h1t' p]
  -- B: φ7 scan the erased prefix (e+1 zeros) left, then hop the anchor
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
  have h4h' : (c4.head : Nat) = aPos - 1 := by
    rw [hc4, h4h, Configuration.moveHead_left_val_of_pos c3 (by omega)]
    omega
  have hwf3 : c3.write c3.head true = c3.tape := by
    rw [← hb3]; exact write_self_eq c3
  have h4t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c4.tape p = if (p : Nat) = aPos + 1 + e then false else c.tape p := by
    intro p
    rw [hc4, h4t, hwf3, h3t, h2t' p]
  -- C: φ8 scan gap₁ left onto the entry's rightmost one, turn right onto the frontier
  obtain ⟨h5p, h5h, h5t⟩ := valuePush_run_scanL0 8 (by omega) rfl c4 h4p
    (aPos - opBase - e - 3)
    (by omega)
    (fun p hp1 hp2 => by
      rw [h4t' p, if_neg (by omega)]
      exact hgapL p (by omega) (by omega))
  set c5 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c4 (aPos - opBase - e - 3)
    with hc5
  have h5h' : (c5.head : Nat) = opBase + 2 + e := by omega

  -- D: φ8 on the entry's rightmost one — turn right onto the frontier; φ9 write the entry one
  have hb5 : c5.tape c5.head = true := by
    rw [h5t, h4t' c5.head, if_neg (by omega)]
    exact hentry c5.head (by omega) (by omega)
  obtain ⟨h6p, h6h, h6t⟩ := valuePush_step c5 (valuePush_state_eta c5 (by omega) h5p)
    (by rw [hb5]; exact valuePushProgram_t8_one)
  set c6 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c5 with hc6
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
  -- E: φ10 scan gap₁ right back onto the anchor, step over it
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
  -- F: φ11 scan the erased prefix right onto the new leftmost unit, step into the block
  obtain ⟨h10p, h10h, h10t⟩ := valuePush_run_scanR0 11 (by omega) rfl c9 h9p (e + 1)
    (by omega)
    (fun p hp1 hp2 => by
      rw [h9t' p, if_neg (by omega)]
      by_cases hq : (p : Nat) = aPos + 1 + e
      · rw [if_pos hq]
      · rw [if_neg hq]
        exact hpre p (by omega) (by omega))
  set c10 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c9 (e + 1) with hc10
  have h10h' : (c10.head : Nat) = aPos + 2 + e := by omega
  have hb10 : c10.tape c10.head = true := by
    rw [h10t, h9t' c10.head, if_neg (by omega), if_neg (by omega)]
    exact hrest c10.head (by omega) (by omega)
  obtain ⟨h11p, h11h, h11t⟩ := valuePush_step c10 (valuePush_state_eta c10 (by omega) h10p)
    (by rw [hb10]; exact valuePushProgram_t11_one)
  set c11 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c10 with hc11
  have h11h' : (c11.head : Nat) = aPos + 3 + e := by
    rw [hc11, h11h]
    simp only [Configuration.moveHead, dif_pos (show (c10.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have hwf10 : c10.write c10.head true = c10.tape := by
    rw [← hb10]; exact write_self_eq c10
  have h11t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c11.tape p = if (p : Nat) = opBase + 3 + e then true
        else if (p : Nat) = aPos + 1 + e then false else c.tape p := by
    intro p
    rw [hc11, h11t, hwf10, h10t, h9t' p]
  -- G: φ12 walk the remaining units right onto the terminator, step onto the scratch base
  obtain ⟨h12p, h12h, h12t⟩ := valuePush_run_walkR1 12 (by omega) rfl c11 h11p (k - e - 2)
    (by omega)
    (fun p hp1 hp2 => by
      rw [h11t' p, if_neg (by omega), if_neg (by omega)]
      exact hrest p (by omega) (by omega))
  set c12 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c11 (k - e - 2) with hc12
  have h12h' : (c12.head : Nat) = aPos + 1 + k := by omega
  have hb12 : c12.tape c12.head = false := by
    rw [h12t, h11t' c12.head, if_neg (by omega), if_neg (by omega)]
    exact hterm c12.head (by omega)
  obtain ⟨h13p, h13h, h13t⟩ := valuePush_step c12 (valuePush_state_eta c12 (by omega) h12p)
    (by rw [hb12]; exact valuePushProgram_t12_zero)
  set c13 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c12 with hc13
  have h13h' : (c13.head : Nat) = aPos + 2 + k := by
    rw [hc13, h13h]
    simp only [Configuration.moveHead, dif_pos (show (c12.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have hwf12 : c12.write c12.head false = c12.tape := by
    rw [← hb12]; exact write_self_eq c12
  have h13t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c13.tape p = if (p : Nat) = opBase + 3 + e then true
        else if (p : Nat) = aPos + 1 + e then false else c.tape p := by
    intro p
    rw [hc13, h13t, hwf12, h12t, h11t' p]
  -- H: φ13 walk the scratch ones right onto its frontier, write the scratch deposit, turn left
  obtain ⟨h14p, h14h, h14t⟩ := valuePush_run_walkR1 13 (by omega) rfl c13 h13p e
    (by omega)
    (fun p hp1 hp2 => by
      rw [h13t' p, if_neg (by omega), if_neg (by omega)]
      exact hscr p (by omega) (by omega))
  set c14 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c13 e with hc14
  have h14h' : (c14.head : Nat) = aPos + 2 + k + e := by omega
  have hb14 : c14.tape c14.head = false := by
    rw [h14t, h13t' c14.head, if_neg (by omega), if_neg (by omega)]
    exact hzr c14.head (by omega) (by omega)
  obtain ⟨h15p, h15h, h15t⟩ := valuePush_step c14 (valuePush_state_eta c14 (by omega) h14p)
    (by rw [hb14]; exact valuePushProgram_t13_zero)
  set c15 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c14 with hc15
  have h15h' : (c15.head : Nat) = aPos + 1 + k + e := by
    rw [hc15, h15h, Configuration.moveHead_left_val_of_pos c14 (by omega)]
    omega
  have h15t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c15.tape p = if (p : Nat) = aPos + 2 + k + e then true
        else if (p : Nat) = opBase + 3 + e then true
        else if (p : Nat) = aPos + 1 + e then false else c.tape p := by
    intro p
    rw [hc15, h15t, valuePush_write_char c14 true h14h' p, h14t, h13t' p]
  -- I: φ14 walk the scratch ones back left onto the terminator, step left onto the block's end
  obtain ⟨h16p, h16h, h16t⟩ := valuePush_run_walkL1 14 (by omega) rfl c15 h15p e
    (by omega)
    (fun p hp1 hp2 => by
      rw [h15t' p, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      exact hscr p (by omega) (by omega))
  set c16 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c15 e with hc16
  have h16h' : (c16.head : Nat) = aPos + 1 + k := by omega
  have hb16 : c16.tape c16.head = false := by
    rw [h16t, h15t' c16.head, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact hterm c16.head (by omega)
  obtain ⟨h17p, h17h, h17t⟩ := valuePush_step c16 (valuePush_state_eta c16 (by omega) h16p)
    (by rw [hb16]; exact valuePushProgram_t14_zero)
  set c17 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c16 with hc17
  have h17h' : (c17.head : Nat) = aPos + k := by
    rw [hc17, h17h, Configuration.moveHead_left_val_of_pos c16 (by omega)]
    omega
  have hwf16 : c16.write c16.head false = c16.tape := by
    rw [← hb16]; exact write_self_eq c16
  have h17t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c17.tape p = if (p : Nat) = aPos + 2 + k + e then true
        else if (p : Nat) = opBase + 3 + e then true
        else if (p : Nat) = aPos + 1 + e then false else c.tape p := by
    intro p
    rw [hc17, h17t, hwf16, h16t, h15t' p]
  -- J: φ15 walk the remaining units back left onto the erased cell, turn right (the loop point)
  obtain ⟨h18p, h18h, h18t⟩ := valuePush_run_walkL1 15 (by omega) rfl c17 h17p (k - e - 1)
    (by omega)
    (fun p hp1 hp2 => by
      rw [h17t' p, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      exact hrest p (by omega) (by omega))
  set c18 := TM.runConfig (M := valuePushProgram.toPhased.toTM) c17 (k - e - 1) with hc18
  have h18h' : (c18.head : Nat) = aPos + 1 + e := by omega
  have hb18 : c18.tape c18.head = false := by
    rw [h18t, h17t' c18.head, if_neg (by omega), if_neg (by omega),
      if_pos (show ((c18.head : Fin (valuePushProgram.toPhased.toTM.tapeLength L)) : Nat)
        = aPos + 1 + e by omega)]
  obtain ⟨h19p, h19h, h19t⟩ := valuePush_step c18 (valuePush_state_eta c18 (by omega) h18p)
    (by rw [hb18]; exact valuePushProgram_t15_zero)
  set c19 := TM.stepConfig (M := valuePushProgram.toPhased.toTM) c18 with hc19
  have h19h' : (c19.head : Nat) = aPos + 2 + e := by
    rw [hc19, h19h]
    simp only [Configuration.moveHead, dif_pos (show (c18.head : Nat) + 1
      < valuePushProgram.toPhased.toTM.tapeLength L by omega)]
    omega
  have hwf18 : c18.write c18.head false = c18.tape := by
    rw [← hb18]; exact write_self_eq c18
  have h19t' : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      c19.tape p = if (p : Nat) = aPos + 2 + k + e then true
        else if (p : Nat) = opBase + 3 + e then true
        else if (p : Nat) = aPos + 1 + e then false else c.tape p := by
    intro p
    rw [hc19, h19t, hwf18, h18t, h17t' p]
  -- chain the twenty segments
  have htotal : TM.runConfig (M := valuePushProgram.toPhased.toTM) c
      (2 * (aPos - opBase) + 2 * k + 3) = c19 := by
    have et : 2 * (aPos - opBase) + 2 * k + 3
        = 1 + (1 + ((e + 1) + (1 + ((aPos - opBase - e - 3)
          + (1 + (1 + ((aPos - opBase - e - 4) + (1 + ((e + 1) + (1 + ((k - e - 2)
          + (1 + (e + (1 + (e + (1 + ((k - e - 1) + 1))))))))))))))))) := by
      omega
    rw [et, TM.runConfig_add, valuePush_runConfig_one, ← hc1,
      TM.runConfig_add, valuePush_runConfig_one, ← hc2,
      TM.runConfig_add, ← hc3,
      TM.runConfig_add, valuePush_runConfig_one, ← hc4,
      TM.runConfig_add, ← hc5,
      TM.runConfig_add, valuePush_runConfig_one, ← hc6,
      TM.runConfig_add, valuePush_runConfig_one, ← hc7,
      TM.runConfig_add, ← hc8,
      TM.runConfig_add, valuePush_runConfig_one, ← hc9,
      TM.runConfig_add, ← hc10,
      TM.runConfig_add, valuePush_runConfig_one, ← hc11,
      TM.runConfig_add, ← hc12,
      TM.runConfig_add, valuePush_runConfig_one, ← hc13,
      TM.runConfig_add, ← hc14,
      TM.runConfig_add, valuePush_runConfig_one, ← hc15,
      TM.runConfig_add, ← hc16,
      TM.runConfig_add, valuePush_runConfig_one, ← hc17,
      TM.runConfig_add, ← hc18,
      valuePush_runConfig_one, ← hc19]
  -- the new drain state and the outside guarantee
  have h19head : (c19.head : Nat) = aPos + 1 + (e + 1) := by omega
  have g1 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = opBase → c19.tape p = false := by
    intro p hp
    rw [h19t' p, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact hhome p hp
  have g2 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      opBase + 1 ≤ (p : Nat) → (p : Nat) < opBase + 3 + (e + 1) → c19.tape p = true := by
    intro p hp1 hp2
    rw [h19t' p, if_neg (by omega)]
    by_cases hq : (p : Nat) = opBase + 3 + e
    · rw [if_pos hq]
    · rw [if_neg hq, if_neg (by omega)]
      exact hentry p (by omega) (by omega)
  have g3 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      opBase + 3 + (e + 1) ≤ (p : Nat) → (p : Nat) < aPos → c19.tape p = false := by
    intro p hp1 hp2
    rw [h19t' p, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact hgapL p (by omega) (by omega)
  have g4 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = aPos → c19.tape p = true := by
    intro p hp
    rw [h19t' p, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact hanchor p hp
  have g5 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      aPos < (p : Nat) → (p : Nat) < aPos + 1 + (e + 1) → c19.tape p = false := by
    intro p hp1 hp2
    rw [h19t' p, if_neg (by omega), if_neg (by omega)]
    by_cases hq : (p : Nat) = aPos + 1 + e
    · rw [if_pos hq]
    · rw [if_neg hq]
      exact hpre p (by omega) (by omega)
  have g6 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      aPos + 1 + (e + 1) ≤ (p : Nat) → (p : Nat) < aPos + 1 + k → c19.tape p = true := by
    intro p hp1 hp2
    rw [h19t' p, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact hrest p (by omega) (by omega)
  have g7 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      (p : Nat) = aPos + 1 + k → c19.tape p = false := by
    intro p hp
    rw [h19t' p, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact hterm p hp
  have g8 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      aPos + 2 + k ≤ (p : Nat) → (p : Nat) < aPos + 2 + k + (e + 1) → c19.tape p = true := by
    intro p hp1 hp2
    rw [h19t' p]
    by_cases hq : (p : Nat) = aPos + 2 + k + e
    · rw [if_pos hq]
    · rw [if_neg hq, if_neg (by omega), if_neg (by omega)]
      exact hscr p (by omega) (by omega)
  have g9 : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      aPos + 2 + k + (e + 1) ≤ (p : Nat) → (p : Nat) ≤ aPos + 2 * k + 2 →
      c19.tape p = false := by
    intro p hp1 hp2
    rw [h19t' p, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact hzr p (by omega) (by omega)
  have hDS : DrainState c19 opBase aPos k (e + 1) :=
    ⟨h19p, h19head, hgeom, hbound, he2, g1, g2, g3, g4, g5, g6, g7, g8, g9⟩
  have hOut : ∀ p : Fin (valuePushProgram.toPhased.toTM.tapeLength L),
      ((p : Nat) < opBase ∨ aPos + 2 * k + 2 < (p : Nat)) → c19.tape p = c.tape p := by
    intro p hp
    rw [h19t' p, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rw [htotal]
  exact ⟨hDS, hOut⟩

end ContractExpansion
end Frontier
end Pnp4

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly Pnp3.Internal.PsubsetPpoly.TM
open Pnp3.Internal.PsubsetPpoly.TM.ConstStatePhasedProgram

set_option maxHeartbeats 1000000 in
/-- **Prologue confinement** (`k ≥ 1`): along the prologue's `aPos − opBase + 2` steps the phase
never reaches the accept (`34`) and the head stays in `[opBase, aPos + 2k + 2]`.  The per-step
safety stream the region-embedding transfer (`RegionEmbeddedMulti.run_track`) consumes — additive
companion to `valuePush_prologue`. -/
theorem valuePush_prologue_confined {L : Nat}
    (c : Configuration (M := valuePushProgram.toPhased.toTM) L)
    (opBase aPos k : Nat) (hlay : ValuePushLayout c opBase aPos k) (hk : 0 < k) :
    ∀ s : Nat, s < aPos - opBase + 2 →
      (((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).state).fst : Nat) ≠ 34
      ∧ ((TM.runConfig (M := valuePushProgram.toPhased.toTM) c s).head : Nat)
          ≤ aPos + 2 * k + 2 := by
  obtain ⟨hphase, hhead, hgeom, hbound, hzeroL, hanchor, hsrc, hzeroR⟩ := hlay
  have hL : opBase + 6 ≤ valuePushProgram.toPhased.toTM.tapeLength L := by omega
  -- Replay the prologue's leg skeleton (φ0, φ1, φ2, the φ3 scan).
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
  -- The truncated chains: runConfig c 1/2/3 land on c1/c2/c3.
  have hcfg1 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c 1 = c1 := by
    rw [valuePush_runConfig_one, ← hc1]
  have hcfg2 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c 2 = c2 := by
    rw [show (2 : Nat) = 1 + 1 from rfl, TM.runConfig_add, hcfg1,
      valuePush_runConfig_one, ← hc2]
  have hcfg3 : TM.runConfig (M := valuePushProgram.toPhased.toTM) c 3 = c3 := by
    rw [show (3 : Nat) = 2 + 1 from rfl, TM.runConfig_add, hcfg2,
      valuePush_runConfig_one, ← hc3]
  -- The per-step facts.
  intro s hs
  by_cases hs0 : s = 0
  · subst hs0
    rw [TM.runConfig_zero]
    exact ⟨by omega, by omega⟩
  have h1p' : ((c1.state).fst : Nat) = 1 := h1p
  have h2p' : ((c2.state).fst : Nat) = 2 := h2p
  have h3p' : ((c3.state).fst : Nat) = 3 := h3p
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
  · -- s = g + 1: the configuration past the anchor step (phase 4 on the source head).
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
  -- 3 ≤ s ≤ g: inside the φ3 scan (the scan's own invariant at r := s − 3).
  · have hsr : s = 3 + (s - 3) := by omega
    obtain ⟨hrp, hrh, _⟩ := valuePush_run_scanR0 3 (by omega) rfl c3 h3p
      (s - 3)
      (by omega)
      (fun p hp1 hp2 => by
        rw [h3t' p, if_neg (by omega), if_neg (by omega)]
        exact hzeroL p (by omega) (by omega))
    rw [hsr, TM.runConfig_add, hcfg3]
    exact ⟨by omega, by omega⟩

end ContractExpansion
end Frontier
end Pnp4
