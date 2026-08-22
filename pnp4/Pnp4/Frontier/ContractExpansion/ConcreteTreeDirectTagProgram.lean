import Pnp4.Frontier.ContractExpansion.ConcreteTreeDirectEvaluator
import Complexity.TMVerifier.TuringToolkit.Foundation

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly
open Pnp3.Internal.PsubsetPpoly.TM

/-!
# A concrete finite-control iteration for the native tree tags

**Progress classification (AGENTS.md): Infrastructure.**  This is a bounded architecture spike,
not a complete NP verifier, and reduces neither mainline source obligation.  **No `P ≠ NP` claim.**

`directTagProgram` is a single, input-size-independent finite-control program.  Starting at a home
cell, it reads the next three bits of the authoritative concrete codec, classifies all five valid
tags (and all three malformed tags), and returns to the same home cell.  Its `runConfig` theorem is
fully concrete and premise-free for `directTagHomeConfig`; it does not use a driver-realization
hypothesis.
-/

/-- Classification of all three-bit strings in the concrete codec. -/
inductive DirectTreeTag where
  | input
  | const
  | not
  | and
  | or
  | malformed
  deriving DecidableEq, Repr, Fintype

/-- The exact tag table used by `encodeCircuitTree` / `decodeCircuitTreeAtDepth`. -/
def decodeDirectTreeTag (b0 b1 b2 : Bool) : DirectTreeTag :=
  match b0, b1, b2 with
  | false, false, false => .input
  | false, false, true => .const
  | false, true, false => .not
  | false, true, true => .and
  | true, false, false => .or
  | _, _, _ => .malformed

@[simp] theorem decodeDirectTreeTag_input :
    decodeDirectTreeTag false false false = .input := rfl
@[simp] theorem decodeDirectTreeTag_const :
    decodeDirectTreeTag false false true = .const := rfl
@[simp] theorem decodeDirectTreeTag_not :
    decodeDirectTreeTag false true false = .not := rfl
@[simp] theorem decodeDirectTreeTag_and :
    decodeDirectTreeTag false true true = .and := rfl
@[simp] theorem decodeDirectTreeTag_or :
    decodeDirectTreeTag true false false = .or := rfl
@[simp] theorem decodeDirectTreeTag_bad101 :
    decodeDirectTreeTag true false true = .malformed := rfl
@[simp] theorem decodeDirectTreeTag_bad110 :
    decodeDirectTreeTag true true false = .malformed := rfl
@[simp] theorem decodeDirectTreeTag_bad111 :
    decodeDirectTreeTag true true true = .malformed := rfl

/-- Finite local state: two captured prefix bits plus the final classification. -/
structure DirectTagState where
  first : Bool
  second : Bool
  tag : DirectTreeTag
  deriving DecidableEq, Repr, Fintype

/-- Four-microstep home-to-home tag iteration.

Phases 0/1 capture the first two bits while moving right, phase 2 reads and classifies the third
bit while beginning the return, and phase 3 returns to home.  Phase 4 idles. -/
def directTagProgram : PhasedProgram.{0} where
  numPhases := 5
  phaseState := fun _ => DirectTagState
  instFin := fun _ => inferInstance
  instDec := fun _ => inferInstance
  startPhase := 0
  startState := ⟨false, false, .malformed⟩
  acceptPhase := 4
  acceptState := ⟨false, false, .malformed⟩
  transition := fun i q scan =>
    if h0 : i.val = 0 then
      (⟨⟨1, by omega⟩, ⟨scan, q.second, q.tag⟩⟩, scan, Move.right)
    else if h1 : i.val = 1 then
      (⟨⟨2, by omega⟩, ⟨q.first, scan, q.tag⟩⟩, scan, Move.right)
    else if h2 : i.val = 2 then
      (⟨⟨3, by omega⟩, ⟨q.first, q.second,
          decodeDirectTreeTag q.first q.second scan⟩⟩, scan, Move.left)
    else if h3 : i.val = 3 then
      (⟨⟨4, by omega⟩, q⟩, scan, Move.left)
    else
      (⟨⟨4, by omega⟩, q⟩, scan, Move.stay)
  timeBound := fun _ => 4

@[simp] theorem directTagProgram_timeBound (L : Nat) :
    directTagProgram.timeBound L = 4 := rfl

@[simp] theorem directTagProgram_tapeLength (L : Nat) :
    directTagProgram.toTM.tapeLength L = L + 5 := by
  simp [TM.tapeLength, directTagProgram]

/-- Canonical home configuration for one iteration, over an arbitrary tape. -/
def directTagHomeConfig (L : Nat)
    (tape : Fin (directTagProgram.toTM.tapeLength L) → Bool) :
    Configuration (M := directTagProgram.toTM) L where
  state := ⟨⟨0, by simp [directTagProgram]⟩, ⟨false, false, .malformed⟩⟩
  head := ⟨0, directTagProgram.toTM.tapeLength_pos L⟩
  tape := tape

/-- The first three tape positions exist independently of the input length, because this program's
four-step runtime allocates five spare cells. -/
def directTagCell (L : Nat) (i : Fin 3) :
    Fin (directTagProgram.toTM.tapeLength L) :=
  ⟨i.val, by rw [directTagProgram_tapeLength]; omega⟩

@[simp] theorem directTagCell_val (L : Nat) (i : Fin 3) :
    (directTagCell L i : Nat) = i.val := rfl

/-! The following single-step lemmas expose the concrete finite-control transition, including the
exact write-back and movement.  They are useful independently of the full four-step theorem. -/

theorem directTagProgram_step0 {L : Nat}
    (c : Configuration (M := directTagProgram.toTM) L)
    (hp : c.state.fst.val = 0)
    (hr : (c.head : Nat) + 1 < directTagProgram.toTM.tapeLength L) :
    (TM.stepConfig (M := directTagProgram.toTM) c).state.fst.val = 1 ∧
    (TM.stepConfig (M := directTagProgram.toTM) c).state.snd.first = c.tape c.head ∧
    ((TM.stepConfig (M := directTagProgram.toTM) c).head : Nat) = (c.head : Nat) + 1 ∧
    (TM.stepConfig (M := directTagProgram.toTM) c).tape = c.tape := by
  have hmove :
      (directTagProgram.toTM.step c.state (c.tape c.head)).snd.snd = Move.right := by
    simp [PhasedProgram.toTM, directTagProgram, hp]
  have hwrite : c.write c.head (c.tape c.head) = c.tape := by
    funext j
    by_cases h : j = c.head <;> simp [Configuration.write, h]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [TM.stepConfig_state]
    simp [PhasedProgram.toTM, directTagProgram, hp]
  · rw [TM.stepConfig_state]
    simp [PhasedProgram.toTM, directTagProgram, hp]
  · rw [TM.stepConfig_head, hmove,
      Configuration.moveHead_right_lt (c := c) hr]
  · rw [TM.stepConfig_tape]
    simp [PhasedProgram.toTM, directTagProgram, hp, hwrite]

theorem directTagProgram_step1 {L : Nat}
    (c : Configuration (M := directTagProgram.toTM) L)
    (hp : c.state.fst.val = 1)
    (hr : (c.head : Nat) + 1 < directTagProgram.toTM.tapeLength L) :
    (TM.stepConfig (M := directTagProgram.toTM) c).state.fst.val = 2 ∧
    (TM.stepConfig (M := directTagProgram.toTM) c).state.snd.first = c.state.snd.first ∧
    (TM.stepConfig (M := directTagProgram.toTM) c).state.snd.second = c.tape c.head ∧
    ((TM.stepConfig (M := directTagProgram.toTM) c).head : Nat) = (c.head : Nat) + 1 ∧
    (TM.stepConfig (M := directTagProgram.toTM) c).tape = c.tape := by
  have hmove :
      (directTagProgram.toTM.step c.state (c.tape c.head)).snd.snd = Move.right := by
    simp [PhasedProgram.toTM, directTagProgram, hp]
  have hwrite : c.write c.head (c.tape c.head) = c.tape := by
    funext j
    by_cases h : j = c.head <;> simp [Configuration.write, h]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [TM.stepConfig_state]
    simp [PhasedProgram.toTM, directTagProgram, hp]
  · rw [TM.stepConfig_state]
    simp [PhasedProgram.toTM, directTagProgram, hp]
  · rw [TM.stepConfig_state]
    simp [PhasedProgram.toTM, directTagProgram, hp]
  · rw [TM.stepConfig_head, hmove,
      Configuration.moveHead_right_lt (c := c) hr]
  · rw [TM.stepConfig_tape]
    simp [PhasedProgram.toTM, directTagProgram, hp, hwrite]

theorem directTagProgram_step2 {L : Nat}
    (c : Configuration (M := directTagProgram.toTM) L)
    (hp : c.state.fst.val = 2) (hl : (c.head : Nat) ≠ 0) :
    (TM.stepConfig (M := directTagProgram.toTM) c).state.fst.val = 3 ∧
    (TM.stepConfig (M := directTagProgram.toTM) c).state.snd.tag =
      decodeDirectTreeTag c.state.snd.first c.state.snd.second (c.tape c.head) ∧
    ((TM.stepConfig (M := directTagProgram.toTM) c).head : Nat) = (c.head : Nat) - 1 ∧
    (TM.stepConfig (M := directTagProgram.toTM) c).tape = c.tape := by
  have hwrite : c.write c.head (c.tape c.head) = c.tape := by
    funext j
    by_cases h : j = c.head <;> simp [Configuration.write, h]
  simp only [TM.stepConfig, PhasedProgram.toTM, directTagProgram]
  simp [hp, Configuration.moveHead, hl, hwrite]

theorem directTagProgram_step3 {L : Nat}
    (c : Configuration (M := directTagProgram.toTM) L)
    (hp : c.state.fst.val = 3) (hl : (c.head : Nat) ≠ 0) :
    (TM.stepConfig (M := directTagProgram.toTM) c).state.fst.val = 4 ∧
    (TM.stepConfig (M := directTagProgram.toTM) c).state.snd = c.state.snd ∧
    ((TM.stepConfig (M := directTagProgram.toTM) c).head : Nat) = (c.head : Nat) - 1 ∧
    (TM.stepConfig (M := directTagProgram.toTM) c).tape = c.tape := by
  have hwrite : c.write c.head (c.tape c.head) = c.tape := by
    funext j
    by_cases h : j = c.head <;> simp [Configuration.write, h]
  simp only [TM.stepConfig, PhasedProgram.toTM, directTagProgram]
  simp [hp, Configuration.moveHead, hl, hwrite]

/-- **Concrete hypothesis-free `runConfig` result.**  One four-microstep iteration reads the actual
three codec bits, classifies them, preserves the tape, and returns the head to home. -/
theorem directTagProgram_runConfig_home (L : Nat)
    (tape : Fin (directTagProgram.toTM.tapeLength L) → Bool) :
    let out := TM.runConfig (M := directTagProgram.toTM) (directTagHomeConfig L tape) 4
    out.state.fst.val = 4 ∧
      out.state.snd.tag = decodeDirectTreeTag
        (tape (directTagCell L 0)) (tape (directTagCell L 1)) (tape (directTagCell L 2)) ∧
      (out.head : Nat) = 0 ∧ out.tape = tape := by
  let c0 := directTagHomeConfig L tape
  let c1 := TM.stepConfig (M := directTagProgram.toTM) c0
  let c2 := TM.stepConfig (M := directTagProgram.toTM) c1
  let c3 := TM.stepConfig (M := directTagProgram.toTM) c2
  let c4 := TM.stepConfig (M := directTagProgram.toTM) c3
  have hlen : directTagProgram.toTM.tapeLength L = L + 5 := directTagProgram_tapeLength L
  have h0r : (c0.head : Nat) + 1 < directTagProgram.toTM.tapeLength L := by
    simp [c0, directTagHomeConfig, hlen]
  obtain ⟨c1p, c1b, c1h, c1t⟩ := directTagProgram_step0 c0 (by rfl) h0r
  have h1r : (c1.head : Nat) + 1 < directTagProgram.toTM.tapeLength L := by
    rw [c1h]
    simp [c0, directTagHomeConfig]
  obtain ⟨c2p, c2first, c2b, c2h, c2t⟩ := directTagProgram_step1 c1 c1p h1r
  have h2l : (c2.head : Nat) ≠ 0 := by rw [c2h, c1h]; simp [c0, directTagHomeConfig]
  obtain ⟨c3p, c3tag, c3h, c3t⟩ := directTagProgram_step2 c2 c2p h2l
  have h3l : (c3.head : Nat) ≠ 0 := by rw [c3h, c2h, c1h]; simp [c0, directTagHomeConfig]
  obtain ⟨c4p, c4s, c4h, c4t⟩ := directTagProgram_step3 c3 c3p h3l
  have hrun : TM.runConfig (M := directTagProgram.toTM) c0 4 = c4 := by
    simp [TM.runConfig, c1, c2, c3, c4, Function.iterate_succ_apply]
  rw [show directTagHomeConfig L tape = c0 from rfl, hrun]
  refine ⟨c4p, ?_, ?_, ?_⟩
  · rw [c4s, c3tag, c2first, c2b, c1b]
    congr 1
  · rw [c4h, c3h, c2h, c1h]
    simp [c0, directTagHomeConfig]
  · rw [c4t, c3t, c2t, c1t]
    rfl

/-- The iteration consumes four microsteps and three tape cells, both bounded by the shared
quadratic budget for every positive serialized witness length. -/
theorem directTagProgram_within_bounds (L : Nat) (hL : 1 ≤ L) :
    directTagProgram.timeBound L ≤ directMicrostepBound L ∧
      3 ≤ directStackCapacity L := by
  constructor
  · simp [directTagProgram, directMicrostepBound, directStackCapacity]
    nlinarith
  · unfold directStackCapacity
    omega

end ContractExpansion
end Frontier
end Pnp4
