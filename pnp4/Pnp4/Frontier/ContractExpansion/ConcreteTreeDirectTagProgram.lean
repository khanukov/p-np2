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
cell, it reads the next three bits, classifies them through a table *defined from the authoritative
decoder*, and returns to the same home cell.  The four-step result retains the classification; a
fifth step enters the unique accept state exactly for a valid tag.  These local results do not
iterate over a tree or realize the functional evaluator's stacks.
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

/-- Root-constructor classification of the authoritative decoder's tree type. -/
def directTreeTagOfTree {n : Nat} : Encoding.CircuitTree n → DirectTreeTag
  | .input _ => .input
  | .const _ => .const
  | .not _ => .not
  | .and _ _ => .and
  | .or _ _ => .or

/-- A payload on which every valid root tag can be decoded: two constant leaves suffice for all
five root constructors (the input field has width zero in the probe). -/
def directTagDecoderProbe : List Bool :=
  [false, false, true, false, false, false, true, false]

/-- The finite-control tag table, derived from the authoritative `decodeCircuitTreeAtDepth` rather
than restating its eight cases.  `n = 1`, width zero and depth three make the probe total precisely
on the five valid root tags. -/
def decodeDirectTreeTag (b0 b1 b2 : Bool) : DirectTreeTag :=
  match Encoding.decodeCircuitTreeAtDepth 1 0 3
      (b0 :: b1 :: b2 :: directTagDecoderProbe) with
  | some (tree, _) => directTreeTagOfTree tree
  | none => .malformed

/-- Definitional bridge from the finite-control classification to the authoritative decoder. -/
theorem decodeDirectTreeTag_authoritative (b0 b1 b2 : Bool) :
    decodeDirectTreeTag b0 b1 b2 =
      match Encoding.decodeCircuitTreeAtDepth 1 0 3
          (b0 :: b1 :: b2 :: directTagDecoderProbe) with
      | some (tree, _) => directTreeTagOfTree tree
      | none => .malformed := rfl

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

/-- A successful run of the authoritative decoder on arbitrary payload has the root constructor
classified by `decodeDirectTreeTag`.  Thus the probe-derived table is formally tied to real decoder
branches, not justified by a second table inspection. -/
theorem decodeDirectTreeTag_eq_root_of_decode {n width d : Nat} (b0 b1 b2 : Bool)
    (payload : List Bool) (tree : Encoding.CircuitTree n) (rest : List Bool)
    (hdecode : Encoding.decodeCircuitTreeAtDepth n width (d + 1)
      (b0 :: b1 :: b2 :: payload) = some (tree, rest)) :
    decodeDirectTreeTag b0 b1 b2 = directTreeTagOfTree tree := by
  rcases b0 with _ | _ <;> rcases b1 with _ | _ <;> rcases b2 with _ | _
  · simp only [Encoding.decodeCircuitTreeAtDepth] at hdecode
    split at hdecode
    · contradiction
    · cases hfin : Encoding.decodeFin width (List.take width payload) with
      | none => simp [hfin] at hdecode
      | some i =>
          simp only [hfin] at hdecode
          split at hdecode
          · rcases hdecode with ⟨rfl, rfl⟩
            rfl
          · contradiction
  · rcases payload with _ | ⟨b, payload⟩
    · simp [Encoding.decodeCircuitTreeAtDepth] at hdecode
    · simp [Encoding.decodeCircuitTreeAtDepth] at hdecode
      rcases hdecode with ⟨rfl, rfl⟩
      rfl
  · simp only [Encoding.decodeCircuitTreeAtDepth] at hdecode
    cases hsub : Encoding.decodeCircuitTreeAtDepth n width d payload with
    | none => simp [hsub] at hdecode
    | some p =>
        rcases p with ⟨c, remainder⟩
        simp only [hsub] at hdecode
        rcases hdecode with ⟨rfl, rfl⟩
        rfl
  · simp only [Encoding.decodeCircuitTreeAtDepth] at hdecode
    cases hleft : Encoding.decodeCircuitTreeAtDepth n width d payload with
    | none => simp [hleft] at hdecode
    | some p =>
        rcases p with ⟨left, payload'⟩
        simp only [hleft] at hdecode
        cases hright : Encoding.decodeCircuitTreeAtDepth n width d payload' with
        | none => simp [hright] at hdecode
        | some p =>
            rcases p with ⟨right, remainder⟩
            simp only [hright] at hdecode
            rcases hdecode with ⟨rfl, rfl⟩
            rfl
  · simp only [Encoding.decodeCircuitTreeAtDepth] at hdecode
    cases hleft : Encoding.decodeCircuitTreeAtDepth n width d payload with
    | none => simp [hleft] at hdecode
    | some p =>
        rcases p with ⟨left, payload'⟩
        simp only [hleft] at hdecode
        cases hright : Encoding.decodeCircuitTreeAtDepth n width d payload' with
        | none => simp [hright] at hdecode
        | some p =>
            rcases p with ⟨right, remainder⟩
            simp only [hright] at hdecode
            rcases hdecode with ⟨rfl, rfl⟩
            rfl
  · simp [Encoding.decodeCircuitTreeAtDepth] at hdecode
  · simp [Encoding.decodeCircuitTreeAtDepth] at hdecode
  · simp [Encoding.decodeCircuitTreeAtDepth] at hdecode

/-- Finite local state: two captured prefix bits plus the final classification. -/
structure DirectTagState where
  first : Bool
  second : Bool
  tag : DirectTreeTag
  deriving DecidableEq, Repr, Fintype

/-- Four-microstep home-to-home tag classification followed by a fifth acceptance step.

Phases 0/1 capture the first two bits while moving right, phase 2 reads and classifies the third
bit while beginning the return, and phase 3 returns to home.  At phase 4 a valid classification
enters the unique phase-5 accept state; malformed classifications remain in phase 4. -/
def directTagProgram : PhasedProgram.{0} where
  numPhases := 6
  phaseState := fun _ => DirectTagState
  instFin := fun _ => inferInstance
  instDec := fun _ => inferInstance
  startPhase := 0
  startState := ⟨false, false, .malformed⟩
  acceptPhase := 5
  acceptState := ⟨false, false, .input⟩
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
    else if h4 : i.val = 4 then
      if q.tag = .malformed then
        (⟨⟨4, by omega⟩, q⟩, scan, Move.stay)
      else
        (⟨⟨5, by omega⟩, ⟨false, false, .input⟩⟩, scan, Move.stay)
    else
      (⟨⟨5, by omega⟩, q⟩, scan, Move.stay)
  timeBound := fun _ => 5

@[simp] theorem directTagProgram_timeBound (L : Nat) :
    directTagProgram.timeBound L = 5 := rfl

@[simp] theorem directTagProgram_tapeLength (L : Nat) :
    directTagProgram.toTM.tapeLength L = L + 6 := by
  simp [TM.tapeLength, directTagProgram]

/-- Canonical home configuration for one iteration, over an arbitrary tape. -/
def directTagHomeConfig (L : Nat)
    (tape : Fin (directTagProgram.toTM.tapeLength L) → Bool) :
    Configuration (M := directTagProgram.toTM) L where
  state := ⟨⟨0, by simp [directTagProgram]⟩, ⟨false, false, .malformed⟩⟩
  head := ⟨0, directTagProgram.toTM.tapeLength_pos L⟩
  tape := tape

/-- The first three tape positions exist independently of the input length, because this program's
five-step runtime allocates six spare cells. -/
def directTagCell (L : Nat) (i : Fin 3) :
    Fin (directTagProgram.toTM.tapeLength L) :=
  ⟨i.val, by rw [directTagProgram_tapeLength]; omega⟩

@[simp] theorem directTagCell_val (L : Nat) (i : Fin 3) :
    (directTagCell L i : Nat) = i.val := rfl

/-- Home configuration at an arbitrary in-range offset with room for the three-bit tag. -/
def directTagHomeConfigAt (L home : Nat)
    (hroom : home + 2 < directTagProgram.toTM.tapeLength L)
    (tape : Fin (directTagProgram.toTM.tapeLength L) → Bool) :
    Configuration (M := directTagProgram.toTM) L where
  state := ⟨⟨0, by simp [directTagProgram]⟩, ⟨false, false, .malformed⟩⟩
  head := ⟨home, by omega⟩
  tape := tape

/-- The three cells beginning at an arbitrary home offset. -/
def directTagCellAt (L home : Nat)
    (hroom : home + 2 < directTagProgram.toTM.tapeLength L) (i : Fin 3) :
    Fin (directTagProgram.toTM.tapeLength L) :=
  ⟨home + i.val, by omega⟩

@[simp] theorem directTagCellAt_val (L home : Nat)
    (hroom : home + 2 < directTagProgram.toTM.tapeLength L) (i : Fin 3) :
    (directTagCellAt L home hroom i : Nat) = home + i.val := rfl

/-- The corresponding three positions inside a finite input word. -/
def directTagInputCell (N home : Nat) (hroom : home + 2 < N) (i : Fin 3) : Fin N :=
  ⟨home + i.val, by omega⟩

@[simp] theorem directTagInputCell_val (N home : Nat) (hroom : home + 2 < N)
    (i : Fin 3) : (directTagInputCell N home hroom i : Nat) = home + i.val := rfl

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

/-- The fifth transition reaches the unique accept state exactly for a valid classification.
Malformed tags remain in the nonaccepting classification phase. -/
theorem directTagProgram_step4_accepts_iff {L : Nat}
    (c : Configuration (M := directTagProgram.toTM) L)
    (hp : c.state.fst.val = 4) :
    (TM.stepConfig (M := directTagProgram.toTM) c).state = directTagProgram.toTM.accept ↔
      c.state.snd.tag ≠ .malformed := by
  cases htag : c.state.snd.tag <;>
    simp only [TM.stepConfig, PhasedProgram.toTM, directTagProgram, htag]
  all_goals split <;> simp_all

/-- **Concrete hypothesis-free `runConfig` result.**  One four-microstep iteration reads the three
supplied home cells, classifies them, preserves the tape, and returns the head to home. -/
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
  have hlen : directTagProgram.toTM.tapeLength L = L + 6 := directTagProgram_tapeLength L
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

/-- **Offset-parametric premise-free run theorem.**  The same finite control reads three cells at
any supplied home offset with room, returns to that offset, and preserves the entire tape. -/
theorem directTagProgram_runConfig_at (L home : Nat)
    (hroom : home + 2 < directTagProgram.toTM.tapeLength L)
    (tape : Fin (directTagProgram.toTM.tapeLength L) → Bool) :
    let out := TM.runConfig (M := directTagProgram.toTM)
      (directTagHomeConfigAt L home hroom tape) 4
    out.state.fst.val = 4 ∧
      out.state.snd.tag = decodeDirectTreeTag
        (tape (directTagCellAt L home hroom 0))
        (tape (directTagCellAt L home hroom 1))
        (tape (directTagCellAt L home hroom 2)) ∧
      (out.head : Nat) = home ∧ out.tape = tape := by
  let c0 := directTagHomeConfigAt L home hroom tape
  let c1 := TM.stepConfig (M := directTagProgram.toTM) c0
  let c2 := TM.stepConfig (M := directTagProgram.toTM) c1
  let c3 := TM.stepConfig (M := directTagProgram.toTM) c2
  let c4 := TM.stepConfig (M := directTagProgram.toTM) c3
  have h0r : (c0.head : Nat) + 1 < directTagProgram.toTM.tapeLength L := by
    change home + 1 < directTagProgram.toTM.tapeLength L
    omega
  obtain ⟨c1p, c1b, c1h, c1t⟩ := directTagProgram_step0 c0 (by rfl) h0r
  have h1r : (c1.head : Nat) + 1 < directTagProgram.toTM.tapeLength L := by
    rw [c1h]
    change home + 1 + 1 < directTagProgram.toTM.tapeLength L
    omega
  obtain ⟨c2p, c2first, c2b, c2h, c2t⟩ := directTagProgram_step1 c1 c1p h1r
  have h2l : (c2.head : Nat) ≠ 0 := by
    rw [c2h, c1h]
    simp [c0, directTagHomeConfigAt]
  obtain ⟨c3p, c3tag, c3h, c3t⟩ := directTagProgram_step2 c2 c2p h2l
  have h3l : (c3.head : Nat) ≠ 0 := by
    rw [c3h, c2h, c1h]
    simp [c0, directTagHomeConfigAt]
  obtain ⟨c4p, c4s, c4h, c4t⟩ := directTagProgram_step3 c3 c3p h3l
  have hcell0 : c0.head = directTagCellAt L home hroom 0 := by
    apply Fin.ext
    simp [c0, directTagHomeConfigAt, directTagCellAt]
  have hcell1 : c1.head = directTagCellAt L home hroom 1 := by
    apply Fin.ext
    rw [c1h]
    simp [c0, directTagHomeConfigAt, directTagCellAt]
  have hcell2 : c2.head = directTagCellAt L home hroom 2 := by
    apply Fin.ext
    rw [c2h, c1h]
    simp [c0, directTagHomeConfigAt, directTagCellAt]
  have hrun : TM.runConfig (M := directTagProgram.toTM) c0 4 = c4 := by
    simp [TM.runConfig, c1, c2, c3, c4, Function.iterate_succ_apply]
  rw [show directTagHomeConfigAt L home hroom tape = c0 from rfl, hrun]
  refine ⟨c4p, ?_, ?_, ?_⟩
  · rw [c4s, c3tag, c2first, c2b, c1b]
    rw [c2t, c1t, hcell2, hcell1, hcell0]
    rfl
  · rw [c4h, c3h, c2h, c1h]
    simp [c0, directTagHomeConfigAt]
  · rw [c4t, c3t, c2t, c1t]
    rfl

/-- **Actual-input/home-offset integration.**  When the arbitrary tape above is instantiated with
the machine's real `initialConfig` tape for a fixed-width bit vector, the four-step classification
reads exactly the three vector entries beginning at `home` and returns there.  This is still one tag
iteration, not a decoder loop or a full evaluator run. -/
theorem directTagProgram_runConfig_input_at (N home : Nat)
    (w : AlgorithmsToLowerBounds.BitVec N) (hroom : home + 2 < N) :
    let hroomTape : home + 2 < directTagProgram.toTM.tapeLength N := by
      rw [directTagProgram_tapeLength]
      omega
    let tape := (directTagProgram.toTM.initialConfig w).tape
    let out := TM.runConfig (M := directTagProgram.toTM)
      (directTagHomeConfigAt N home hroomTape tape) 4
    out.state.snd.tag = decodeDirectTreeTag
        (w (directTagInputCell N home hroom 0))
        (w (directTagInputCell N home hroom 1))
        (w (directTagInputCell N home hroom 2)) ∧
      (out.head : Nat) = home := by
  dsimp only
  let hroomTape : home + 2 < directTagProgram.toTM.tapeLength N := by
    rw [directTagProgram_tapeLength]
    omega
  let tape := (directTagProgram.toTM.initialConfig w).tape
  have hrun := directTagProgram_runConfig_at N home hroomTape tape
  refine ⟨?_, hrun.2.2.1⟩
  rw [hrun.2.1]
  congr 1
  all_goals
    simp only [tape]
    rw [TM.initial_tape_input]
    congr 1

/-- After the fifth step the redesigned accept state is reached exactly for one of the five valid
authoritative tags.  The four-step theorem above remains the observation point for the tag value. -/
theorem directTagProgram_runConfig_five_accepts_iff (L : Nat)
    (tape : Fin (directTagProgram.toTM.tapeLength L) → Bool) :
    (TM.runConfig (M := directTagProgram.toTM) (directTagHomeConfig L tape) 5).state =
        directTagProgram.toTM.accept ↔
      decodeDirectTreeTag
        (tape (directTagCell L 0)) (tape (directTagCell L 1))
          (tape (directTagCell L 2)) ≠ .malformed := by
  let c4 := TM.runConfig (M := directTagProgram.toTM) (directTagHomeConfig L tape) 4
  have hrun := directTagProgram_runConfig_home L tape
  have hp : c4.state.fst.val = 4 := hrun.1
  have htag : c4.state.snd.tag = decodeDirectTreeTag
      (tape (directTagCell L 0)) (tape (directTagCell L 1))
        (tape (directTagCell L 2)) := hrun.2.1
  have hstep := directTagProgram_step4_accepts_iff c4 hp
  rw [show TM.runConfig (M := directTagProgram.toTM) (directTagHomeConfig L tape) 5 =
      TM.stepConfig (M := directTagProgram.toTM) c4 by
        simp [c4, TM.runConfig, Function.iterate_succ_apply]]
  rw [hstep, htag]

end ContractExpansion
end Frontier
end Pnp4
