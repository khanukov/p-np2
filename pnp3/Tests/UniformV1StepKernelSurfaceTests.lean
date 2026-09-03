import Complexity.Uniform.V1.StepKernelExamples

namespace Pnp3.Tests.UniformV1StepKernel

open Pnp3.ComplexityInterfaces
open Pnp3.ComplexityInterfaces.DagCircuit
open Pnp3.Complexity.Uniform.V1
open Pnp3.Complexity.Uniform.V1.Circuit

#check symbols
#check moves
#check blockDispatch
#check stateBit
#check headBit
#check presentBit
#check valueBit
#check scanPresent
#check scanValue
#check symbolGuard
#check branch
#check actionOr
#check nextStateBit
#check moveBit
#check writePresent
#check writeValue
#check nextHeadBit
#check nextPresent
#check nextValue
#check encodedStep
#check StepSpec
#check runBundle

theorem check_symbols_members :
    none ∈ symbols ∧ some false ∈ symbols ∧ some true ∈ symbols :=
  symbols_members

theorem check_moves_members :
    Move.left ∈ moves ∧ Move.stay ∈ moves ∧ Move.right ∈ moves :=
  moves_members

theorem check_blockDispatch_state {M : UniformTM} {n budget : Nat} {A : Type}
    (s : Fin M.stateCount → A) (h p v : Fin (tapeLength n budget) → A)
    (q : Fin M.stateCount) :
    blockDispatch M n budget s h p v (stateIndex M n budget q) = s q :=
  blockDispatch_state M n budget s h p v q

theorem check_blockDispatch_head {M : UniformTM} {n budget : Nat} {A : Type}
    (s : Fin M.stateCount → A) (h p v : Fin (tapeLength n budget) → A)
    (i : Fin (tapeLength n budget)) :
    blockDispatch M n budget s h p v (headIndex M n budget i) = h i :=
  blockDispatch_head M n budget s h p v i

theorem check_blockDispatch_present {M : UniformTM} {n budget : Nat} {A : Type}
    (s : Fin M.stateCount → A) (h p v : Fin (tapeLength n budget) → A)
    (i : Fin (tapeLength n budget)) :
    blockDispatch M n budget s h p v (tapePresentIndex M n budget i) = p i :=
  blockDispatch_present M n budget s h p v i

theorem check_blockDispatch_value {M : UniformTM} {n budget : Nat} {A : Type}
    (s : Fin M.stateCount → A) (h p v : Fin (tapeLength n budget) → A)
    (i : Fin (tapeLength n budget)) :
    blockDispatch M n budget s h p v (tapeValueIndex M n budget i) = v i :=
  blockDispatch_value M n budget s h p v i

theorem check_stateBit_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (q : Fin M.stateCount) :
    stateBit M n budget (encodeConfig M c) q = decide (q = c.state) :=
  stateBit_encodeConfig M c q

theorem check_headBit_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (i : Fin (tapeLength n budget)) :
    headBit M n budget (encodeConfig M c) i = decide (i = c.head) :=
  headBit_encodeConfig M c i

theorem check_presentBit_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (i : Fin (tapeLength n budget)) :
    presentBit M n budget (encodeConfig M c) i = symbolPresent (c.tape i) :=
  presentBit_encodeConfig M c i

theorem check_valueBit_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (i : Fin (tapeLength n budget)) :
    valueBit M n budget (encodeConfig M c) i = symbolValue (c.tape i) :=
  valueBit_encodeConfig M c i

theorem check_scanPresent_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) :
    scanPresent M n budget (encodeConfig M c) = symbolPresent (c.tape c.head) :=
  scanPresent_encodeConfig M c

theorem check_scanValue_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) :
    scanValue M n budget (encodeConfig M c) = symbolValue (c.tape c.head) :=
  scanValue_encodeConfig M c

theorem check_symbolGuard_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (symbol : Option Bool) :
    symbolGuard M n budget (encodeConfig M c) symbol =
      decide (symbol = c.tape c.head) :=
  symbolGuard_encodeConfig M c symbol

theorem check_branch_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (q : Fin M.stateCount)
    (symbol : Option Bool) :
    branch M n budget (encodeConfig M c) q symbol =
      (decide (q = c.state) && decide (symbol = c.tape c.head)) :=
  branch_encodeConfig M c q symbol

theorem check_actionOr_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget)
    (predicate : (Fin M.stateCount × Option Bool × Move) → Bool) :
    actionOr M n budget (encodeConfig M c) predicate =
      predicate (M.step c.state (c.tape c.head)) :=
  actionOr_encodeConfig M c predicate

theorem check_nextStateBit_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (q : Fin M.stateCount) :
    nextStateBit M n budget (encodeConfig M c) q =
      decide (q = (M.step c.state (c.tape c.head)).1) :=
  nextStateBit_encodeConfig M c q

theorem check_moveBit_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (move : Move) :
    moveBit M n budget (encodeConfig M c) move =
      decide (move = (M.step c.state (c.tape c.head)).2.2) :=
  moveBit_encodeConfig M c move

theorem check_writePresent_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) :
    writePresent M n budget (encodeConfig M c) =
      symbolPresent (M.step c.state (c.tape c.head)).2.1 :=
  writePresent_encodeConfig M c

theorem check_writeValue_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) :
    writeValue M n budget (encodeConfig M c) =
      symbolValue (M.step c.state (c.tape c.head)).2.1 :=
  writeValue_encodeConfig M c

theorem check_nextHeadBit_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (i : Fin (tapeLength n budget)) :
    nextHeadBit M n budget (encodeConfig M c) i =
      decide (i = moveHead c.head (M.step c.state (c.tape c.head)).2.2) :=
  nextHeadBit_encodeConfig M c i

theorem check_nextPresent_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (i : Fin (tapeLength n budget)) :
    nextPresent M n budget (encodeConfig M c) i =
      symbolPresent (if i = c.head then
        (M.step c.state (c.tape c.head)).2.1 else c.tape i) :=
  nextPresent_encodeConfig M c i

theorem check_nextValue_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (i : Fin (tapeLength n budget)) :
    nextValue M n budget (encodeConfig M c) i =
      symbolValue (if i = c.head then
        (M.step c.state (c.tape c.head)).2.1 else c.tape i) :=
  nextValue_encodeConfig M c i

theorem check_encodedStep_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) :
    encodedStep M n budget (encodeConfig M c) = encodeConfig M (M.stepConfig c) :=
  encodedStep_encodeConfig M c

theorem check_encodedStep_iterate_run (M : UniformTM) {n budget : Nat}
    (t : Nat) (c : Config M.stateCount n budget) :
    (encodedStep M n budget)^[t] (encodeConfig M c) = encodeConfig M (M.run t c) :=
  encodedStep_iterate_run M t c

theorem check_stepSpec_of_evalFun (M : UniformTM) {n budget : Nat}
    (S : DagBundle (configWidth M n budget) (configWidth M n budget))
    (h : S.evalFun = encodedStep M n budget) : StepSpec M S :=
  stepSpec_of_evalFun M S h

theorem check_iterateBundle_stepSpec (M : UniformTM) {n budget : Nat}
    (S : DagBundle (configWidth M n budget) (configWidth M n budget))
    (h : StepSpec M S) (t : Nat) (c : Config M.stateCount n budget) :
    (iterateBundle S t).evalFun (encodeConfig M c) = encodeConfig M (M.run t c) :=
  iterateBundle_stepSpec M S h t c

theorem check_runBundle_gates (M : UniformTM) {n budget : Nat}
    (S : DagBundle (configWidth M n budget) (configWidth M n budget)) (t : Nat) :
    (runBundle M n budget S t).gates = 2 + t * S.gates :=
  runBundle_gates M S t

theorem check_runBundle_spec (M : UniformTM) {n budget : Nat}
    (S : DagBundle (configWidth M n budget) (configWidth M n budget))
    (h : StepSpec M S) (t : Nat) :
    Spec (runBundle M n budget S t)
      (fun x => M.run t (initialConfig M budget x)) :=
  runBundle_spec M S h t

theorem check_runBundle_accept_iff (M : UniformTM) {n budget : Nat}
    (S : DagBundle (configWidth M n budget) (configWidth M n budget))
    (h : StepSpec M S) (t : Nat)
    (x : Pnp3.Complexity.Uniform.V1.Bitstring n) :
    (runBundle M n budget S t).evalOutput
        (stateIndex M n budget M.accept) x = true ↔ AcceptsAt M budget t x :=
  runBundle_accept_iff M S h t x

theorem check_firstBit_true_encodedStep :
    let x : Pnp3.Complexity.Uniform.V1.Bitstring 1 := fun _ => true
    let c := initialConfig firstBitMachine 1 x
    let cell0 : Fin (tapeLength 1 1) := ⟨0, by simp [tapeLength]⟩
    encodedStep firstBitMachine 1 1 (encodeConfig firstBitMachine c)
        (stateIndex firstBitMachine 1 1 firstBitMachine.accept) = true ∧
      encodedStep firstBitMachine 1 1 (encodeConfig firstBitMachine c)
        (tapePresentIndex firstBitMachine 1 1 cell0) = true ∧
      encodedStep firstBitMachine 1 1 (encodeConfig firstBitMachine c)
        (tapeValueIndex firstBitMachine 1 1 cell0) = true :=
  firstBit_true_encodedStep

theorem check_firstBit_empty_encodedStep :
    let x : Pnp3.Complexity.Uniform.V1.Bitstring 0 := fun i => i.elim0
    let c := initialConfig firstBitMachine 1 x
    let cell0 : Fin (tapeLength 0 1) := ⟨0, by simp [tapeLength]⟩
    encodedStep firstBitMachine 0 1 (encodeConfig firstBitMachine c)
        (stateIndex firstBitMachine 0 1 firstBitMachine.reject) = true ∧
      encodedStep firstBitMachine 0 1 (encodeConfig firstBitMachine c)
        (tapePresentIndex firstBitMachine 0 1 cell0) = false ∧
      encodedStep firstBitMachine 0 1 (encodeConfig firstBitMachine c)
        (tapeValueIndex firstBitMachine 0 1 cell0) = false :=
  firstBit_empty_encodedStep

theorem check_lengthParity_one_step_encodedStep (bit : Bool) :
    let x : Pnp3.Complexity.Uniform.V1.Bitstring 1 := fun _ => bit
    let c := initialConfig lengthParityMachine 1 x
    let cell0 : Fin (tapeLength 1 1) := ⟨0, by simp [tapeLength]⟩
    let cell1 : Fin (tapeLength 1 1) := ⟨1, by simp [tapeLength]⟩
    encodedStep lengthParityMachine 1 1 (encodeConfig lengthParityMachine c)
        (stateIndex lengthParityMachine 1 1 ⟨1, by decide⟩) = true ∧
      encodedStep lengthParityMachine 1 1 (encodeConfig lengthParityMachine c)
        (headIndex lengthParityMachine 1 1 cell1) = true ∧
      encodedStep lengthParityMachine 1 1 (encodeConfig lengthParityMachine c)
        (tapePresentIndex lengthParityMachine 1 1 cell0) = true ∧
      encodedStep lengthParityMachine 1 1 (encodeConfig lengthParityMachine c)
        (tapeValueIndex lengthParityMachine 1 1 cell0) = bit ∧
      encodedStep lengthParityMachine 1 1 (encodeConfig lengthParityMachine c)
        (tapePresentIndex lengthParityMachine 1 1 cell1) = false ∧
      encodedStep lengthParityMachine 1 1 (encodeConfig lengthParityMachine c)
        (tapeValueIndex lengthParityMachine 1 1 cell1) = false :=
  lengthParity_one_step_encodedStep bit

theorem check_blankWrite_leftClamp_encodedStep :
    let M : UniformTM :=
      UniformTM.mk
        3
        (⟨0, by decide⟩)
        (⟨1, by decide⟩)
        (⟨2, by decide⟩)
        (by decide)
        (fun _ _ => (⟨1, by decide⟩, none, Move.left))
    let x : Pnp3.Complexity.Uniform.V1.Bitstring 1 := fun _ => true
    let c := initialConfig M 1 x
    let cell0 : Fin (tapeLength 1 1) := ⟨0, by simp [tapeLength]⟩
    encodedStep M 1 1 (encodeConfig M c)
        (stateIndex M 1 1 M.accept) = true ∧
      encodedStep M 1 1 (encodeConfig M c)
        (headIndex M 1 1 cell0) = true ∧
      encodedStep M 1 1 (encodeConfig M c)
        (tapePresentIndex M 1 1 cell0) = false ∧
      encodedStep M 1 1 (encodeConfig M c)
        (tapeValueIndex M 1 1 cell0) = false :=
  blankWrite_leftClamp_encodedStep

end Pnp3.Tests.UniformV1StepKernel
