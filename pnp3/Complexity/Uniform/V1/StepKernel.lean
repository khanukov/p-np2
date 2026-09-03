import Complexity.Uniform.V1.CircuitEncoding

/-!
# Encoded one-step semantic kernel for Uniform V1

This module is intentionally a pure Boolean semantic kernel.  It constructs no
step bundle; bundle iteration below is conditional on a caller-supplied
`StepSpec`.
-/

namespace Pnp3.Complexity.Uniform.V1.Circuit

open Pnp3.ComplexityInterfaces
open Pnp3.ComplexityInterfaces.DagCircuit

/-! ## Fixed compile-time enumerations and layout dispatch -/

/-- The canonical three-symbol alphabet, in blank/false/true order. -/
def symbols : List (Option Bool) := [none, some false, some true]

/-- The canonical three head moves, in left/stay/right order.  This public
enumeration is intentionally reserved for P1b-3 circuit compilation.  The pure
`encodedStep` does not consume it because `nextHeadBit` inspects the selected
action's move directly. -/
def moves : List Move := [Move.left, Move.stay, Move.right]

theorem symbols_members :
    none ∈ symbols ∧ some false ∈ symbols ∧ some true ∈ symbols := by
  simp [symbols]

theorem moves_members :
    Move.left ∈ moves ∧ Move.stay ∈ moves ∧ Move.right ∈ moves := by
  simp [moves]

/-- Dispatch an output coordinate to its state, head, presence, or value
block.  This is polymorphic because both encodings and semantic kernels use
the same layout. -/
def blockDispatch (M : UniformTM) (n budget : Nat) {A : Type}
    (state : Fin M.stateCount → A)
    (head present value : Fin (tapeLength n budget) → A)
    (o : Fin (configWidth M n budget)) : A :=
  if hstate : o.val < M.stateCount then
    state ⟨o.val, hstate⟩
  else if hhead : o.val < M.stateCount + tapeLength n budget then
    head ⟨o.val - M.stateCount, by omega⟩
  else if hpresent : o.val < M.stateCount + 2 * tapeLength n budget then
    present ⟨o.val - (M.stateCount + tapeLength n budget), by omega⟩
  else
    value ⟨o.val - (M.stateCount + 2 * tapeLength n budget), by
      have hout := o.isLt
      simp only [configWidth] at hout
      omega⟩

@[simp] theorem blockDispatch_state (M : UniformTM) (n budget : Nat) {A : Type}
    (state : Fin M.stateCount → A)
    (head present value : Fin (tapeLength n budget) → A)
    (q : Fin M.stateCount) :
    blockDispatch M n budget state head present value
      (stateIndex M n budget q) = state q := by
  simp [blockDispatch, stateIndex]

@[simp] theorem blockDispatch_head (M : UniformTM) (n budget : Nat) {A : Type}
    (state : Fin M.stateCount → A)
    (head present value : Fin (tapeLength n budget) → A)
    (i : Fin (tapeLength n budget)) :
    blockDispatch M n budget state head present value
      (headIndex M n budget i) = head i := by
  simp [blockDispatch, headIndex]

@[simp] theorem blockDispatch_present (M : UniformTM) (n budget : Nat) {A : Type}
    (state : Fin M.stateCount → A)
    (head present value : Fin (tapeLength n budget) → A)
    (i : Fin (tapeLength n budget)) :
    blockDispatch M n budget state head present value
      (tapePresentIndex M n budget i) = present i := by
  simp only [blockDispatch, tapePresentIndex]
  split <;> rename_i hs
  · omega
  split <;> rename_i hh
  · omega
  split <;> rename_i hp
  · congr 1; apply Fin.ext; simp
  · omega

@[simp] theorem blockDispatch_value (M : UniformTM) (n budget : Nat) {A : Type}
    (state : Fin M.stateCount → A)
    (head present value : Fin (tapeLength n budget) → A)
    (i : Fin (tapeLength n budget)) :
    blockDispatch M n budget state head present value
      (tapeValueIndex M n budget i) = value i := by
  simp only [blockDispatch, tapeValueIndex]
  split <;> rename_i hs
  · omega
  split <;> rename_i hh
  · omega
  split <;> rename_i hp
  · omega
  · congr 1; apply Fin.ext; simp

/-! ## Boolean access, scan, and row selection -/

def stateBit (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget)) (q : Fin M.stateCount) : Bool :=
  v (stateIndex M n budget q)

def headBit (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget))
    (i : Fin (tapeLength n budget)) : Bool :=
  v (headIndex M n budget i)

def presentBit (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget))
    (i : Fin (tapeLength n budget)) : Bool :=
  v (tapePresentIndex M n budget i)

def valueBit (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget))
    (i : Fin (tapeLength n budget)) : Bool :=
  v (tapeValueIndex M n budget i)

@[simp] theorem stateBit_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (q : Fin M.stateCount) :
    stateBit M n budget (encodeConfig M c) q = decide (q = c.state) := by
  simp [stateBit]

@[simp] theorem headBit_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (i : Fin (tapeLength n budget)) :
    headBit M n budget (encodeConfig M c) i = decide (i = c.head) := by
  simp [headBit]

@[simp] theorem presentBit_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (i : Fin (tapeLength n budget)) :
    presentBit M n budget (encodeConfig M c) i = symbolPresent (c.tape i) := by
  simp [presentBit]

@[simp] theorem valueBit_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (i : Fin (tapeLength n budget)) :
    valueBit M n budget (encodeConfig M c) i = symbolValue (c.tape i) := by
  simp [valueBit]

private theorem any_finRange_eq (k : Nat) (chosen : Fin k) (f : Fin k → Bool) :
    (List.finRange k).any (fun i => decide (i = chosen) && f i) = f chosen := by
  apply Bool.eq_iff_iff.mpr
  simp

/-- Presence rail selected by the one-hot head block. -/
def scanPresent (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget)) : Bool :=
  (List.finRange (tapeLength n budget)).any
    (fun i => headBit M n budget v i && presentBit M n budget v i)

/-- Value rail selected by the same one-hot head block. -/
def scanValue (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget)) : Bool :=
  (List.finRange (tapeLength n budget)).any
    (fun i => headBit M n budget v i && valueBit M n budget v i)

@[simp] theorem scanPresent_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) :
    scanPresent M n budget (encodeConfig M c) = symbolPresent (c.tape c.head) := by
  simp only [scanPresent, headBit_encodeConfig, presentBit_encodeConfig]
  exact any_finRange_eq _ c.head _

@[simp] theorem scanValue_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) :
    scanValue M n budget (encodeConfig M c) = symbolValue (c.tape c.head) := by
  simp only [scanValue, headBit_encodeConfig, valueBit_encodeConfig]
  exact any_finRange_eq _ c.head _

/-- Compare the scanned canonical rail pair with one compile-time symbol. -/
def symbolGuard (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget)) (symbol : Option Bool) : Bool :=
  decide (scanPresent M n budget v = symbolPresent symbol) &&
    decide (scanValue M n budget v = symbolValue symbol)

@[simp] theorem symbolGuard_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (symbol : Option Bool) :
    symbolGuard M n budget (encodeConfig M c) symbol =
      decide (symbol = c.tape c.head) := by
  rw [symbolGuard, scanPresent_encodeConfig, scanValue_encodeConfig]
  cases symbol <;> cases h : c.tape c.head <;>
    simp_all [symbolPresent, symbolValue]
  case some.some a b => cases a <;> cases b <;> simp

/-- One state/symbol row guard. -/
def branch (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget)) (q : Fin M.stateCount)
    (symbol : Option Bool) : Bool :=
  stateBit M n budget v q && symbolGuard M n budget v symbol

@[simp] theorem branch_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (q : Fin M.stateCount)
    (symbol : Option Bool) :
    branch M n budget (encodeConfig M c) q symbol =
      (decide (q = c.state) && decide (symbol = c.tape c.head)) := by
  simp [branch]

/-- False-seeded disjunction of a fixed predicate over every state/symbol
transition row.  The public `M.step` is the sole action source. -/
def actionOr (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget))
    (predicate : (Fin M.stateCount × Option Bool × Move) → Bool) : Bool :=
  (List.finRange M.stateCount).any fun q =>
    symbols.any fun symbol =>
      branch M n budget v q symbol && predicate (M.step q symbol)

@[simp] theorem actionOr_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget)
    (predicate : (Fin M.stateCount × Option Bool × Move) → Bool) :
    actionOr M n budget (encodeConfig M c) predicate =
      predicate (M.step c.state (c.tape c.head)) := by
  apply Bool.eq_iff_iff.mpr
  cases hs : c.tape c.head with
  | none => simp [actionOr, branch_encodeConfig, symbols, hs]
  | some b => cases b <;> simp [actionOr, branch_encodeConfig, symbols, hs]

/-! ## One-step output rails -/

def nextStateBit (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget)) (q : Fin M.stateCount) : Bool :=
  actionOr M n budget v (fun action => decide (q = action.1))

/-- The selected action has the specified move.  This public rail is
intentionally reserved for P1b-3 circuit compilation; pure `encodedStep` does
not consume it because `nextHeadBit` inspects the selected action directly. -/
def moveBit (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget)) (move : Move) : Bool :=
  actionOr M n budget v (fun action => decide (move = action.2.2))

def writePresent (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget)) : Bool :=
  actionOr M n budget v (fun action => symbolPresent action.2.1)

def writeValue (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget)) : Bool :=
  actionOr M n budget v (fun action => symbolValue action.2.1)

def nextHeadBit (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget))
    (i : Fin (tapeLength n budget)) : Bool :=
  (List.finRange (tapeLength n budget)).any fun old =>
    headBit M n budget v old &&
      actionOr M n budget v
        (fun action => decide (i = moveHead old action.2.2))

def nextPresent (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget))
    (i : Fin (tapeLength n budget)) : Bool :=
  if headBit M n budget v i then writePresent M n budget v
  else presentBit M n budget v i

def nextValue (M : UniformTM) (n budget : Nat)
    (v : Bitstring (configWidth M n budget))
    (i : Fin (tapeLength n budget)) : Bool :=
  if headBit M n budget v i then writeValue M n budget v
  else valueBit M n budget v i

@[simp] theorem nextStateBit_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (q : Fin M.stateCount) :
    nextStateBit M n budget (encodeConfig M c) q =
      decide (q = (M.step c.state (c.tape c.head)).1) := by
  simp [nextStateBit]

@[simp] theorem moveBit_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (move : Move) :
    moveBit M n budget (encodeConfig M c) move =
      decide (move = (M.step c.state (c.tape c.head)).2.2) := by
  simp [moveBit]

@[simp] theorem writePresent_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) :
    writePresent M n budget (encodeConfig M c) =
      symbolPresent (M.step c.state (c.tape c.head)).2.1 := by
  simp [writePresent]

@[simp] theorem writeValue_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) :
    writeValue M n budget (encodeConfig M c) =
      symbolValue (M.step c.state (c.tape c.head)).2.1 := by
  simp [writeValue]

@[simp] theorem nextHeadBit_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (i : Fin (tapeLength n budget)) :
    nextHeadBit M n budget (encodeConfig M c) i =
      decide (i = moveHead c.head (M.step c.state (c.tape c.head)).2.2) := by
  simp only [nextHeadBit, headBit_encodeConfig, actionOr_encodeConfig]
  exact any_finRange_eq _ c.head _

@[simp] theorem nextPresent_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (i : Fin (tapeLength n budget)) :
    nextPresent M n budget (encodeConfig M c) i =
      symbolPresent (if i = c.head then
        (M.step c.state (c.tape c.head)).2.1 else c.tape i) := by
  by_cases hi : i = c.head <;>
    simp [nextPresent, hi, symbolPresent]

@[simp] theorem nextValue_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (i : Fin (tapeLength n budget)) :
    nextValue M n budget (encodeConfig M c) i =
      symbolValue (if i = c.head then
        (M.step c.state (c.tape c.head)).2.1 else c.tape i) := by
  by_cases hi : i = c.head <;>
    simp [nextValue, hi, symbolValue]

/-- Pure Boolean one-step transform in the fixed four-block layout.  No claim
is made for malformed Boolean vectors. -/
def encodedStep (M : UniformTM) (n budget : Nat) :
    Bitstring (configWidth M n budget) → Bitstring (configWidth M n budget) :=
  fun v => blockDispatch M n budget
    (nextStateBit M n budget v)
    (nextHeadBit M n budget v)
    (nextPresent M n budget v)
    (nextValue M n budget v)

/-- Headline exactness on canonical encodings. -/
theorem encodedStep_encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) :
    encodedStep M n budget (encodeConfig M c) =
      encodeConfig M (M.stepConfig c) := by
  funext o
  rcases configIndex_cover M n budget o with
    ⟨q, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp [encodedStep, UniformTM.stepConfig]
  · simp [encodedStep, UniformTM.stepConfig]
  · simp [encodedStep, UniformTM.stepConfig]
  · simp [encodedStep, UniformTM.stepConfig]

/-- Repeated pure steps agree with `UniformTM.run`, in `Nat.iterate`
orientation. -/
theorem encodedStep_iterate_run (M : UniformTM) {n budget : Nat}
    (t : Nat) (c : Config M.stateCount n budget) :
    (encodedStep M n budget)^[t] (encodeConfig M c) =
      encodeConfig M (M.run t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih, encodedStep_encodeConfig]
      rfl

/-! ## Conditional bundle iteration -/

/-- Semantic contract required of a caller-supplied one-step bundle.  This
slice deliberately constructs no witness. -/
def StepSpec (M : UniformTM) {n budget : Nat}
    (S : DagBundle (configWidth M n budget) (configWidth M n budget)) : Prop :=
  ∀ c : Config M.stateCount n budget,
    S.evalFun (encodeConfig M c) = encodeConfig M (M.stepConfig c)

theorem stepSpec_of_evalFun (M : UniformTM) {n budget : Nat}
    (S : DagBundle (configWidth M n budget) (configWidth M n budget))
    (h : S.evalFun = encodedStep M n budget) : StepSpec M S := by
  intro c
  rw [h]
  exact encodedStep_encodeConfig M c

theorem iterateBundle_stepSpec (M : UniformTM) {n budget : Nat}
    (S : DagBundle (configWidth M n budget) (configWidth M n budget))
    (h : StepSpec M S) (t : Nat) (c : Config M.stateCount n budget) :
    (iterateBundle S t).evalFun (encodeConfig M c) =
      encodeConfig M (M.run t c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      funext o
      rw [DagBundle.evalFun_apply, iterateBundle_succ, evalOutput_substBundle]
      change S.evalFun ((iterateBundle S t).evalFun (encodeConfig M c)) o = _
      rw [ih, h (M.run t c)]
      rfl

/-- Compose the conditional run iterate over the exact two-gate initial
bundle. -/
def runBundle (M : UniformTM) (n budget : Nat)
    (S : DagBundle (configWidth M n budget) (configWidth M n budget))
    (t : Nat) : EncodedConfig M n budget :=
  substBundle (iterateBundle S t) (initialBundle M n budget)

@[simp] theorem runBundle_gates (M : UniformTM) {n budget : Nat}
    (S : DagBundle (configWidth M n budget) (configWidth M n budget)) (t : Nat) :
    (runBundle M n budget S t).gates = 2 + t * S.gates := by
  simp [runBundle]

theorem runBundle_spec (M : UniformTM) {n budget : Nat}
    (S : DagBundle (configWidth M n budget) (configWidth M n budget))
    (h : StepSpec M S) (t : Nat) :
    Spec (runBundle M n budget S t)
      (fun x => M.run t (initialConfig M budget x)) := by
  intro x o
  rw [runBundle, evalOutput_substBundle]
  change (iterateBundle S t).evalFun (initialBundle M n budget |>.evalFun x) o = _
  have hi : (initialBundle M n budget).evalFun x =
      encodeConfig M (initialConfig M budget x) := by
    funext j
    exact initialBundle_spec M n budget x j
  rw [hi, iterateBundle_stepSpec M S h t]

theorem runBundle_accept_iff (M : UniformTM) {n budget : Nat}
    (S : DagBundle (configWidth M n budget) (configWidth M n budget))
    (h : StepSpec M S) (t : Nat) (x : Bitstring n) :
    (runBundle M n budget S t).evalOutput
        (stateIndex M n budget M.accept) x = true ↔ AcceptsAt M budget t x := by
  rw [runBundle_spec M S h t x, encodeConfig_state]
  simp [AcceptsAt, eq_comm]

end Pnp3.Complexity.Uniform.V1.Circuit
