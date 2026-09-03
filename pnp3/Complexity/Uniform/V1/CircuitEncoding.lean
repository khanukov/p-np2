import Complexity.DagGadgets
import Complexity.Uniform.V1.Machine

/-!
# Direct fixed-width encoding of Uniform V1 configurations

This infrastructure slice fixes the Boolean layout of one configuration and
builds its initial shared DAG bundle.  It contains no transition or run
compiler and no complexity-class bridge.
-/

namespace Pnp3.Complexity.Uniform.V1.Circuit

open Pnp3.ComplexityInterfaces
open Pnp3.ComplexityInterfaces.DagCircuit

/-- The tag rail: only a nonblank tape symbol is present. -/
def symbolPresent : Option Bool → Bool
  | none => false
  | some _ => true

/-- The value rail.  Blank and `some false` both have a false value rail and
are distinguished by `symbolPresent`. -/
def symbolValue : Option Bool → Bool
  | none => false
  | some b => b

/-- Decode a canonical pair of symbol rails.  When the presence rail is false,
the value rail is deliberately ignored; canonical encodings rule out the
malformed `(false, true)` pair separately. -/
def decodeSymbol (present value : Bool) : Option Bool :=
  if present then some value else none

/-- Exact truth table for the canonical three-symbol rail encoding. -/
theorem symbolRails_cases :
    (symbolPresent none, symbolValue none) = (false, false) ∧
    (symbolPresent (some false), symbolValue (some false)) = (true, false) ∧
    (symbolPresent (some true), symbolValue (some true)) = (true, true) := by
  simp [symbolPresent, symbolValue]

/-- Encoding then decoding either rail pair returns the exact three-valued
tape symbol. -/
@[simp] theorem decodeSymbol_roundtrip (symbol : Option Bool) :
    decodeSymbol (symbolPresent symbol) (symbolValue symbol) = symbol := by
  cases symbol with
  | none => rfl
  | some b => cases b <;> rfl

/-- The canonical rail pair uniquely determines the tape symbol. -/
theorem symbolRails_injective :
    Function.Injective (fun symbol => (symbolPresent symbol, symbolValue symbol)) := by
  intro a b h
  have := congrArg (fun rails => decodeSymbol rails.1 rails.2) h
  simpa using this

/-- Canonical symbol encodings never use the malformed `(false, true)` pair. -/
theorem symbolRails_not_malformed (symbol : Option Bool) :
    ¬ (symbolPresent symbol = false ∧ symbolValue symbol = true) := by
  cases symbol with
  | none => simp [symbolPresent, symbolValue]
  | some b => simp [symbolPresent]

/-! ## Fixed layout

The public ordering is state, head, tape-present, tape-value.  Each tape block
has exactly `tapeLength n budget` wires.
-/

/-- Total width of the fixed Boolean encoding. -/
def configWidth (M : UniformTM) (n budget : Nat) : Nat :=
  M.stateCount + 3 * tapeLength n budget

/-- State block: offsets `[0, M.stateCount)`. -/
def stateIndex (M : UniformTM) (n budget : Nat) (q : Fin M.stateCount) :
    Fin (configWidth M n budget) :=
  ⟨q.val, by simp [configWidth, tapeLength]; omega⟩

/-- Head block: immediately after the state block. -/
def headIndex (M : UniformTM) (n budget : Nat)
    (i : Fin (tapeLength n budget)) : Fin (configWidth M n budget) :=
  ⟨M.stateCount + i.val, by simp [configWidth]; omega⟩

/-- Tape presence block: immediately after the head block. -/
def tapePresentIndex (M : UniformTM) (n budget : Nat)
    (i : Fin (tapeLength n budget)) : Fin (configWidth M n budget) :=
  ⟨M.stateCount + tapeLength n budget + i.val, by
    simp [configWidth]; omega⟩

/-- Tape value block: the final block. -/
def tapeValueIndex (M : UniformTM) (n budget : Nat)
    (i : Fin (tapeLength n budget)) : Fin (configWidth M n budget) :=
  ⟨M.stateCount + 2 * tapeLength n budget + i.val, by
    simp [configWidth]; omega⟩

/-- Exact offsets pin the public state/head/presence/value ordering. -/
theorem configIndex_layout (M : UniformTM) (n budget : Nat)
    (q : Fin M.stateCount) (i : Fin (tapeLength n budget)) :
    (stateIndex M n budget q).val = q.val ∧
    (headIndex M n budget i).val = M.stateCount + i.val ∧
    (tapePresentIndex M n budget i).val =
      M.stateCount + tapeLength n budget + i.val ∧
    (tapeValueIndex M n budget i).val =
      M.stateCount + 2 * tapeLength n budget + i.val := by
  simp [stateIndex, headIndex, tapePresentIndex, tapeValueIndex]

/-- The four constructors land in four consecutive disjoint ranges. -/
theorem configIndex_ranges (M : UniformTM) (n budget : Nat)
    (q : Fin M.stateCount) (i : Fin (tapeLength n budget)) :
    (stateIndex M n budget q).val < M.stateCount ∧
    (M.stateCount ≤ (headIndex M n budget i).val ∧
      (headIndex M n budget i).val < M.stateCount + tapeLength n budget) ∧
    (M.stateCount + tapeLength n budget ≤
        (tapePresentIndex M n budget i).val ∧
      (tapePresentIndex M n budget i).val <
        M.stateCount + 2 * tapeLength n budget) ∧
    (M.stateCount + 2 * tapeLength n budget ≤
        (tapeValueIndex M n budget i).val ∧
      (tapeValueIndex M n budget i).val < configWidth M n budget) := by
  simp [stateIndex, headIndex, tapePresentIndex, tapeValueIndex, configWidth]
  omega

/-- Every index constructor is injective within its block. -/
theorem configIndex_injective (M : UniformTM) (n budget : Nat) :
    Function.Injective (stateIndex M n budget) ∧
    Function.Injective (headIndex M n budget) ∧
    Function.Injective (tapePresentIndex M n budget) ∧
    Function.Injective (tapeValueIndex M n budget) := by
  constructor
  · intro a b h
    apply Fin.ext
    simpa [stateIndex] using congrArg Fin.val h
  constructor
  · intro a b h
    apply Fin.ext
    simpa [headIndex] using congrArg Fin.val h
  constructor <;> intro a b h <;> apply Fin.ext
  · simpa [tapePresentIndex] using congrArg Fin.val h
  · simpa [tapeValueIndex] using congrArg Fin.val h

/-- The ranges are pairwise disjoint, including the nonadjacent pairs. -/
theorem configIndex_disjoint (M : UniformTM) (n budget : Nat)
    (q : Fin M.stateCount) (i j : Fin (tapeLength n budget)) :
    stateIndex M n budget q ≠ headIndex M n budget i ∧
    stateIndex M n budget q ≠ tapePresentIndex M n budget i ∧
    stateIndex M n budget q ≠ tapeValueIndex M n budget i ∧
    headIndex M n budget i ≠ tapePresentIndex M n budget j ∧
    headIndex M n budget i ≠ tapeValueIndex M n budget j ∧
    tapePresentIndex M n budget i ≠ tapeValueIndex M n budget j := by
  simp only [Fin.ne_iff_vne]
  simp [stateIndex, headIndex, tapePresentIndex, tapeValueIndex]
  omega

/-! ## Concrete configuration encoding -/

/-- Encode a concrete configuration in the pinned four-block layout.  State
and head blocks are one-hot; the two tape blocks use canonical symbol rails. -/
def encodeConfig (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) : Fin (configWidth M n budget) → Bool :=
  fun o =>
    if _hstate : o.val < M.stateCount then
      decide (o.val = c.state.val)
    else if _hhead : o.val < M.stateCount + tapeLength n budget then
      decide (o.val - M.stateCount = c.head.val)
    else if _hpresent :
        o.val < M.stateCount + 2 * tapeLength n budget then
      symbolPresent (c.tape ⟨o.val - (M.stateCount + tapeLength n budget), by
        omega⟩)
    else
      symbolValue (c.tape ⟨o.val - (M.stateCount + 2 * tapeLength n budget), by
        have hout := o.isLt
        simp only [configWidth] at hout
        omega⟩)

/-- State outputs are the exact equality indicator. -/
@[simp] theorem encodeConfig_state (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (q : Fin M.stateCount) :
    encodeConfig M c (stateIndex M n budget q) = decide (q = c.state) := by
  simp [encodeConfig, stateIndex, Fin.ext_iff]

/-- Head outputs are the exact equality indicator. -/
@[simp] theorem encodeConfig_head (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (i : Fin (tapeLength n budget)) :
    encodeConfig M c (headIndex M n budget i) = decide (i = c.head) := by
  simp [encodeConfig, headIndex, Fin.ext_iff]

/-- Presence outputs expose the exact canonical symbol tag. -/
@[simp] theorem encodeConfig_tapePresent (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (i : Fin (tapeLength n budget)) :
    encodeConfig M c (tapePresentIndex M n budget i) =
      symbolPresent (c.tape i) := by
  simp only [encodeConfig, tapePresentIndex]
  split
  · omega
  split
  · omega
  split
  · congr 2
    apply Fin.ext
    simp
  · omega

/-- Value outputs expose the exact canonical symbol value rail. -/
@[simp] theorem encodeConfig_tapeValue (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (i : Fin (tapeLength n budget)) :
    encodeConfig M c (tapeValueIndex M n budget i) =
      symbolValue (c.tape i) := by
  simp only [encodeConfig, tapeValueIndex]
  split
  · omega
  split
  · omega
  split
  · omega
  · congr 2
    apply Fin.ext
    simp

/-- Reading the two encoded tape rails reconstructs the exact symbol. -/
theorem encodeConfig_tape_decode (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) (i : Fin (tapeLength n budget)) :
    decodeSymbol
      (encodeConfig M c (tapePresentIndex M n budget i))
      (encodeConfig M c (tapeValueIndex M n budget i)) = c.tape i := by
  simp

/-- Exactly one state selector is true. -/
theorem encodeConfig_state_unique (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) :
    ∃! q : Fin M.stateCount,
      encodeConfig M c (stateIndex M n budget q) = true := by
  refine ⟨c.state, by simp, ?_⟩
  intro q hq
  simpa using hq

/-- Exactly one head selector is true. -/
theorem encodeConfig_head_unique (M : UniformTM) {n budget : Nat}
    (c : Config M.stateCount n budget) :
    ∃! i : Fin (tapeLength n budget),
      encodeConfig M c (headIndex M n budget i) = true := by
  refine ⟨c.head, by simp, ?_⟩
  intro i hi
  simpa using hi

/-! ## Bundle specification -/

/-- A fixed-width DAG bundle whose outputs have the configuration layout. -/
abbrev EncodedConfig (M : UniformTM) (n budget : Nat) :=
  DagBundle n (configWidth M n budget)

/-- Exact extensional specification for a configuration-valued function.
Because this is equality with `encodeConfig`, canonical blank rails are pinned
rather than normalized after evaluation. -/
def Spec {M : UniformTM} {n budget : Nat} (B : EncodedConfig M n budget)
    (f : Bitstring n → Config M.stateCount n budget) : Prop :=
  ∀ x o, B.evalOutput o x = encodeConfig M (f x) o

/-- A specified bundle's tape rails decode to the exact concrete symbol. -/
theorem Spec_tape_decode {M : UniformTM} {n budget : Nat}
    {B : EncodedConfig M n budget}
    {f : Bitstring n → Config M.stateCount n budget} (h : Spec B f)
    (x : Bitstring n) (i : Fin (tapeLength n budget)) :
    decodeSymbol
      (B.evalOutput (tapePresentIndex M n budget i) x)
      (B.evalOutput (tapeValueIndex M n budget i) x) = (f x).tape i := by
  rw [h x, h x]
  exact encodeConfig_tape_decode M (f x) i

/-- Exact specification excludes the malformed blank-tag/true-value pair. -/
theorem Spec_tape_not_malformed {M : UniformTM} {n budget : Nat}
    {B : EncodedConfig M n budget}
    {f : Bitstring n → Config M.stateCount n budget} (h : Spec B f)
    (x : Bitstring n) (i : Fin (tapeLength n budget)) :
    ¬ (B.evalOutput (tapePresentIndex M n budget i) x = false ∧
      B.evalOutput (tapeValueIndex M n budget i) x = true) := by
  rw [h x, h x, encodeConfig_tapePresent, encodeConfig_tapeValue]
  exact symbolRails_not_malformed ((f x).tape i)

/-! ## Direct initial bundle -/

private def constantWire {n : Nat} (b : Bool) : DagWire n 2 :=
  if b then DagWire.gate ⟨1, by decide⟩ else DagWire.gate ⟨0, by decide⟩

/-- The initial configuration bundle has one shared false gate and one shared
true gate.  Input values are zero-gate projections; all other outputs select
one of those two constants. -/
def initialBundle (M : UniformTM) (n budget : Nat) : EncodedConfig M n budget where
  gates := 2
  gate := fun i => if i.val = 0 then DagGate.const false else DagGate.const true
  output := fun o =>
    if _hstate : o.val < M.stateCount then
      constantWire (decide (o.val = M.start.val))
    else if _hhead : o.val < M.stateCount + tapeLength n budget then
      constantWire (decide (o.val - M.stateCount = 0))
    else if _hpresent :
        o.val < M.stateCount + 2 * tapeLength n budget then
      constantWire
        (decide (o.val - (M.stateCount + tapeLength n budget) < n))
    else if hinput :
        o.val - (M.stateCount + 2 * tapeLength n budget) < n then
      DagWire.input ⟨o.val - (M.stateCount + 2 * tapeLength n budget), hinput⟩
    else
      constantWire false

@[simp] theorem initialBundle_gates (M : UniformTM) (n budget : Nat) :
    (initialBundle M n budget).gates = 2 := rfl

private theorem eval_constantWire (n : Nat) (b : Bool) (x : Bitstring n) :
    DagCircuit.eval
      { gates := 2
        gate := fun i => if i.val = 0 then DagGate.const false else DagGate.const true
        output := constantWire b }
      x = b := by
  cases b <;>
    simp [DagCircuit.eval, DagCircuit.eval.evalGateAt, constantWire]

private theorem evalOutput_initialBundle (M : UniformTM) (n budget : Nat)
    (o : Fin (configWidth M n budget)) (x : Bitstring n) :
    (initialBundle M n budget).evalOutput o x =
      if _hstate : o.val < M.stateCount then
        decide (o.val = M.start.val)
      else if _hhead : o.val < M.stateCount + tapeLength n budget then
        decide (o.val - M.stateCount = 0)
      else if _hpresent :
          o.val < M.stateCount + 2 * tapeLength n budget then
        decide (o.val - (M.stateCount + tapeLength n budget) < n)
      else if hinput :
          o.val - (M.stateCount + 2 * tapeLength n budget) < n then
        x ⟨o.val - (M.stateCount + 2 * tapeLength n budget), hinput⟩
      else false := by
  simp only [DagBundle.evalOutput, DagBundle.asCircuit, initialBundle]
  split <;> rename_i hstate
  · exact eval_constantWire n _ x
  split <;> rename_i hhead
  · exact eval_constantWire n _ x
  split <;> rename_i hpresent
  · exact eval_constantWire n _ x
  split <;> rename_i hinput
  · rfl
  · exact eval_constantWire n false x

/-- Headline P1b-1 correctness: the direct shared bundle computes the exact
Boolean encoding of `initialConfig` at every output. -/
theorem initialBundle_spec (M : UniformTM) (n budget : Nat) :
    Spec (initialBundle M n budget) (fun x => initialConfig M budget x) := by
  intro x o
  rw [evalOutput_initialBundle]
  unfold encodeConfig
  split <;> rename_i hstate
  · rfl
  split <;> rename_i hhead
  · rfl
  split <;> rename_i hpresent
  · simp only [initialConfig]
    split <;> rename_i hinput
    · simp [hinput, symbolPresent]
    · simp [hinput, symbolPresent]
  · simp only [initialConfig]
    split <;> rename_i hinput
    · rfl
    · rfl

/-- Every output circuit retains the two shared gates and one output-accounting
node, hence has exact size three. -/
@[simp] theorem initialBundle_asCircuit_size (M : UniformTM) (n budget : Nat)
    (o : Fin (configWidth M n budget)) :
    DagCircuit.size ((initialBundle M n budget).asCircuit o) =
      (initialBundle M n budget).gates + 1 := rfl

@[simp] theorem initialBundle_output_size (M : UniformTM) (n budget : Nat)
    (o : Fin (configWidth M n budget)) :
    DagCircuit.size ((initialBundle M n budget).asCircuit o) = 3 := rfl

/-- A concrete nonvacuity pin: at length one and budget zero, the false input
in cell zero is present with value false, while cell one is genuinely blank.
The initial state and head selectors are pinned in the same evaluation. -/
theorem initialBundle_blank_distinction (M : UniformTM) :
    let x : Bitstring 1 := fun _ => false
    let cell0 : Fin (tapeLength 1 0) := ⟨0, by simp [tapeLength]⟩
    let cell1 : Fin (tapeLength 1 0) := ⟨1, by simp [tapeLength]⟩
    (initialBundle M 1 0).evalOutput (stateIndex M 1 0 M.start) x = true ∧
    (initialBundle M 1 0).evalOutput (headIndex M 1 0 cell0) x = true ∧
    (initialBundle M 1 0).evalOutput (tapePresentIndex M 1 0 cell0) x = true ∧
    (initialBundle M 1 0).evalOutput (tapeValueIndex M 1 0 cell0) x = false ∧
    (initialBundle M 1 0).evalOutput (tapePresentIndex M 1 0 cell1) x = false ∧
    (initialBundle M 1 0).evalOutput (tapeValueIndex M 1 0 cell1) x = false := by
  dsimp
  have h := initialBundle_spec M 1 0
  unfold Spec at h
  simp only [h]
  simp [initialConfig, tapeLength, symbolPresent, symbolValue]

end Pnp3.Complexity.Uniform.V1.Circuit
