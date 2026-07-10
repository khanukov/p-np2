import Pnp4.Frontier.StreamingMagnification.StandardDAGMCSP
import Mathlib.Tactic
import Mathlib.Data.List.GetD

/-!
# A canonical fixed-length codec for standard Boolean DAG circuits

The external code is literally a function on `Fin codeLength`.  The first
two little-endian words contain the actual number of gates and the output
wire.  They are followed by exactly `s` fixed-width slots.  Every slot has a
three-bit tag and two reference words.  Five tags describe gates and a sixth
tag is reserved for padding; the remaining two tags are rejected.

Canonical encodings use zero in every semantically unused field and use only
zeroed padding slots after the active prefix.  Consequently decoding is
injective on valid circuit encodings rather than quotienting by junk bits.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace DAGCodec

open StandardDAG

/-- Enough bits for every gate count, output reference, and gate reference.
The `+ 2` makes this positive even at `n = s = 0`. -/
def wordWidth (n s : Nat) : Nat := Nat.clog 2 (n + s + 2)

/-- Three tag bits and two fixed-width reference fields. -/
def slotWidth (n s : Nat) : Nat :=
  3 + (wordWidth n s + wordWidth n s)

/-- Two header words followed by exactly `s` slots. -/
def codeLength (n s : Nat) : Nat :=
  (wordWidth n s + wordWidth n s) + s * slotWidth n s

/-- Externally visible, exactly sized bit strings. -/
abbrev BitString (length : Nat) := Fin length -> Bool

/-- The concrete external type of circuit bodies. -/
abbrev Code (n s : Nat) := BitString (codeLength n s)

/-- Turn a finite word into its little-endian bit function. -/
def bitsOfWord {w : Nat} (word : BitVec w) : Fin w -> Bool :=
  word.getLsb

/-- Reassemble a little-endian bit function as a finite word. -/
def wordOfBits {w : Nat} (bits : Fin w -> Bool) : BitVec w :=
  (BitVec.ofBoolListLE (List.ofFn bits)).cast (by simp)

@[simp] theorem wordOfBits_bitsOfWord {w : Nat} (word : BitVec w) :
    wordOfBits (bitsOfWord word) = word := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [wordOfBits, BitVec.getLsbD_cast,
    BitVec.getLsbD_ofBoolListLE]
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp only [List.getElem_ofFn, bitsOfWord]
  exact (BitVec.getLsbD_eq_getElem hi).symm

@[simp] theorem wordOfBits_getLsb {w : Nat} (word : BitVec w) :
    wordOfBits (fun i => word.getLsb i) = word := by
  simpa [bitsOfWord] using wordOfBits_bitsOfWord word

/-- Fixed-width little-endian encoding of a natural number. -/
def encodeNat (w value : Nat) : BitVec w := BitVec.ofNat w value

/-- Executable unsigned decoding of a word. -/
def decodeNat {w : Nat} (word : BitVec w) : Nat := word.toNat

theorem decodeNat_encodeNat {w value : Nat} (hvalue : value < 2 ^ w) :
    decodeNat (encodeNat w value) = value := by
  simp [decodeNat, encodeNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvalue]

theorem two_pow_wordWidth_ge (n s : Nat) :
    n + s + 2 <= 2 ^ wordWidth n s := by
  simpa [wordWidth] using Nat.le_pow_clog (b := 2) (by omega) (n + s + 2)

theorem wordWidth_pos (n s : Nat) : 0 < wordWidth n s := by
  apply Nat.clog_pos (b := 2) (by omega)
  omega

/-- The conventional paper-size bounded circuit type. -/
abbrev BoundedCircuit (n s : Nat) :=
  { circuit : FlatCircuit n // circuit.gateCount <= s }

theorem gateCount_fits {n s : Nat} (circuit : BoundedCircuit n s) :
    circuit.val.gateCount < 2 ^ wordWidth n s := by
  apply lt_of_lt_of_le (b := n + s + 2)
  · omega
  · exact two_pow_wordWidth_ge n s

theorem output_fits {n s : Nat} (circuit : BoundedCircuit n s) :
    circuit.val.val.output < 2 ^ wordWidth n s := by
  apply lt_of_lt_of_le (b := n + s + 2)
  · have houtput := circuit.val.property.2.2
    have hcount : circuit.val.val.gateCount <= s := by
      simpa [FlatCircuit.gateCount] using circuit.property
    omega
  · exact two_pow_wordWidth_ge n s

/-- Every reference carried by a gate fits one `w`-bit word. -/
def GateRefsFit (w : Nat) : FlatGate -> Prop
  | .const _ => True
  | .notGate src => src < 2 ^ w
  | .andGate left right | .orGate left right =>
      left < 2 ^ w ∧ right < 2 ^ w

theorem valid_gate_refs_fit {n s i : Nat} {gate : FlatGate}
    (hi : i < s) (hgate : gate.Valid n i) :
    GateRefsFit (wordWidth n s) gate := by
  have hcap : n + i < 2 ^ wordWidth n s := by
    apply lt_of_lt_of_le (b := n + s + 2)
    · omega
    · exact two_pow_wordWidth_ge n s
  cases gate with
  | const value => trivial
  | notGate src =>
      exact lt_trans hgate hcap
  | andGate left right =>
      exact ⟨lt_trans hgate.1 hcap, lt_trans hgate.2 hcap⟩
  | orGate left right =>
      exact ⟨lt_trans hgate.1 hcap, lt_trans hgate.2 hcap⟩

/-- The source gate at a natural position below the actual gate count. -/
def circuitGate {n s : Nat} (circuit : BoundedCircuit n s)
    (i : Nat) (hi : i < circuit.val.gateCount) : FlatGate :=
  circuit.val.val.gates.get ⟨i, by
    rw [circuit.val.gates_length]
    exact hi⟩

theorem circuitGate_valid {n s : Nat} (circuit : BoundedCircuit n s)
    (i : Nat) (hi : i < circuit.val.gateCount) :
    (circuitGate circuit i hi).Valid n i := by
  let j : Fin circuit.val.val.gates.length := ⟨i, by
    rw [circuit.val.gates_length]
    exact hi⟩
  simpa [circuitGate, j] using circuit.val.property.2.1 j

/-! ## Raw slots and canonical slot forms -/

/-- Six collision-free meanings for the three-bit tag. -/
inductive SlotTag where
  | constFalse
  | constTrue
  | notGate
  | andGate
  | orGate
  | pad
  deriving DecidableEq, Repr

namespace SlotTag

/-- Numeric three-bit tag assignment.  Values six and seven remain invalid. -/
def code : SlotTag -> Nat
  | .constFalse => 0
  | .constTrue => 1
  | .notGate => 2
  | .andGate => 3
  | .orGate => 4
  | .pad => 5

/-- Partial parser for the six admitted tags. -/
def ofCode : Nat -> Option SlotTag
  | 0 => some .constFalse
  | 1 => some .constTrue
  | 2 => some .notGate
  | 3 => some .andGate
  | 4 => some .orGate
  | 5 => some .pad
  | _ => none

@[simp] theorem ofCode_code (tag : SlotTag) : ofCode tag.code = some tag := by
  cases tag <;> rfl

theorem code_lt_eight (tag : SlotTag) : tag.code < 2 ^ 3 := by
  cases tag <;> decide

end SlotTag

/-- A parsed but not yet validated fixed slot. -/
structure RawSlot (w : Nat) where
  tag : BitVec 3
  left : BitVec w
  right : BitVec w
  deriving DecidableEq, Repr

namespace RawSlot

/-- Executable tag parser. -/
def parsedTag {w : Nat} (slot : RawSlot w) : Option SlotTag :=
  SlotTag.ofCode slot.tag.toNat

/-- Total gate projection.  It is used only after `IsActive` has succeeded;
the default branch makes the parser itself total and executable. -/
def toGate {w : Nat} (slot : RawSlot w) : FlatGate :=
  match slot.parsedTag with
  | some .constFalse => .const false
  | some .constTrue => .const true
  | some .notGate => .notGate slot.left.toNat
  | some .andGate => .andGate slot.left.toNat slot.right.toNat
  | some .orGate => .orGate slot.left.toNat slot.right.toNat
  | some .pad | none => .const false

/-- Active slots have a gate tag and canonical zero dummy fields. -/
def IsActive {w : Nat} (slot : RawSlot w) : Prop :=
  match slot.parsedTag with
  | some .constFalse | some .constTrue => slot.left = 0 ∧ slot.right = 0
  | some .notGate => slot.right = 0
  | some .andGate | some .orGate => True
  | some .pad | none => False

/-- Inactive slots use the unique all-zero `PAD` record. -/
def IsPadding {w : Nat} (slot : RawSlot w) : Prop :=
  slot.parsedTag = some .pad ∧ slot.left = 0 ∧ slot.right = 0

instance instDecidableIsActive {w : Nat} (slot : RawSlot w) :
    Decidable slot.IsActive := by
  unfold IsActive
  split <;> infer_instance

instance instDecidableIsPadding {w : Nat} (slot : RawSlot w) :
    Decidable slot.IsPadding := by
  unfold IsPadding
  infer_instance

/-- The unique canonical padding record. -/
def padding (w : Nat) : RawSlot w where
  tag := encodeNat 3 SlotTag.pad.code
  left := 0
  right := 0

/-- Canonical slot encoding of one gate. -/
def ofGate (w : Nat) : FlatGate -> RawSlot w
  | .const false =>
      { tag := encodeNat 3 SlotTag.constFalse.code, left := 0, right := 0 }
  | .const true =>
      { tag := encodeNat 3 SlotTag.constTrue.code, left := 0, right := 0 }
  | .notGate src =>
      { tag := encodeNat 3 SlotTag.notGate.code
        left := encodeNat w src, right := 0 }
  | .andGate left right =>
      { tag := encodeNat 3 SlotTag.andGate.code
        left := encodeNat w left, right := encodeNat w right }
  | .orGate left right =>
      { tag := encodeNat 3 SlotTag.orGate.code
        left := encodeNat w left, right := encodeNat w right }

@[simp] theorem parsedTag_padding (w : Nat) :
    (padding w).parsedTag = some .pad := by
  simp [padding, parsedTag, encodeNat, BitVec.toNat_ofNat,
    SlotTag.code, SlotTag.ofCode]

@[simp] theorem isPadding_padding (w : Nat) : (padding w).IsPadding := by
  unfold IsPadding
  rw [parsedTag_padding]
  simp [padding]

@[simp] theorem parsedTag_ofGate (w : Nat) (gate : FlatGate) :
    (ofGate w gate).parsedTag = some (match gate with
      | .const false => .constFalse
      | .const true => .constTrue
      | .notGate _ => .notGate
      | .andGate _ _ => .andGate
      | .orGate _ _ => .orGate) := by
  cases gate with
  | const value => cases value <;> simp [ofGate, parsedTag, encodeNat,
      BitVec.toNat_ofNat, SlotTag.code, SlotTag.ofCode]
  | notGate src => simp [ofGate, parsedTag, encodeNat,
      BitVec.toNat_ofNat, SlotTag.code, SlotTag.ofCode]
  | andGate left right => simp [ofGate, parsedTag, encodeNat,
      BitVec.toNat_ofNat, SlotTag.code, SlotTag.ofCode]
  | orGate left right => simp [ofGate, parsedTag, encodeNat,
      BitVec.toNat_ofNat, SlotTag.code, SlotTag.ofCode]

@[simp] theorem isActive_ofGate (w : Nat) (gate : FlatGate) :
    (ofGate w gate).IsActive := by
  unfold IsActive
  rw [parsedTag_ofGate]
  cases gate with
  | const value => cases value <;> simp [ofGate]
  | notGate src => simp [ofGate]
  | andGate left right => simp
  | orGate left right => simp

theorem toGate_ofGate {w : Nat} (gate : FlatGate)
    (hrefs : GateRefsFit w gate) :
    (ofGate w gate).toGate = gate := by
  unfold toGate
  rw [parsedTag_ofGate]
  cases gate with
  | const value => cases value <;> rfl
  | notGate src =>
      simp [ofGate, encodeNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hrefs]
  | andGate left right =>
      simp [ofGate, encodeNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hrefs.1, Nat.mod_eq_of_lt hrefs.2]
  | orGate left right =>
      simp [ofGate, encodeNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hrefs.1, Nat.mod_eq_of_lt hrefs.2]

end RawSlot

/-! ## Exact bit layout -/

@[ext] theorem RawSlot.ext {w : Nat} {left right : RawSlot w}
    (htag : left.tag = right.tag)
    (hleft : left.left = right.left)
    (hright : left.right = right.right) : left = right := by
  cases left
  cases right
  simp_all

/-- Flatten one typed slot to its tag/left/right bit positions. -/
def packSlotBits {w : Nat} (slot : RawSlot w) :
    Fin (3 + (w + w)) -> Bool := fun index =>
  match finSumFinEquiv.symm index with
  | .inl tagIndex => slot.tag.getLsb tagIndex
  | .inr refsIndex =>
      match finSumFinEquiv.symm refsIndex with
      | .inl leftIndex => slot.left.getLsb leftIndex
      | .inr rightIndex => slot.right.getLsb rightIndex

@[simp] theorem packSlotBits_tag {w : Nat} (slot : RawSlot w) (i : Fin 3) :
    packSlotBits slot (finSumFinEquiv (.inl i)) = slot.tag.getLsb i := by
  unfold packSlotBits
  simp only [Equiv.symm_apply_apply]

@[simp] theorem packSlotBits_left {w : Nat} (slot : RawSlot w) (i : Fin w) :
    packSlotBits slot
      (finSumFinEquiv (.inr (finSumFinEquiv (.inl i)))) =
      slot.left.getLsb i := by
  unfold packSlotBits
  simp only [Equiv.symm_apply_apply]

@[simp] theorem packSlotBits_right {w : Nat} (slot : RawSlot w) (i : Fin w) :
    packSlotBits slot
      (finSumFinEquiv (.inr (finSumFinEquiv (.inr i)))) =
      slot.right.getLsb i := by
  unfold packSlotBits
  simp only [Equiv.symm_apply_apply]

/-- Reassemble one typed slot from its exact bit positions. -/
def unpackSlotBits {w : Nat} (bits : Fin (3 + (w + w)) -> Bool) :
    RawSlot w where
  tag := wordOfBits fun i => bits (finSumFinEquiv (.inl i))
  left := wordOfBits fun i =>
    bits (finSumFinEquiv (.inr (finSumFinEquiv (.inl i))))
  right := wordOfBits fun i =>
    bits (finSumFinEquiv (.inr (finSumFinEquiv (.inr i))))

@[simp] theorem unpackSlotBits_packSlotBits {w : Nat} (slot : RawSlot w) :
    unpackSlotBits (packSlotBits slot) = slot := by
  apply RawSlot.ext
  · change wordOfBits (fun i => packSlotBits slot
      (finSumFinEquiv (.inl i))) = slot.tag
    rw [show (fun i => packSlotBits slot (finSumFinEquiv (.inl i))) =
        fun i => slot.tag.getLsb i by
      funext i
      exact packSlotBits_tag slot i]
    exact wordOfBits_getLsb slot.tag
  · change wordOfBits (fun i => packSlotBits slot
      (finSumFinEquiv (.inr (finSumFinEquiv (.inl i))))) = slot.left
    rw [show (fun i => packSlotBits slot
        (finSumFinEquiv (.inr (finSumFinEquiv (.inl i))))) =
        fun i => slot.left.getLsb i by
      funext i
      exact packSlotBits_left slot i]
    exact wordOfBits_getLsb slot.left
  · change wordOfBits (fun i => packSlotBits slot
      (finSumFinEquiv (.inr (finSumFinEquiv (.inr i))))) = slot.right
    rw [show (fun i => packSlotBits slot
        (finSumFinEquiv (.inr (finSumFinEquiv (.inr i))))) =
        fun i => slot.right.getLsb i by
      funext i
      exact packSlotBits_right slot i]
    exact wordOfBits_getLsb slot.right

/-- Flatten two header words and exactly `s` typed slots. -/
def packRawBits {w s : Nat} (gateCount output : BitVec w)
    (slots : Fin s -> RawSlot w) :
    Fin ((w + w) + s * (3 + (w + w))) -> Bool := fun index =>
  match finSumFinEquiv.symm index with
  | .inl headerIndex =>
      match finSumFinEquiv.symm headerIndex with
      | .inl countIndex => gateCount.getLsb countIndex
      | .inr outputIndex => output.getLsb outputIndex
  | .inr slotsIndex =>
      let pair := finProdFinEquiv.symm slotsIndex
      packSlotBits (slots pair.1) pair.2

@[simp] theorem packRawBits_gateCount {w s : Nat}
    (gateCount output : BitVec w) (slots : Fin s -> RawSlot w) (i : Fin w) :
    packRawBits gateCount output slots
      (finSumFinEquiv (.inl (finSumFinEquiv (.inl i)))) =
      gateCount.getLsb i := by
  unfold packRawBits
  simp only [Equiv.symm_apply_apply]

@[simp] theorem packRawBits_output {w s : Nat}
    (gateCount output : BitVec w) (slots : Fin s -> RawSlot w) (i : Fin w) :
    packRawBits gateCount output slots
      (finSumFinEquiv (.inl (finSumFinEquiv (.inr i)))) =
      output.getLsb i := by
  unfold packRawBits
  simp only [Equiv.symm_apply_apply]

@[simp] theorem packRawBits_slot {w s : Nat}
    (gateCount output : BitVec w) (slots : Fin s -> RawSlot w)
    (i : Fin s) (j : Fin (3 + (w + w))) :
    packRawBits gateCount output slots
      (finSumFinEquiv (.inr (finProdFinEquiv (i, j)))) =
      packSlotBits (slots i) j := by
  unfold packRawBits
  simp only [Equiv.symm_apply_apply]

/-- Reassemble two headers and exactly `s` slots from the flat layout. -/
def unpackRawBits {w s : Nat}
    (bits : Fin ((w + w) + s * (3 + (w + w))) -> Bool) :
    BitVec w × BitVec w × (Fin s -> RawSlot w) :=
  let gateCount := wordOfBits fun i =>
    bits (finSumFinEquiv (.inl (finSumFinEquiv (.inl i))))
  let output := wordOfBits fun i =>
    bits (finSumFinEquiv (.inl (finSumFinEquiv (.inr i))))
  let slots := fun i => unpackSlotBits fun j =>
    bits (finSumFinEquiv (.inr (finProdFinEquiv (i, j))))
  (gateCount, output, slots)

@[simp] theorem unpackRawBits_packRawBits {w s : Nat}
    (gateCount output : BitVec w) (slots : Fin s -> RawSlot w) :
    unpackRawBits (packRawBits gateCount output slots) =
      (gateCount, output, slots) := by
  apply Prod.ext
  · change wordOfBits (fun i => packRawBits gateCount output slots
      (finSumFinEquiv (.inl (finSumFinEquiv (.inl i))))) = gateCount
    rw [show (fun i => packRawBits gateCount output slots
        (finSumFinEquiv (.inl (finSumFinEquiv (.inl i))))) =
        fun i => gateCount.getLsb i by
      funext i
      exact packRawBits_gateCount gateCount output slots i]
    exact wordOfBits_getLsb gateCount
  · apply Prod.ext
    · change wordOfBits (fun i => packRawBits gateCount output slots
        (finSumFinEquiv (.inl (finSumFinEquiv (.inr i))))) = output
      rw [show (fun i => packRawBits gateCount output slots
          (finSumFinEquiv (.inl (finSumFinEquiv (.inr i))))) =
          fun i => output.getLsb i by
        funext i
        exact packRawBits_output gateCount output slots i]
      exact wordOfBits_getLsb output
    · funext i
      change unpackSlotBits (fun j => packRawBits gateCount output slots
        (finSumFinEquiv (.inr (finProdFinEquiv (i, j))))) = slots i
      rw [show (fun j => packRawBits gateCount output slots
          (finSumFinEquiv (.inr (finProdFinEquiv (i, j))))) =
          packSlotBits (slots i) by
        funext j
        exact packRawBits_slot gateCount output slots i j]
      exact unpackSlotBits_packSlotBits (slots i)

/-! ## Raw and canonical fixed-slot records -/

/-- Typed raw view of a fixed-length code.  It always has exactly `s` slots,
including when `s = 0`. -/
structure RawCode (n s : Nat) where
  gateCount : BitVec (wordWidth n s)
  output : BitVec (wordWidth n s)
  slots : Fin s -> RawSlot (wordWidth n s)

namespace RawCode

@[ext] theorem ext {n s : Nat} {left right : RawCode n s}
    (hgateCount : left.gateCount = right.gateCount)
    (houtput : left.output = right.output)
    (hslots : left.slots = right.slots) : left = right := by
  cases left
  cases right
  simp_all

/-- External flattening to exactly `codeLength n s` bits. -/
def pack {n s : Nat} (raw : RawCode n s) : Code n s :=
  packRawBits raw.gateCount raw.output raw.slots

/-- Total parsing of any external body into its typed raw fields. -/
def unpack {n s : Nat} (code : Code n s) : RawCode n s :=
  let fields := unpackRawBits code
  { gateCount := fields.1
    output := fields.2.1
    slots := fields.2.2 }

@[simp] theorem unpack_pack {n s : Nat} (raw : RawCode n s) :
    unpack raw.pack = raw := by
  cases raw
  simp [unpack, pack]

def gateCountValue {n s : Nat} (raw : RawCode n s) : Nat :=
  raw.gateCount.toNat

def outputValue {n s : Nat} (raw : RawCode n s) : Nat :=
  raw.output.toNat

/-- Canonical typed record of a bounded source circuit. -/
def ofCircuit {n s : Nat} (circuit : BoundedCircuit n s) : RawCode n s where
  gateCount := encodeNat (wordWidth n s) circuit.val.gateCount
  output := encodeNat (wordWidth n s) circuit.val.val.output
  slots := fun i =>
    if hi : i.val < circuit.val.gateCount then
      RawSlot.ofGate (wordWidth n s) (circuitGate circuit i.val hi)
    else
      RawSlot.padding (wordWidth n s)

@[simp] theorem gateCountValue_ofCircuit {n s : Nat}
    (circuit : BoundedCircuit n s) :
    (ofCircuit circuit).gateCountValue = circuit.val.gateCount := by
  simp [ofCircuit, gateCountValue, encodeNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (gateCount_fits circuit)]

@[simp] theorem outputValue_ofCircuit {n s : Nat}
    (circuit : BoundedCircuit n s) :
    (ofCircuit circuit).outputValue = circuit.val.val.output := by
  simp [ofCircuit, outputValue, encodeNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (output_fits circuit)]

theorem slot_ofCircuit_active {n s : Nat}
    (circuit : BoundedCircuit n s) (i : Fin s)
    (hi : i.val < circuit.val.gateCount) :
    (ofCircuit circuit).slots i =
      RawSlot.ofGate (wordWidth n s) (circuitGate circuit i.val hi) := by
  simp [ofCircuit, hi]

theorem slot_ofCircuit_padding {n s : Nat}
    (circuit : BoundedCircuit n s) (i : Fin s)
    (hi : circuit.val.gateCount <= i.val) :
    (ofCircuit circuit).slots i = RawSlot.padding (wordWidth n s) := by
  simp [ofCircuit, Nat.not_lt.mpr hi]

theorem slot_ofCircuit_toGate {n s : Nat}
    (circuit : BoundedCircuit n s) (i : Fin s)
    (hi : i.val < circuit.val.gateCount) :
    ((ofCircuit circuit).slots i).toGate = circuitGate circuit i.val hi := by
  rw [slot_ofCircuit_active circuit i hi]
  apply RawSlot.toGate_ofGate
  simpa using
    (valid_gate_refs_fit (n := n) (s := s) (i := i.val)
      (gate := circuitGate circuit i.val hi)
      (lt_of_lt_of_le hi circuit.property)
      (circuitGate_valid circuit i.val hi))

/-- The first decoded gate-count slots, truncated automatically if a malformed
header claims more than `s` slots.  Canonicality separately rejects that case. -/
def gateList {n s : Nat} (raw : RawCode n s) : List FlatGate :=
  (List.ofFn fun i : Fin s => (raw.slots i).toGate).take raw.gateCountValue

/-- Total projection of a raw record to unchecked circuit data. -/
def toData {n s : Nat} (raw : RawCode n s) : FlatCircuitData where
  gateCount := raw.gateCountValue
  gates := raw.gateList
  output := raw.outputValue

theorem flatCircuitData_ext {left right : FlatCircuitData}
    (hcount : left.gateCount = right.gateCount)
    (hgates : left.gates = right.gates)
    (houtput : left.output = right.output) : left = right := by
  cases left
  cases right
  simp_all

theorem gateList_ofCircuit {n s : Nat} (circuit : BoundedCircuit n s) :
    (ofCircuit circuit).gateList = circuit.val.val.gates := by
  apply List.ext_getElem
  · simp [gateList, circuit.val.gates_length,
      Nat.min_eq_left circuit.property]
  · intro i hleft hright
    simp only [gateList] at hleft ⊢
    rw [List.getElem_take, List.getElem_ofFn]
    have hi : i < circuit.val.gateCount := by
      simpa [circuit.val.gates_length] using hright
    rw [slot_ofCircuit_toGate circuit ⟨i, by omega⟩ hi]
    rfl

@[simp] theorem toData_ofCircuit {n s : Nat}
    (circuit : BoundedCircuit n s) :
    (ofCircuit circuit).toData = circuit.val.val := by
  apply flatCircuitData_ext
  · exact gateCountValue_ofCircuit circuit
  · exact gateList_ofCircuit circuit
  · exact outputValue_ofCircuit circuit

/-- Canonicality is fully decidable: an active gate prefix, unique inactive
padding, and the standard topological validity check. -/
def Canonical {n s : Nat} (raw : RawCode n s) : Prop :=
  raw.gateCountValue <= s ∧
    (∀ i : Fin s, i.val < raw.gateCountValue -> (raw.slots i).IsActive) ∧
    (∀ i : Fin s, raw.gateCountValue <= i.val -> (raw.slots i).IsPadding) ∧
    raw.toData.Valid n

instance instDecidableCanonical {n s : Nat} (raw : RawCode n s) :
    Decidable raw.Canonical := by
  unfold Canonical
  letI : Decidable
      (∀ i : Fin s, i.val < raw.gateCountValue -> (raw.slots i).IsActive) :=
    Fintype.decidableForallFintype
  letI : Decidable
      (∀ i : Fin s, raw.gateCountValue <= i.val -> (raw.slots i).IsPadding) :=
    Fintype.decidableForallFintype
  infer_instance

theorem canonical_ofCircuit {n s : Nat} (circuit : BoundedCircuit n s) :
    (ofCircuit circuit).Canonical := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using circuit.property
  · intro i hi
    rw [gateCountValue_ofCircuit] at hi
    rw [slot_ofCircuit_active circuit i hi]
    exact RawSlot.isActive_ofGate _ _
  · intro i hi
    rw [gateCountValue_ofCircuit] at hi
    rw [slot_ofCircuit_padding circuit i hi]
    exact RawSlot.isPadding_padding _
  · rw [toData_ofCircuit]
    exact circuit.val.property

/-- Executable canonical decoder at the typed-record layer. -/
def decode {n s : Nat} (raw : RawCode n s) : Option (BoundedCircuit n s) :=
  if hcanonical : raw.Canonical then
    some ⟨⟨raw.toData, hcanonical.2.2.2⟩, hcanonical.1⟩
  else
    none

@[simp] theorem decode_ofCircuit {n s : Nat} (circuit : BoundedCircuit n s) :
    (ofCircuit circuit).decode = some circuit := by
  unfold decode
  rw [dif_pos (canonical_ofCircuit circuit)]
  apply congrArg some
  apply Subtype.ext
  apply Subtype.ext
  exact toData_ofCircuit circuit

theorem decode_some_iff_canonical {n s : Nat} (raw : RawCode n s) :
    raw.decode.isSome = true <-> raw.Canonical := by
  simp [decode]

end RawCode

/-! ## Executable external codec -/

/-- Encode a bounded circuit as an exact fixed-length external body. -/
def encode {n s : Nat} (circuit : BoundedCircuit n s) : Code n s :=
  (RawCode.ofCircuit circuit).pack

/-- Parse, canonicality-check, and validity-check an external body. -/
def decode {n s : Nat} (code : Code n s) : Option (BoundedCircuit n s) :=
  (RawCode.unpack code).decode

@[simp] theorem decode_encode {n s : Nat} (circuit : BoundedCircuit n s) :
    decode (encode circuit) = some circuit := by
  simp [decode, encode]

theorem encode_injective {n s : Nat} :
    Function.Injective (@encode n s) := by
  intro left right heq
  have hdecoded := congrArg (@decode n s) heq
  simpa using hdecoded

theorem decode_success_iff_canonical {n s : Nat} (code : Code n s) :
    (decode code).isSome = true <-> (RawCode.unpack code).Canonical := by
  exact RawCode.decode_some_iff_canonical _

/-- A successfully decoded object carries both standard validity and the
paper gate-count bound in its type. -/
theorem decode_valid {n s : Nat} {code : Code n s}
    {circuit : BoundedCircuit n s} (_hdecode : decode code = some circuit) :
    circuit.val.val.Valid n ∧ circuit.val.gateCount <= s := by
  exact ⟨circuit.val.property, circuit.property⟩

/-- A list view records the external finite length definitionally. -/
def encodedBits {n s : Nat} (circuit : BoundedCircuit n s) : List Bool :=
  List.ofFn (encode circuit)

@[simp] theorem encodedBits_length {n s : Nat}
    (circuit : BoundedCircuit n s) :
    (encodedBits circuit).length = codeLength n s := by
  simp [encodedBits]

theorem codeLength_exact_formula (n s : Nat) :
    codeLength n s =
      2 * wordWidth n s + s * (3 + 2 * wordWidth n s) := by
  unfold codeLength slotWidth
  ring

/-- Explicit linear-in-`s`, logarithmic-word upper bound, valid uniformly at
all edge cases because `wordWidth` is always positive. -/
theorem codeLength_le (n s : Nat) :
    codeLength n s <=
      5 * (s + 1) * Nat.clog 2 (n + s + 2) := by
  rw [codeLength_exact_formula]
  have hwidth : 1 <= wordWidth n s := wordWidth_pos n s
  change 2 * wordWidth n s + s * (3 + 2 * wordWidth n s) <=
    5 * (s + 1) * wordWidth n s
  nlinarith

@[simp] theorem wordWidth_zero_zero : wordWidth 0 0 = 1 := by
  norm_num [wordWidth]

@[simp] theorem codeLength_zero_zero : codeLength 0 0 = 2 := by
  norm_num [codeLength, slotWidth, wordWidth]

theorem codeLength_zero_slots (n : Nat) :
    codeLength n 0 = 2 * wordWidth n 0 := by
  rw [codeLength_exact_formula]
  omega

/-! ## Finite exhaustive canonical code collection -/

/-- Every successful canonical body, as an executable finite collection.
This is suitable for a downstream reference minimum search. -/
def canonicalCodes (n s : Nat) : Finset (Code n s) :=
  Finset.univ.filter fun code => (decode code).isSome

@[simp] theorem mem_canonicalCodes_iff {n s : Nat} (code : Code n s) :
    code ∈ canonicalCodes n s <-> (decode code).isSome = true := by
  simp [canonicalCodes]

@[simp] theorem encode_mem_canonicalCodes {n s : Nat}
    (circuit : BoundedCircuit n s) :
    encode circuit ∈ canonicalCodes n s := by
  simp [canonicalCodes]

/-- The ambient search space has exactly `2 ^ codeLength` bodies. -/
theorem card_code (n s : Nat) :
    Fintype.card (Code n s) = 2 ^ codeLength n s := by
  simp [Code, BitString]

end DAGCodec
end StreamingMagnification
end Frontier
end Pnp4
