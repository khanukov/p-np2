import Pnp4.Frontier.StreamingMagnification.StreamMerge

/-!
# Fixed-length wire format for Stream-Merge results

This module gives the five observable `StreamMerge.Result` cases pairwise
distinct three-bit tags.  A found result carries the exact fixed-length DAG
body.  Every body-free result has the unique all-zero body, and the parser
rejects noncanonical bodies on those branches.

The final section exposes the bit graph of both an arbitrary result and the
executable reference Stream-Merge function.  These predicates are merely an
executable graph interface; this module makes no complexity-class claim.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace StreamMergeWire

open StreamMerge

/-! ## Tags and fixed-length layout -/

/-- The five semantic result cases, before their three-bit encoding. -/
inductive WireTag where
  | found
  | noCircuit
  | invalidPrior
  | startPastEnd
  | wrongBlockLength
  deriving DecidableEq, Repr

namespace WireTag

/-- Numeric little-endian tag assignment.  Codes five through seven are
reserved and rejected by the parser. -/
def code : WireTag -> Nat
  | .found => 0
  | .noCircuit => 1
  | .invalidPrior => 2
  | .startPastEnd => 3
  | .wrongBlockLength => 4

/-- Partial inverse of the five admitted tag codes. -/
def ofCode : Nat -> Option WireTag
  | 0 => some .found
  | 1 => some .noCircuit
  | 2 => some .invalidPrior
  | 3 => some .startPastEnd
  | 4 => some .wrongBlockLength
  | _ => none

@[simp] theorem ofCode_code (tag : WireTag) : ofCode tag.code = some tag := by
  cases tag <;> rfl

theorem code_lt_eight (tag : WireTag) : tag.code < 2 ^ 3 := by
  cases tag <;> decide

end WireTag

/-- Three tag bits followed by one exact DAG-code body. -/
def wireLength (n s : Nat) : Nat := 3 + DAGCodec.codeLength n s

/-- The exact fixed-length external result type. -/
abbrev ResultWire (n s : Nat) := DAGCodec.BitString (wireLength n s)

/-- Encode one tag as a three-bit little-endian word. -/
def encodeTag (tag : WireTag) : Fin 3 -> Bool :=
  DAGCodec.bitsOfWord (DAGCodec.encodeNat 3 tag.code)

/-- Parse a three-bit tag, rejecting the three reserved codes. -/
def parseTag (bits : Fin 3 -> Bool) : Option WireTag :=
  WireTag.ofCode (DAGCodec.wordOfBits bits).toNat

@[simp] theorem parseTag_encodeTag (tag : WireTag) :
    parseTag (encodeTag tag) = some tag := by
  unfold parseTag encodeTag
  rw [DAGCodec.wordOfBits_bitsOfWord]
  cases tag <;> decide

/-- Pack the disjoint tag and body coordinates. -/
def pack {n s : Nat} (tag : Fin 3 -> Bool) (body : DAGCodec.Code n s) :
    ResultWire n s := fun index =>
  match finSumFinEquiv.symm index with
  | .inl tagIndex => tag tagIndex
  | .inr bodyIndex => body bodyIndex

/-- Read the three tag bits. -/
def tagBits {n s : Nat} (wire : ResultWire n s) : Fin 3 -> Bool :=
  fun index => wire (finSumFinEquiv (.inl index))

/-- Read the exact circuit-body coordinates. -/
def resultBody {n s : Nat} (wire : ResultWire n s) : DAGCodec.Code n s :=
  fun index => wire (finSumFinEquiv (.inr index))

@[simp] theorem tagBits_pack {n s : Nat} (tag : Fin 3 -> Bool)
    (body : DAGCodec.Code n s) :
    tagBits (pack tag body) = tag := by
  funext index
  simp [tagBits, pack]

@[simp] theorem resultBody_pack {n s : Nat} (tag : Fin 3 -> Bool)
    (body : DAGCodec.Code n s) :
    resultBody (pack tag body) = body := by
  funext index
  simp [resultBody, pack]

/-- The canonical body on every result branch that carries no circuit. -/
def zeroBody (n s : Nat) : DAGCodec.Code n s := fun _ => false

/-- The tag associated to a proof-level Stream-Merge result. -/
def resultTag {n s : Nat} : StreamMerge.Result n s -> WireTag
  | .found _ => .found
  | .noCircuit => .noCircuit
  | .malformed .invalidPrior => .invalidPrior
  | .malformed .startPastEnd => .startPastEnd
  | .malformed .wrongBlockLength => .wrongBlockLength

/-- Serialize all five cases to exactly `3 + DAGCodec.codeLength n s` bits. -/
def serialize {n s : Nat} : StreamMerge.Result n s -> ResultWire n s
  | .found code => pack (encodeTag .found) code
  | .noCircuit => pack (encodeTag .noCircuit) (zeroBody n s)
  | .malformed .invalidPrior =>
      pack (encodeTag .invalidPrior) (zeroBody n s)
  | .malformed .startPastEnd =>
      pack (encodeTag .startPastEnd) (zeroBody n s)
  | .malformed .wrongBlockLength =>
      pack (encodeTag .wrongBlockLength) (zeroBody n s)

@[simp] theorem tagBits_serialize {n s : Nat}
    (result : StreamMerge.Result n s) :
    tagBits (serialize result) = encodeTag (resultTag result) := by
  cases result with
  | found code => simp [serialize, resultTag]
  | noCircuit => simp [serialize, resultTag]
  | malformed reason => cases reason <;> simp [serialize, resultTag]

@[simp] theorem parseTag_serialize {n s : Nat}
    (result : StreamMerge.Result n s) :
    parseTag (tagBits (serialize result)) = some (resultTag result) := by
  simp

/-! ## Canonical parser and exact round trip -/

/-- Parse a result wire.  The found tag accepts its circuit body literally;
all four body-free tags require the canonical zero body. -/
def parse {n s : Nat} (wire : ResultWire n s) :
    Option (StreamMerge.Result n s) :=
  match parseTag (tagBits wire) with
  | some .found => some (.found (resultBody wire))
  | some .noCircuit =>
      if resultBody wire = zeroBody n s then some .noCircuit else none
  | some .invalidPrior =>
      if resultBody wire = zeroBody n s then
        some (.malformed .invalidPrior)
      else none
  | some .startPastEnd =>
      if resultBody wire = zeroBody n s then
        some (.malformed .startPastEnd)
      else none
  | some .wrongBlockLength =>
      if resultBody wire = zeroBody n s then
        some (.malformed .wrongBlockLength)
      else none
  | none => none

@[simp] theorem parse_serialize {n s : Nat}
    (result : StreamMerge.Result n s) :
    parse (serialize result) = some result := by
  cases result with
  | found code => simp [parse, serialize]
  | noCircuit => simp [parse, serialize]
  | malformed reason => cases reason <;> simp [parse, serialize]

/-- Fixed-length serialization is collision-free. -/
theorem serialize_injective {n s : Nat} :
    Function.Injective (@serialize n s) := by
  intro left right heq
  have hparsed := congrArg (@parse n s) heq
  simpa using hparsed

/-! ## Tag disjointness -/

/-- Results with distinct semantic tags have distinct wire encodings. -/
theorem serialize_ne_of_resultTag_ne {n s : Nat}
    {left right : StreamMerge.Result n s}
    (htags : resultTag left ≠ resultTag right) :
    serialize left ≠ serialize right := by
  intro heq
  apply htags
  exact congrArg resultTag (serialize_injective heq)

theorem serialize_found_ne_noCircuit {n s : Nat}
    (code : DAGCodec.Code n s) :
    serialize (.found code) ≠
      serialize (.noCircuit : StreamMerge.Result n s) := by
  apply serialize_ne_of_resultTag_ne
  simp [resultTag]

theorem serialize_found_ne_malformed {n s : Nat}
    (code : DAGCodec.Code n s) (reason : StreamMerge.MalformedReason) :
    serialize (.found code) ≠ serialize (.malformed reason) := by
  apply serialize_ne_of_resultTag_ne
  cases reason <;> simp [resultTag]

theorem serialize_noCircuit_ne_malformed {n s : Nat}
    (reason : StreamMerge.MalformedReason) :
    serialize (.noCircuit : StreamMerge.Result n s) ≠
      serialize (.malformed reason) := by
  apply serialize_ne_of_resultTag_ne
  cases reason <;> simp [resultTag]

theorem serialize_malformed_ne_malformed {n s : Nat}
    {left right : StreamMerge.MalformedReason} (hreasons : left ≠ right) :
    serialize (StreamMerge.Result.malformed left : StreamMerge.Result n s) ≠
      serialize (.malformed right) := by
  apply serialize_ne_of_resultTag_ne
  cases left <;> cases right <;> simp_all [resultTag]

/-! ## Explicit output-bit graph -/

/-- The output bit at a specified position of an already determined result. -/
def outputBit {n s : Nat} (result : StreamMerge.Result n s)
    (position : Fin (wireLength n s)) : Bool :=
  serialize result position

/-- Relational graph of `outputBit`, suitable for bit-by-bit specifications. -/
def OutputBitGraph {n s : Nat} (result : StreamMerge.Result n s)
    (position : Fin (wireLength n s)) (bit : Bool) : Prop :=
  outputBit result position = bit

instance instDecidableOutputBitGraph {n s : Nat}
    (result : StreamMerge.Result n s) (position : Fin (wireLength n s))
    (bit : Bool) : Decidable (OutputBitGraph result position bit) := by
  unfold OutputBitGraph
  infer_instance

theorem outputBitGraph_total {n s : Nat} (result : StreamMerge.Result n s)
    (position : Fin (wireLength n s)) :
    Exists fun bit => OutputBitGraph result position bit :=
  ⟨outputBit result position, rfl⟩

theorem outputBitGraph_functional {n s : Nat}
    {result : StreamMerge.Result n s} {position : Fin (wireLength n s)}
    {left right : Bool}
    (hleft : OutputBitGraph result position left)
    (hright : OutputBitGraph result position right) : left = right := by
  exact hleft.symm.trans hright

/-- Executable output bit of the reference Stream-Merge function. -/
def referenceOutputBit {n s : Nat} (priorCode : DAGCodec.Code n s)
    (blockLength start : Nat) (block : List Bool)
    (position : Fin (wireLength n s)) : Bool :=
  outputBit (StreamMerge.referenceStreamMerge priorCode blockLength start block)
    position

/-- Explicit graph predicate for each bit of the reference result wire. -/
def ReferenceOutputBitGraph {n s : Nat} (priorCode : DAGCodec.Code n s)
    (blockLength start : Nat) (block : List Bool)
    (position : Fin (wireLength n s)) (bit : Bool) : Prop :=
  referenceOutputBit priorCode blockLength start block position = bit

instance instDecidableReferenceOutputBitGraph {n s : Nat}
    (priorCode : DAGCodec.Code n s) (blockLength start : Nat)
    (block : List Bool) (position : Fin (wireLength n s)) (bit : Bool) :
    Decidable
      (ReferenceOutputBitGraph priorCode blockLength start block position bit) := by
  unfold ReferenceOutputBitGraph
  infer_instance

theorem referenceOutputBitGraph_total {n s : Nat}
    (priorCode : DAGCodec.Code n s) (blockLength start : Nat)
    (block : List Bool) (position : Fin (wireLength n s)) :
    Exists fun bit =>
      ReferenceOutputBitGraph priorCode blockLength start block position bit :=
  ⟨referenceOutputBit priorCode blockLength start block position, rfl⟩

theorem referenceOutputBitGraph_functional {n s : Nat}
    {priorCode : DAGCodec.Code n s} {blockLength start : Nat}
    {block : List Bool} {position : Fin (wireLength n s)}
    {left right : Bool}
    (hleft :
      ReferenceOutputBitGraph priorCode blockLength start block position left)
    (hright :
      ReferenceOutputBitGraph priorCode blockLength start block position right) :
    left = right := by
  exact hleft.symm.trans hright

end StreamMergeWire
end StreamingMagnification
end Frontier
end Pnp4
