import Pnp4.Frontier.StreamingMagnification.DAGCodec
import Pnp4.Frontier.StreamingMagnification.TotalSearch
import Batteries.Data.BitVec.Lemmas
import Batteries.Data.Fin.Lemmas
import Mathlib.Tactic

/-!
# Executable reference specification for Stream-Merge

This module defines the oracle-free Stream-Merge *reference function*.  It
searches the finite space of fixed-length standard-DAG codes, first by the
number of internal gates and then by the physical serialized bit order
(`false < true`, with position zero compared first).  Successful decoding is
the canonicality filter, so malformed and noncanonical bodies are never
returned.

The function is deliberately executable and obtains its minimum by explicit
finite search.  It is also deliberately **not** an implementation in
`StreamingRAM.Program`: it exhausts up to `2 ^ codeLength` bodies and may
evaluate whole truth tables.  Consequently no time, update-gap, reporting, or
space bound follows from this module.  A later operational implementation has
to refine this reference result and prove its own trace/resource bounds.

The nominal block length is separate from the actual block.  At a prefix of
length `start`, the exact required length is

`min blockLength (2 ^ n - start)`.

Thus the same definition handles a final partial block and the small-length
case in which the nominal block is larger than the entire truth table.
-/

namespace Pnp4
namespace Frontier
namespace StreamingMagnification
namespace StreamMerge

open StandardDAG
open TotalSearch

/-! ## Physical serialized order -/

/-- The serialized body regarded as a big-endian finite number.  This is the
numeric rank for lexicographic order on physical positions: position zero is
the most significant bit and `false < true`.

This is intentionally different from `DAGCodec.wordOfBits`, which decodes the
little-endian words *inside* the chosen circuit layout. -/
def serializedIndex {n s : Nat} (code : DAGCodec.Code n s) :
    Fin (2 ^ DAGCodec.codeLength n s) :=
  (BitVec.ofFnBE code).toFin

/-- The body at a physical serialized rank.  Increasing `index` enumerates
all bodies in bit-lexicographic order. -/
def codeAtSerializedIndex {n s : Nat}
    (index : Fin (2 ^ DAGCodec.codeLength n s)) : DAGCodec.Code n s :=
  fun position =>
    (BitVec.ofNatLT index.val index.isLt).getMsb position

/-- Non-strict physical serialized-bit lexicographic order. -/
def SerializedLexLE {n s : Nat}
    (left right : DAGCodec.Code n s) : Prop :=
  serializedIndex left <= serializedIndex right

instance instDecidableSerializedLexLE {n s : Nat}
    (left right : DAGCodec.Code n s) :
    Decidable (SerializedLexLE left right) := by
  unfold SerializedLexLE
  infer_instance

/-! ## Prefix and block constraints -/

/-- Materialized lexicographic truth table of a standard DAG. -/
def circuitBits {n : Nat} (circuit : FlatCircuit n) : List Bool :=
  tableBits (circuitTruthTable circuit)

@[simp] theorem circuitBits_length {n : Nat} (circuit : FlatCircuit n) :
    (circuitBits circuit).length = 2 ^ n := by
  simp [circuitBits]

/-- Exact number of bits supplied by the next merge request. -/
def expectedLength (n blockLength start : Nat) : Nat :=
  min blockLength (2 ^ n - start)

/-- The window lies in the table and contains exactly the required next
block.  `start = 2 ^ n` is admitted as a completed no-op boundary, whose only
well-formed block is empty. -/
def WindowWellFormed (n blockLength start : Nat) (block : List Bool) : Prop :=
  start <= 2 ^ n /\ block.length = expectedLength n blockLength start

instance instDecidableWindowWellFormed
    (n blockLength start : Nat) (block : List Bool) :
    Decidable (WindowWellFormed n blockLength start block) := by
  unfold WindowWellFormed
  infer_instance

/-- The already-read prefix represented by `prior`, followed by the new
literal block. -/
def targetPrefix {n s : Nat} (prior : DAGCodec.BoundedCircuit n s)
    (start : Nat) (block : List Bool) : List Bool :=
  (circuitBits prior.val).take start ++ block

/-- A bounded candidate satisfies exactly the combined old-prefix/new-block
constraint.  Under `WindowWellFormed`, this is equivalent to the two literal
MMW agreement conditions. -/
def Fits {n s : Nat} (prior candidate : DAGCodec.BoundedCircuit n s)
    (start : Nat) (block : List Bool) : Prop :=
  (circuitBits candidate.val).take (start + block.length) =
    targetPrefix prior start block

instance instDecidableFits {n s : Nat}
    (prior candidate : DAGCodec.BoundedCircuit n s)
    (start : Nat) (block : List Bool) :
    Decidable (Fits prior candidate start block) := by
  unfold Fits
  infer_instance

/-- Semantic existence predicate for the exact merge constraint. -/
def HasCandidate {n s : Nat} (prior : DAGCodec.BoundedCircuit n s)
    (start : Nat) (block : List Bool) : Prop :=
  Exists fun candidate : DAGCodec.BoundedCircuit n s =>
    Fits prior candidate start block

/-! ## Finite size-then-lex search -/

/-- Test the body at `index` at one exact internal-gate count. -/
def eligibleAtGateCount {n s : Nat}
    (prior : DAGCodec.BoundedCircuit n s) (start : Nat) (block : List Bool)
    (gateCount : Fin (s + 1))
    (index : Fin (2 ^ DAGCodec.codeLength n s)) : Bool :=
  match DAGCodec.decode (codeAtSerializedIndex index) with
  | none => false
  | some candidate =>
      decide (candidate.val.gateCount = gateCount.val /\
        Fits prior candidate start block)

/-- Lexicographically first canonical body at one exact gate count. -/
def firstCodeAtGateCount {n s : Nat}
    (prior : DAGCodec.BoundedCircuit n s) (start : Nat) (block : List Bool)
    (gateCount : Fin (s + 1)) :
    Option (Fin (2 ^ DAGCodec.codeLength n s)) :=
  Fin.find? (eligibleAtGateCount prior start block gateCount)

/-- The least gate count for which a fitting canonical body exists. -/
def firstGateCount {n s : Nat}
    (prior : DAGCodec.BoundedCircuit n s) (start : Nat) (block : List Bool) :
    Option (Fin (s + 1)) :=
  Fin.find? fun gateCount =>
    (firstCodeAtGateCount prior start block gateCount).isSome

/-- Fully executable finite minimization. -/
def selectCode {n s : Nat} (prior : DAGCodec.BoundedCircuit n s)
    (start : Nat) (block : List Bool) : Option (DAGCodec.Code n s) := do
  let gateCount <- firstGateCount prior start block
  let index <- firstCodeAtGateCount prior start block gateCount
  pure (codeAtSerializedIndex index)

/-! ## Tagged public boundary -/

/-- Malformed requests are distinguished from a genuine absence result. -/
inductive MalformedReason where
  | invalidPrior
  | startPastEnd
  | wrongBlockLength
  deriving DecidableEq, Repr

/-- Collision-free result tag.  In particular `noCircuit` is not encoded as
an all-zero circuit body. -/
inductive Result (n s : Nat) where
  | found (code : DAGCodec.Code n s)
  | noCircuit
  | malformed (reason : MalformedReason)

/-- Wire-level executable reference Stream-Merge.

Validation order is prior code, start bound, and then exact block length. -/
def referenceStreamMerge {n s : Nat}
    (priorCode : DAGCodec.Code n s)
    (blockLength start : Nat) (block : List Bool) : Result n s :=
  match DAGCodec.decode priorCode with
  | none => .malformed .invalidPrior
  | some prior =>
      if start <= 2 ^ n then
        if block.length = expectedLength n blockLength start then
          match selectCode prior start block with
          | some code => .found code
          | none => .noCircuit
        else
          .malformed .wrongBlockLength
      else
        .malformed .startPastEnd

end StreamMerge
end StreamingMagnification
end Frontier
end Pnp4
