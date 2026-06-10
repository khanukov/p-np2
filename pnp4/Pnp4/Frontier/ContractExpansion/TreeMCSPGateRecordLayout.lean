import Complexity.TMVerifier.TuringToolkit.Encoding

/-!
# On-tape gate-record layout + unary back-reference distances (NP-verifier track — decoder brick D0)

This is the **data-format spec** the on-tape gate interpreter (`TM_VERIFIER_STRATEGY.md` §6k) will read.
The fixed verifier `M` cannot embed the toolkit's `circuitEvaluatorCS` (it is recursion on the gate
`List`, a per-instance unrolling), so `M` interprets a **contiguous stream of fixed-shape gate records**
laid out on the tape, looping over them with a back-edge (`repeatBody`).

The single design choice this brick fixes is the **record encoding**, with one principle: every
variable-length field is a **self-delimiting unary block** `1^k 0`, so the interpreter recovers it by a
single marker-free scan over `1`s (`selfLoopScanRightOne`) stopping at the `0` terminator — the §6k
"unary-distance addressing" that resolves the reachable-scratch crux for operand fetch on the 2-symbol
single tape.

Scope (D0): the unary field codec, the one-gate-record encoder/decoder, and their round-trip + size
lemmas.  *Not* here: the full witness→record-stream decoder (D2), the interpreter (I), the row loop (R),
or any assembly.  Back-reference Nats in `notGate`/`andGate`/`orGate` are encoded verbatim; the
**distance** convention (record at gate position `p` stores `p − j` for a reference to gate `j`) is
applied by the stream decoder (D2) when it knows positions — here the codec is a faithful bijection on
`SLGate` values, independent of that convention.
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-! ### Unary field `1^k 0` (the back-reference distance representation) -/

/-- A natural `k` as a self-delimiting **unary** field: `k` ones followed by a `0` terminator. -/
def unaryField (k : Nat) : List Bool := List.replicate k true ++ [false]

@[simp] theorem unaryField_length (k : Nat) : (unaryField k).length = k + 1 := by
  simp [unaryField]

/-- Decode one unary field: read the maximal leading block of `1`s, consume the `0` terminator, and
return the count together with the remaining bits.  Mirrors `selfLoopScanRightOne` on the tape (scan
over `1`s, stop on the first `0`). -/
def decodeUnaryField : List Bool → Option (Nat × List Bool)
  | [] => none
  | true :: rest =>
      match decodeUnaryField rest with
      | none => none
      | some (k, rest') => some (k + 1, rest')
  | false :: rest => some (0, rest)

/-- Round-trip for the unary field: decoding `unaryField k` (followed by any suffix) returns `k` and the
untouched suffix. -/
@[simp] theorem decodeUnaryField_unaryField (k : Nat) (rest : List Bool) :
    decodeUnaryField (unaryField k ++ rest) = some (k, rest) := by
  induction k with
  | zero => simp [unaryField, decodeUnaryField]
  | succ k ih =>
      have h : unaryField (k + 1) = true :: unaryField k := by
        simp [unaryField, List.replicate_succ]
      rw [h, List.cons_append]
      simp [decodeUnaryField, ih]

/-! ### One gate record

Layout: a unary **tag** (`0` input, `1` const, `2` not, `3` and, `4` or) followed by the operand
fields — a unary input-index / back-reference distance per operand, except `const`, whose single
operand is one literal value bit. -/

/-- Encode one `SLGate` as a tape record. -/
def encodeGateRecord {n : Nat} (g : SLGate n) : List Bool :=
  match g with
  | .input i     => unaryField 0 ++ unaryField i.val
  | .const b     => unaryField 1 ++ [b]
  | .notGate k   => unaryField 2 ++ unaryField k
  | .andGate k l => unaryField 3 ++ unaryField k ++ unaryField l
  | .orGate k l  => unaryField 4 ++ unaryField k ++ unaryField l

/-- Decode one gate record off the front of a bit stream, returning the gate and the remaining bits.
Fails (`none`) on a truncated stream, an unknown tag, or an input index `≥ n` (a malformed record —
the route the verifier sends to its reject sink). -/
def decodeGateRecord (n : Nat) (bs : List Bool) : Option (SLGate n × List Bool) :=
  match decodeUnaryField bs with
  | none => none
  | some (tag, r0) =>
    match tag with
    | 0 =>
      match decodeUnaryField r0 with
      | none => none
      | some (i, r1) => if h : i < n then some (SLGate.input ⟨i, h⟩, r1) else none
    | 1 =>
      match r0 with
      | [] => none
      | b :: r1 => some (SLGate.const b, r1)
    | 2 =>
      match decodeUnaryField r0 with
      | none => none
      | some (k, r1) => some (SLGate.notGate k, r1)
    | 3 =>
      match decodeUnaryField r0 with
      | none => none
      | some (k, r1) =>
        match decodeUnaryField r1 with
        | none => none
        | some (l, r2) => some (SLGate.andGate k l, r2)
    | 4 =>
      match decodeUnaryField r0 with
      | none => none
      | some (k, r1) =>
        match decodeUnaryField r1 with
        | none => none
        | some (l, r2) => some (SLGate.orGate k l, r2)
    | _ => none

/-- **Round-trip**: a record produced by `encodeGateRecord` decodes back to the same gate, leaving any
suffix untouched.  The core correctness of the layout — the interpreter recovers exactly the encoded
gate. -/
theorem decodeGateRecord_encodeGateRecord {n : Nat} (g : SLGate n) (rest : List Bool) :
    decodeGateRecord n (encodeGateRecord g ++ rest) = some (g, rest) := by
  cases g with
  | input i =>
      simp only [encodeGateRecord, List.append_assoc, decodeGateRecord,
        decodeUnaryField_unaryField, dif_pos i.isLt, Fin.eta]
  | const b =>
      simp [encodeGateRecord, decodeGateRecord, decodeUnaryField_unaryField]
  | notGate k =>
      simp only [encodeGateRecord, List.append_assoc, decodeGateRecord,
        decodeUnaryField_unaryField]
  | andGate k l =>
      simp only [encodeGateRecord, List.append_assoc, decodeGateRecord,
        decodeUnaryField_unaryField]
  | orGate k l =>
      simp only [encodeGateRecord, List.append_assoc, decodeGateRecord,
        decodeUnaryField_unaryField]

/-! ### Record size (for the polynomial layout budget) -/

/-- Exact length of an encoded gate record (a tag terminator + the operand fields). -/
def gateRecordSize {n : Nat} (g : SLGate n) : Nat :=
  match g with
  | .input i     => i.val + 2
  | .const _     => 3
  | .notGate k   => k + 4
  | .andGate k l => k + l + 6
  | .orGate k l  => k + l + 7

@[simp] theorem encodeGateRecord_length {n : Nat} (g : SLGate n) :
    (encodeGateRecord g).length = gateRecordSize g := by
  cases g <;>
    simp only [encodeGateRecord, gateRecordSize, unaryField, List.length_append,
      List.length_replicate, List.length_cons, List.length_nil] <;> omega

end ContractExpansion
end Frontier
end Pnp4
