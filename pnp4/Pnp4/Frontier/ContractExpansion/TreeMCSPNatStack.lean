import Pnp4.Frontier.ContractExpansion.TreeMCSPGateRecordLayout

/-!
# `encodeNatStack` — D2t-5a: the on-tape value-stack format

D2t-5's on-tape driver maintains a **value stack** of completed-subtree root WORK-indices (the abstract
`List Nat` threaded by `runStack`, D2t-5b).  On tape that stack is stored as a contiguous run of
**self-delimiting unary fields** `1^v 0` — the *same* `unaryField` encoding the WORK gate records use for
operands, so a popped index copies straight into a record's operand field with no re-encoding.

This module fixes that format and proves the stack operations against the abstract `List Nat`:

* `encodeNatStack S` — the bottom-to-top stack `S` as `unaryField`s concatenated left-to-right; `push`
  (cons) is prepending one field.
* `decodeUnaryField_encodeNatStack_cons` — **pop**: reading one unary field off the encoded stack returns
  the top index and the encoded tail (so the on-tape `selfLoopScanRightOne`/field-read realises a pop).
* `decodeNatStack_encodeNatStack` — full round-trip: `S.length` pops recover `S` and leave the suffix.

These are the value-stack analogue of the WORK record-stream codec (`encodeGateRecordStream` /
`decodeGateRecordStream`), and the bridge D2t-5b uses to relate the tape STACK region to the abstract
stack `runStack` threads.

**Progress classification (AGENTS.md): Infrastructure** — a tape-format codec proven against the abstract
stack; builds no machine and proves no separation.  Standard `[propext, Classical.choice, Quot.sound]`
triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- The value stack `S` (bottom-to-top) encoded as concatenated self-delimiting unary fields `1^v 0`.
`push v` is prepending `unaryField v` (the top sits at the front). -/
def encodeNatStack : List Nat → List Bool
  | [] => []
  | v :: rest => unaryField v ++ encodeNatStack rest

@[simp] theorem encodeNatStack_nil : encodeNatStack [] = [] := rfl

@[simp] theorem encodeNatStack_cons (v : Nat) (rest : List Nat) :
    encodeNatStack (v :: rest) = unaryField v ++ encodeNatStack rest := rfl

/-- **Pop.**  Reading one unary field off the encoded stack returns the top index `v` and the encoded
tail — the on-tape field-read realises an abstract `List Nat` head/tail. -/
@[simp] theorem decodeUnaryField_encodeNatStack_cons (v : Nat) (rest : List Nat) :
    decodeUnaryField (encodeNatStack (v :: rest)) = some (v, encodeNatStack rest) := by
  simp [encodeNatStack]

/-- Exact length of the encoded stack: the sum of `(vᵢ + 1)` (each field is `1^vᵢ 0`). -/
@[simp] theorem encodeNatStack_length (S : List Nat) :
    (encodeNatStack S).length = (S.map (· + 1)).sum := by
  induction S with
  | nil => simp
  | cons v rest ih => simp [encodeNatStack, ih]

/-- Decode `count` consecutive indices off the front of a bit stream (the value stack reader). -/
def decodeNatStack : Nat → List Bool → Option (List Nat × List Bool)
  | 0, bs => some ([], bs)
  | (k + 1), bs =>
    match decodeUnaryField bs with
    | none => none
    | some (v, rest) =>
      match decodeNatStack k rest with
      | none => none
      | some (vs, rest') => some (v :: vs, rest')

@[simp] theorem decodeNatStack_zero (bs : List Bool) : decodeNatStack 0 bs = some ([], bs) := rfl

/-- **Stack round-trip**: popping `S.length` indices off `encodeNatStack S ++ rest` recovers `S` exactly
and leaves the suffix untouched (induction on `S`, via the one-field pop). -/
theorem decodeNatStack_encodeNatStack (S : List Nat) (rest : List Bool) :
    decodeNatStack S.length (encodeNatStack S ++ rest) = some (S, rest) := by
  induction S generalizing rest with
  | nil => simp
  | cons v rest ih =>
      simp only [encodeNatStack, List.length_cons, List.append_assoc, decodeNatStack,
        decodeUnaryField_unaryField, ih]

end ContractExpansion
end Frontier
end Pnp4
