import Pnp4.Frontier.ContractExpansion.TreeMCSPDriveStack

/-!
# `encodeCtrlStack` — D2t-5a: the on-tape control-stack format

The second tape stack of D2t-5's driver (D2t-5b, `drive`/`TreeMCSPDriveStack`): the **control stack** of
pending internal nodes, each a frame `(tag, remaining)` — the gate tag and how many children are still to
be processed.  On tape it is stored, like the value stack (`NatStack`) and the WORK records, as a run of
**self-delimiting unary fields**: a frame is `unaryField tag.tagCode ++ unaryField remaining` (tag code,
then the remaining-children count), and the stack is the frames concatenated **top-first**.

This module fixes that format and proves the stack operations against the abstract `List (ITag × Nat)`:

* `encodeCtrlStack S` — the control stack `S` (top at the head) as concatenated frames; `push` (cons)
  prepends one frame.
* `decodeCtrlFrame_encodeCtrlStack_cons` — **pop**: reading one frame off the top recovers `(tag, rem)`
  and the encoded tail (two `unaryField` reads + a 3-way tag decode).
* `decodeCtrlStack_encodeCtrlStack` — full **round-trip**: `S.length` frame-pops recover `S` and leave the
  suffix untouched.

Together with `TreeMCSPNatStack` (the value-stack format), this completes the **D2t-5a tape formats**; the
on-tape `pushFrame`/`popFrame` machines realise these codecs, and the D2t-5b loop relates the two tape
stacks to `drive`'s abstract `(control, value)` stacks.

**Progress classification (AGENTS.md): Infrastructure** — a tape-format codec proven against the abstract
stack; builds no machine and proves no separation.  Standard `[propext, Classical.choice, Quot.sound]`
triple only.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- A small code per internal tag, stored on tape as a unary field. -/
def ITag.tagCode : ITag → Nat
  | .tnot => 0
  | .tand => 1
  | .tor => 2

/-- Recover a tag from its code (the inverse of `tagCode` on `{0,1,2}`). -/
def ITag.ofCode : Nat → Option ITag
  | 0 => some .tnot
  | 1 => some .tand
  | 2 => some .tor
  | _ => none

@[simp] theorem ITag.ofCode_tagCode (t : ITag) : ITag.ofCode t.tagCode = some t := by
  cases t <;> rfl

/-- A control frame `(tag, remaining)` as two self-delimiting unary fields: the tag code, then the
remaining-children count. -/
def encodeCtrlFrame : ITag × Nat → List Bool
  | (tag, rem) => unaryField tag.tagCode ++ unaryField rem

/-- The control stack `S` (top at the head) as concatenated frames; `push f` (cons) prepends `f`. -/
def encodeCtrlStack : List (ITag × Nat) → List Bool
  | [] => []
  | f :: rest => encodeCtrlFrame f ++ encodeCtrlStack rest

@[simp] theorem encodeCtrlStack_nil : encodeCtrlStack [] = [] := rfl

/-- Decode one control frame off the front: the tag-code field, the 3-way tag decode, then the
remaining-count field. -/
def decodeCtrlFrame (bs : List Bool) : Option ((ITag × Nat) × List Bool) :=
  match decodeUnaryField bs with
  | none => none
  | some (code, rest) =>
    match ITag.ofCode code with
    | none => none
    | some tag =>
      match decodeUnaryField rest with
      | none => none
      | some (rem, rest') => some ((tag, rem), rest')

/-- **Pop.**  Reading one frame off the top of the encoded stack recovers the top `(tag, rem)` and the
encoded tail. -/
@[simp] theorem decodeCtrlFrame_encodeCtrlStack_cons (tag : ITag) (rem : Nat)
    (rest : List (ITag × Nat)) :
    decodeCtrlFrame (encodeCtrlStack ((tag, rem) :: rest)) = some ((tag, rem), encodeCtrlStack rest) := by
  simp [encodeCtrlStack, encodeCtrlFrame, decodeCtrlFrame, List.append_assoc]

/-- Decode `count` consecutive control frames off the front of a bit stream (the control-stack reader). -/
def decodeCtrlStack : Nat → List Bool → Option (List (ITag × Nat) × List Bool)
  | 0, bs => some ([], bs)
  | (k + 1), bs =>
    match decodeCtrlFrame bs with
    | none => none
    | some (f, rest) =>
      match decodeCtrlStack k rest with
      | none => none
      | some (fs, rest') => some (f :: fs, rest')

@[simp] theorem decodeCtrlStack_zero (bs : List Bool) : decodeCtrlStack 0 bs = some ([], bs) := rfl

/-- **Stack round-trip**: popping `S.length` frames off `encodeCtrlStack S ++ suffix` recovers `S` exactly
and leaves the suffix untouched (induction on `S`, via the one-frame pop). -/
theorem decodeCtrlStack_encodeCtrlStack (S : List (ITag × Nat)) (suffix : List Bool) :
    decodeCtrlStack S.length (encodeCtrlStack S ++ suffix) = some (S, suffix) := by
  induction S generalizing suffix with
  | nil => simp
  | cons f tail ih =>
      obtain ⟨tag, rem⟩ := f
      simp only [encodeCtrlStack, encodeCtrlFrame, List.length_cons, List.append_assoc, decodeCtrlStack,
        decodeCtrlFrame, decodeUnaryField_unaryField, ITag.ofCode_tagCode, ih]

end ContractExpansion
end Frontier
end Pnp4
