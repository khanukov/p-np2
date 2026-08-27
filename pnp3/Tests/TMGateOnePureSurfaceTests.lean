import Complexity.TMVerifier.TuringToolkit.GateOneSemantics

/-!
# G1 one-gate interpreter, pure layer: surface tests

Import-side type probes for the pure T2a surface: the fresh unary ABI, its
pure parser and canonicity characterisation, and the pure gate semantics.

Nothing here is about a machine.  The fixed finite control, its frame
language, and the exact validation/rewind execution capstone are separate
layers with their own surface files.

This is an audit surface: it pins public signatures, it does not prove
anything new.
-/

namespace Pnp3.Tests.TMGateOnePureSurface

open Pnp3.Internal.PsubsetPpoly.TM

-- ABI and pure parser.
#check @G1Frame
#check @G1Frame.bits
#check @decodeG1Frame?
#check @decodeG1Frame_bits
#check @decodeG1Frame_reserved
#check @g1FrameCodec
#check @g1FrameCodec_bits
#check @g1FrameCodec_decode
#check @G1Frame.bits_argSep
#check @G1Tag
#check @G1Tag.units
#check @G1Tag.arity
#check @G1Request
#check @G1Request.Canonical
#check @G1Request.WellFormed
#check @encodeG1Frames
#check @encodeG1
#check @encodeG1Frames_injective
#check @encodeG1_injective
#check @g1Point
#check @encodeG1_length
#check @g1OutputPosition
#check @encodeG1_getElem?_outputPosition
#check @decodeG1Tape?
#check @decodeG1Tape_encode
#check @decodeG1Tape?_eq_some
#check @decodeG1Tape?_iff
#check @decodeG1Tape?_encode_not_canonical
#check @g1_example_tape_roundtrip
#check @decodeG1Tape?_eq_frameList
#check @decodeG1FrameList?_reject_tagRun
#check @decodeG1FrameList?_canonical
#check @G1Request.canonical_iff
#check @encodeG1_getD_outputPosition

-- Pure semantics.
#check @G1Request.spec
#check @G1Request.spec_input
#check @G1Request.spec_const_false
#check @G1Request.spec_const_true
#check @G1Request.spec_const_out_of_convention
#check @G1Request.spec_not
#check @G1Request.spec_and_of
#check @G1Request.spec_or_of
#check @G1Request.spec_and_oob
#check @G1Request.spec_or_oob
#check @G1Request.spec_unused_field
#check @G1Request.spec_eq_none_of_not_canonical
#check @G1Request.spec_isSome_iff
#check @G1Request.g1_example_canonical_oob_not_wellFormed

/-! ## Exact theorem-contract pins -/

theorem check_G1Frame_bits_length (f : G1Frame) : f.bits.length = 4 :=
  G1Frame.bits_length f

theorem check_decodeG1Frame_bits (f : G1Frame) :
    decodeG1Frame? f.bits = some f :=
  decodeG1Frame_bits f

theorem check_encodeG1_length (r : G1Request) :
    (encodeG1 r).length =
      4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6) :=
  encodeG1_length r

theorem check_encodeG1_getElem?_outputPosition (r : G1Request) :
    (encodeG1 r)[g1OutputPosition r]? = some false :=
  encodeG1_getElem?_outputPosition r

theorem check_decodeG1Tape?_iff (bits : List Bool) (r : G1Request) :
    decodeG1Tape? bits = some r ↔ (bits = encodeG1 r ∧ r.Canonical) :=
  decodeG1Tape?_iff bits r

theorem check_decodeG1Tape?_encode_not_canonical {r : G1Request}
    (h : ¬ r.Canonical) : decodeG1Tape? (encodeG1 r) = none :=
  decodeG1Tape?_encode_not_canonical h

theorem check_spec_input (i : Nat) (vals : List Bool) :
    (G1Request.mk .input i 0 vals).spec = vals[i]? :=
  G1Request.spec_input i vals

theorem check_spec_const_false (vals : List Bool) :
    (G1Request.mk .const 0 0 vals).spec = some false :=
  G1Request.spec_const_false vals

theorem check_spec_const_true (vals : List Bool) :
    (G1Request.mk .const 1 0 vals).spec = some true :=
  G1Request.spec_const_true vals

theorem check_spec_not (i : Nat) (vals : List Bool) :
    (G1Request.mk .not i 0 vals).spec = vals[i]?.map (!·) :=
  G1Request.spec_not i vals

theorem check_spec_and_of {i j : Nat} {vals : List Bool} {a b : Bool}
    (h1 : vals[i]? = some a) (h2 : vals[j]? = some b) :
    (G1Request.mk .and i j vals).spec = some (a && b) :=
  G1Request.spec_and_of h1 h2

theorem check_spec_or_of {i j : Nat} {vals : List Bool} {a b : Bool}
    (h1 : vals[i]? = some a) (h2 : vals[j]? = some b) :
    (G1Request.mk .or i j vals).spec = some (a || b) :=
  G1Request.spec_or_of h1 h2

theorem check_spec_and_oob {i j : Nat} {vals : List Bool}
    (h : vals[i]? = none ∨ vals[j]? = none) :
    (G1Request.mk .and i j vals).spec = none :=
  G1Request.spec_and_oob h

theorem check_spec_or_oob {i j : Nat} {vals : List Bool}
    (h : vals[i]? = none ∨ vals[j]? = none) :
    (G1Request.mk .or i j vals).spec = none :=
  G1Request.spec_or_oob h

theorem check_spec_isSome_iff (r : G1Request) :
    r.spec.isSome = true ↔ r.WellFormed :=
  G1Request.spec_isSome_iff r

end Pnp3.Tests.TMGateOnePureSurface
