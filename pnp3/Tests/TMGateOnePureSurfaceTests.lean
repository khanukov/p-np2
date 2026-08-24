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
#check @decodeG1Frame_reserved
#check @G1Tag
#check @G1Tag.units
#check @G1Tag.arity
#check @G1Request
#check @G1Request.Canonical
#check @encodeG1Frames
#check @encodeG1
#check @g1Point
#check @encodeG1_length
#check @g1OutputPosition
#check @encodeG1_getElem?_outputPosition
#check @decodeG1Tape?
#check @decodeG1Tape_encode
#check @decodeG1Tape?_eq_some
#check @decodeG1Tape?_iff
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

end Pnp3.Tests.TMGateOnePureSurface
