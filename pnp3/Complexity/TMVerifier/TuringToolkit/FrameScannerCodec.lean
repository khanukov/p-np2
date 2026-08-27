import Complexity.TMVerifier.TuringToolkit.Foundation

/-!
# Generic fixed-width (4-bit) frame codecs

This is the alphabet layer of the generic frame-scanner kernel.  It knows
nothing about Turing machines, control states, or the T1 ABI: a `FrameCodec F`
is just an encode/decode pair on an arbitrary frame type `F` whose codewords
all have the fixed physical width `4`, together with the round-trip law.

Everything downstream — `FrameScannerKernel`'s macrostep and list-scan
induction, the `T1Frame` instantiation, and the non-T1 genericity probe —
consumes frames only through this interface.  Any later four-bit alphabet is
a new instance, not a new scanner proof.

The module also fixes the two purely physical vocabularies that the kernel
shares with every instance:

* `FrameScan.writeCell` — a single-cell tape overwrite, with its self-write
  identity;
* `FrameScan.frameListTape` — the list-backed tape used by every exact trace
  theorem, together with `flatMap_bits_length` and the "the four cells at an
  aligned position spell the frame that sits there" lemma
  `physicalBitsAt_flatMap`.

Both are stated for an arbitrary `Fin L → Bool` tape, so they are usable
before any machine is fixed.  No axioms, no placeholders.
-/

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM

namespace FrameScan

universe v

/-- A fixed-width frame alphabet: an injective 4-bit encoding of `F` with a
partial decoder inverting it.

`bits_length` is what makes the width literally `4` — the whole kernel is
stated at that width — and `decode_bits` is the round-trip law.  The two
together give `bits` injectivity (`bits_injective`). -/
structure FrameCodec (F : Type v) where
  /-- Physical encoding of one frame: always exactly four cells. -/
  bits : F → List Bool
  /-- Partial decoder for a four-cell window. -/
  decode? : List Bool → Option F
  /-- Fixed frame width. -/
  bits_length : ∀ f : F, (bits f).length = 4
  /-- Encode/decode round trip. -/
  decode_bits : ∀ f : F, decode? (bits f) = some f

namespace FrameCodec

variable {F : Type v} (C : FrameCodec F)

/-- The round trip makes the encoder injective. -/
theorem bits_injective {f g : F} (h : C.bits f = C.bits g) : f = g := by
  have := C.decode_bits f
  rw [h, C.decode_bits g] at this
  exact (Option.some.inj this).symm

/-- A codeword, spelled out as four explicit cells.  This is the form the
kernel's tape lemmas need: it replaces "case on the concrete frame type",
which is not available generically. -/
theorem bits_eq_four (f : F) :
    ∃ a b c d : Bool, C.bits f = [a, b, c, d] := by
  have hlen := C.bits_length f
  match hb : C.bits f with
  | [] => rw [hb] at hlen; simp at hlen
  | [_] => rw [hb] at hlen; simp at hlen
  | [_, _] => rw [hb] at hlen; simp at hlen
  | [_, _, _] => rw [hb] at hlen; simp at hlen
  | [a, b, c, d] => exact ⟨a, b, c, d, rfl⟩
  | _ :: _ :: _ :: _ :: _ :: _ => rw [hb] at hlen; simp at hlen

/-- Concatenated codewords occupy exactly four cells per frame. -/
theorem flatMap_bits_length (fs : List F) :
    (fs.flatMap C.bits).length = 4 * fs.length := by
  induction fs with
  | nil => simp
  | cons f rest ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons, ih,
        C.bits_length f]
      omega

end FrameCodec

/-! ## Physical tape vocabulary

These are machine-independent: they take a bare `Fin L → Bool`, so the kernel
can state its step adapters before instantiating `L` to a `tapeLength`. -/

/-- Overwrite a single physical cell. -/
def writeCell {L : Nat} (h : Nat) (b : Bool) (tape : Fin L → Bool) :
    Fin L → Bool :=
  fun i => if (i : Nat) = h then b else tape i

/-- Writing back the bit already present is the identity. -/
theorem writeCell_self {L : Nat} (h : Nat) (hh : h < L) (tape : Fin L → Bool) :
    writeCell h (tape ⟨h, hh⟩) tape = tape := by
  funext i
  by_cases hi : (i : Nat) = h
  · have hfin : (⟨h, hh⟩ : Fin L) = i := Fin.ext hi.symm
    simp [writeCell, hi, hfin]
  · simp [writeCell, hi]

/-- The list-backed tape: cell `i` holds `bits[i]`, blank past the end. -/
def frameListTape {L : Nat} (bits : List Bool) : Fin L → Bool :=
  fun i => bits.getD i.val false

/-- The four physical cells starting at an aligned head position. -/
def physicalBitsAt {L h : Nat} (hh : h + 4 < L) (tape : Fin L → Bool) :
    List Bool :=
  [tape ⟨h, by omega⟩, tape ⟨h + 1, by omega⟩,
   tape ⟨h + 2, by omega⟩, tape ⟨h + 3, by omega⟩]

/-- **The frame at an aligned position is the frame the list puts there.**
On a tape backed by `(pre ++ frame :: suffix)`, the four cells starting at
`4 * pre.length` spell exactly `frame`'s codeword.  Generic in the codec, so
no `cases` on a concrete frame type is possible: the proof destructures the
codeword through `bits_eq_four` instead. -/
theorem physicalBitsAt_flatMap {F : Type v} (C : FrameCodec F) {L : Nat}
    (pre suffix : List F) (frame : F)
    (hsafe : 4 * pre.length + 4 < L) :
    physicalBitsAt (h := 4 * pre.length) hsafe
        (frameListTape (L := L) ((pre ++ frame :: suffix).flatMap C.bits)) =
      C.bits frame := by
  obtain ⟨a, b, c, d, hbits⟩ := C.bits_eq_four frame
  have hlen := C.flatMap_bits_length pre
  simp [physicalBitsAt, frameListTape, List.getD, List.flatMap_append, hlen,
    hbits]

end FrameScan

end TM
end PsubsetPpoly
end Internal
end Pnp3
