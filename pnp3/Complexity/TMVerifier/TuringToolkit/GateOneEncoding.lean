import Complexity.TMVerifier.TuringToolkit.FrameScannerCodec
import Complexity.PsubsetPpolyInternal.Bitstring

/-!
# G1: a fresh unary one-gate ABI

**Progress classification: Infrastructure.**  A tape alphabet, a request
record and a pure parser.  No machine execution, no gate semantics, no
acceptance, no lower bound.

A fresh ABI is required: `SLGate.encode` is width-parameterised
(`encodeFin widthN/widthS`), i.e. compiled advice, which a zero-parameter
fixed-control machine cannot consume.  `G1` is related to `SLGate` only
through a future pure `spec`-level bridge (deferred).

Every frame is exactly four cells and `0000` stays reserved for the blank
tape.  The complete code table is

```text
blank 0000   separator 0100   output false 1000   spent    1100
bof   0001   data false 0101  output true  1001   reserved 1101
tag   0010   data true  0110  finish       1010   reserved 1110
index 0011   cursor     0111  argSep       1011   reserved 1111
```

`argSep = 1011` separates the two unary operand-index fields.  `spent` and
`cursor` are the two *machine-internal* markers the planned destructive read
needs (`index ↦ spent`, `data ↦ cursor`); they are decodable but never
produced by the encoder.  The three remaining codes are rejected.

The canonical word is

```text
bof · tag^g · argSep · index^arg1 · argSep · index^arg2
    · separator · data(v₀)…data(v_{m-1}) · output(false) · finish
```

with `g = r.tag.units ∈ {1,…,5}` the unary tag (`input 1`, `const 2`,
`not 3`, `and 4`, `or 5`) — no per-kind code, no width field.  `G1Tag.arity`
fixes the operand convention: an arity-1 tag uses `arg1` only and must leave
`arg2 = 0`; `const` additionally requires `arg1 ≤ 1`, the unary encoding of
the constant bit.  `G1Request.Canonical` is exactly that convention, and the
pure decoder enforces it: `decodeG1Tape?_iff` says a bit list decodes to `r`
iff it is literally `encodeG1 r` with `r` canonical, so wrong tag counts,
wrong unused fields, missing delimiters, reserved codes and malformed
canonical words are all rejected.

**Caveat.**  `decodeG1Tape?_iff` is a statement about the *pure* parser only.
A fixed zero-parameter control deciding the same frame grammar is deferred to a
later layer; no machine-level parser correspondence, execution, acceptance, or
rejection theorem exists in this slice.  As in T1, nothing here claims behavior
for physically padded or otherwise malformed machine tapes.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

/-! ## Frames -/

/-- The G1 four-bit frame alphabet.  `spent` and `cursor` are the only
machine-internal markers; both are needed by the planned destructive read and
neither is produced by the encoder. -/
inductive G1Frame
  | blank | bof | tag | index | separator
  | data (value : Bool) | cursor
  | output (value : Bool) | finish
  | argSep | spent
  deriving DecidableEq, Repr

def G1Frame.bits : G1Frame → List Bool
  | .blank        => [false, false, false, false]
  | .bof          => [false, false, false, true ]
  | .tag          => [false, false, true,  false]
  | .index        => [false, false, true,  true ]
  | .separator    => [false, true,  false, false]
  | .data false   => [false, true,  false, true ]
  | .data true    => [false, true,  true,  false]
  | .cursor       => [false, true,  true,  true ]
  | .output false => [true,  false, false, false]
  | .output true  => [true,  false, false, true ]
  | .finish       => [true,  false, true,  false]
  | .argSep       => [true,  false, true,  true ]
  | .spent        => [true,  true,  false, false]

@[simp] theorem G1Frame.bits_length (f : G1Frame) : f.bits.length = 4 := by
  cases f with
  | data b | output b => cases b <;> rfl
  | blank | bof | tag | index | separator | cursor | finish | argSep | spent =>
      rfl

/-- The pure frame decoder.  The three codes `1101`, `1110`, `1111` are
reserved and rejected, as is every non-four-cell window. -/
def decodeG1Frame? : List Bool → Option G1Frame
  | [false, false, false, false] => some .blank
  | [false, false, false, true ] => some .bof
  | [false, false, true,  false] => some .tag
  | [false, false, true,  true ] => some .index
  | [false, true,  false, false] => some .separator
  | [false, true,  false, true ] => some (.data false)
  | [false, true,  true,  false] => some (.data true)
  | [false, true,  true,  true ] => some .cursor
  | [true,  false, false, false] => some (.output false)
  | [true,  false, false, true ] => some (.output true)
  | [true,  false, true,  false] => some .finish
  | [true,  false, true,  true ] => some .argSep
  | [true,  true,  false, false] => some .spent
  | _ => none

@[simp] theorem decodeG1Frame_bits (f : G1Frame) :
    decodeG1Frame? f.bits = some f := by
  cases f with
  | data b | output b => cases b <;> rfl
  | blank | bof | tag | index | separator | cursor | finish | argSep | spent =>
      rfl

/-- The pure G1 alphabet as an instance of the generic four-bit codec. -/
def g1FrameCodec : FrameScan.FrameCodec G1Frame where
  bits := G1Frame.bits
  decode? := decodeG1Frame?
  bits_length := G1Frame.bits_length
  decode_bits := decodeG1Frame_bits

@[simp] theorem g1FrameCodec_bits : g1FrameCodec.bits = G1Frame.bits := rfl
@[simp] theorem g1FrameCodec_decode : g1FrameCodec.decode? = decodeG1Frame? := rfl

/-- Literal ABI pin for the argument separator code. -/
theorem G1Frame.bits_argSep :
    G1Frame.argSep.bits = [true, false, true, true] := rfl

/-- The three reserved codes are rejected. -/
theorem decodeG1Frame_reserved :
    decodeG1Frame? [true, true, false, true] = none ∧
      decodeG1Frame? [true, true, true, false] = none ∧
        decodeG1Frame? [true, true, true, true] = none :=
  ⟨rfl, rfl, rfl⟩

private theorem decodeG1Frame?_eq_some {bits : List Bool} {f : G1Frame}
    (h : decodeG1Frame? bits = some f) : bits = f.bits := by
  rcases bits with _ | ⟨a, bits⟩
  · simp [decodeG1Frame?] at h
  rcases bits with _ | ⟨b, bits⟩
  · simp [decodeG1Frame?] at h
  rcases bits with _ | ⟨c, bits⟩
  · simp [decodeG1Frame?] at h
  rcases bits with _ | ⟨d, bits⟩
  · simp [decodeG1Frame?] at h
  rcases bits with _ | ⟨e, rest⟩
  · cases a <;> cases b <;> cases c <;> cases d <;>
      simp [decodeG1Frame?] at h <;> subst f <;> rfl
  · simp [decodeG1Frame?] at h

/-- Split a physical bit list into four-cell frames. -/
def decodeG1Frames? : List Bool → Option (List G1Frame)
  | [] => some []
  | a :: b :: c :: d :: rest => do
      let f ← decodeG1Frame? [a, b, c, d]
      pure (f :: (← decodeG1Frames? rest))
  | _ => none

private theorem decodeG1Frames?_eq_some {bits : List Bool} {fs : List G1Frame}
    (h : decodeG1Frames? bits = some fs) : bits = fs.flatMap G1Frame.bits := by
  match bits with
  | [] => simp [decodeG1Frames?] at h; subst fs; rfl
  | [_] => simp [decodeG1Frames?] at h
  | [_, _] => simp [decodeG1Frames?] at h
  | [_, _, _] => simp [decodeG1Frames?] at h
  | a :: b :: c :: d :: rest =>
      simp only [decodeG1Frames?] at h
      cases hframe : decodeG1Frame? [a, b, c, d] with
      | none => simp [hframe] at h
      | some frame =>
          cases hrest : decodeG1Frames? rest with
          | none => simp [hframe, hrest] at h
          | some tail =>
              simp [hframe, hrest] at h
              subst fs
              rw [decodeG1Frames?_eq_some hrest]
              simp only [List.flatMap_cons]
              rw [← decodeG1Frame?_eq_some hframe]
              rfl
  termination_by bits.length

@[simp] theorem decodeG1Frames_encoded (fs : List G1Frame) :
    decodeG1Frames? (fs.flatMap G1Frame.bits) = some fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      cases f with
      | data b | output b => cases b <;>
          simp [decodeG1Frames?, decodeG1Frame?, G1Frame.bits, ih]
      | blank | bof | tag | index | separator | cursor | finish | argSep
      | spent => simp [decodeG1Frames?, decodeG1Frame?, G1Frame.bits, ih]

theorem G1Frame.flatMap_bits_length (fs : List G1Frame) :
    (fs.flatMap G1Frame.bits).length = 4 * fs.length := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [ih, Nat.mul_succ]; omega

/-! ## Gate tags and requests -/

/-- The five gate kinds of the one-gate interpreter. -/
inductive G1Tag
  | input | const | not | and | or
  deriving DecidableEq, Repr

/-- **The unary tag representation.**  The tag field of the canonical word is
`tag^units`; there is no per-kind code and no width. -/
def G1Tag.units : G1Tag → Nat
  | .input => 1
  | .const => 2
  | .not   => 3
  | .and   => 4
  | .or    => 5

/-- How many operand-index fields the tag actually uses. -/
def G1Tag.arity : G1Tag → Nat
  | .input => 1
  | .const => 1
  | .not   => 1
  | .and   => 2
  | .or    => 2

/-- Inverse of `G1Tag.units`: a unary tag run of any other length is not a
tag, so the pure decoder rejects it. -/
def g1TagOfUnits? : Nat → Option G1Tag
  | 1 => some .input
  | 2 => some .const
  | 3 => some .not
  | 4 => some .and
  | 5 => some .or
  | _ => none

@[simp] theorem g1TagOfUnits?_units (t : G1Tag) :
    g1TagOfUnits? t.units = some t := by cases t <;> rfl

theorem g1TagOfUnits?_eq_some {k : Nat} {t : G1Tag}
    (h : g1TagOfUnits? k = some t) : k = t.units := by
  match k with
  | 0 | 6 => simp [g1TagOfUnits?] at h
  | 1 | 2 | 3 | 4 | 5 =>
      simp [g1TagOfUnits?] at h; subst h; rfl
  | (k + 7) => simp [g1TagOfUnits?] at h

/-- A one-gate request: the gate kind, two unary operand-index fields, and the
runtime value list the operands index into. -/
structure G1Request where
  tag : G1Tag
  arg1 : Nat
  arg2 : Nat
  vals : List Bool
  deriving DecidableEq, Repr

/-- **The canonical unused-field convention**, as a Boolean test.  An arity-1
tag must leave `arg2 = 0`; `const` must additionally keep `arg1 ≤ 1`, since
`arg1` *is* the constant bit in unary. -/
def G1Request.canonicalB (r : G1Request) : Bool :=
  (if r.tag.arity = 1 then r.arg2 = 0 else true) &&
    (if r.tag = .const then r.arg1 ≤ 1 else true)

/-- The canonical unused-field convention. -/
def G1Request.Canonical (r : G1Request) : Prop := r.canonicalB = true

instance (r : G1Request) : Decidable r.Canonical :=
  inferInstanceAs (Decidable (r.canonicalB = true))

theorem G1Request.canonical_iff (r : G1Request) :
    r.Canonical ↔ ((r.tag.arity = 1 → r.arg2 = 0) ∧ (r.tag = .const → r.arg1 ≤ 1)) := by
  cases r with
  | mk tag arg1 arg2 vals =>
      cases tag <;> simp [Canonical, canonicalB, G1Tag.arity]

/-! ## The encoder -/

def encodeG1Frames (r : G1Request) : List G1Frame :=
  [.bof] ++ List.replicate r.tag.units .tag ++ [.argSep] ++
    List.replicate r.arg1 .index ++ [.argSep] ++
    List.replicate r.arg2 .index ++ [.separator] ++
    r.vals.map .data ++ [.output false, .finish]

def encodeG1 (r : G1Request) : List Bool :=
  (encodeG1Frames r).flatMap G1Frame.bits

/-- The canonical word without its `output`/`finish` tail. -/
def g1PrefixFrames (r : G1Request) : List G1Frame :=
  [.bof] ++ List.replicate r.tag.units .tag ++ [.argSep] ++
    List.replicate r.arg1 .index ++ [.argSep] ++
    List.replicate r.arg2 .index ++ [.separator] ++ r.vals.map .data

theorem encodeG1Frames_eq_prefix (r : G1Request) :
    encodeG1Frames r = g1PrefixFrames r ++ .output false :: [.finish] := by
  simp [encodeG1Frames, g1PrefixFrames, List.append_assoc]

@[simp] theorem g1PrefixFrames_length (r : G1Request) :
    (g1PrefixFrames r).length =
      r.tag.units + r.arg1 + r.arg2 + r.vals.length + 4 := by
  simp [g1PrefixFrames]; omega

/-- The initial point of the machine: the canonical word, cell by cell. -/
def g1Point (bits : List Bool) : Boolcube.Point bits.length := fun i => bits.get i

@[simp] theorem encodeG1Frames_length (r : G1Request) :
    (encodeG1Frames r).length =
      r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6 := by
  simp [encodeG1Frames]; omega

/-- **Exact physical length.**  Four cells per frame, six delimiter frames. -/
@[simp] theorem encodeG1_length (r : G1Request) :
    (encodeG1 r).length =
      4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 6) := by
  rw [encodeG1, G1Frame.flatMap_bits_length, encodeG1Frames_length]

/-- Physical cell holding the destination bit: the last cell of the single
`output` frame. -/
def g1OutputPosition (r : G1Request) : Nat :=
  4 * (r.tag.units + r.arg1 + r.arg2 + r.vals.length + 4) + 3

theorem g1OutputPosition_lt_length (r : G1Request) :
    g1OutputPosition r < (encodeG1 r).length := by
  simp [g1OutputPosition, encodeG1_length]; omega

/-- The four cells of the frame at an aligned physical position. -/
theorem G1Frame.flatMap_getElem? (pre suffix : List G1Frame) (frame : G1Frame)
    (j : Nat) (hj : j < 4) :
    ((pre ++ frame :: suffix).flatMap G1Frame.bits)[4 * pre.length + j]? =
      frame.bits[j]? := by
  have hlen : (pre.flatMap G1Frame.bits).length = 4 * pre.length :=
    G1Frame.flatMap_bits_length pre
  have hj' : j < frame.bits.length := by rw [G1Frame.bits_length]; exact hj
  have hidx : 4 * pre.length + j - (pre.flatMap G1Frame.bits).length = j := by
    omega
  rw [List.flatMap_append, List.flatMap_cons,
    List.getElem?_append_right (by omega), hidx,
    List.getElem?_append_left hj']

/-- **The output cell starts at `false`.**  The destination bit of the
canonical word is the last cell of the single `output false` frame. -/
theorem encodeG1_getElem?_outputPosition (r : G1Request) :
    (encodeG1 r)[g1OutputPosition r]? = some false := by
  have h := G1Frame.flatMap_getElem? (g1PrefixFrames r) [.finish]
    (.output false) 3 (by omega)
  rw [g1PrefixFrames_length] at h
  rw [encodeG1, encodeG1Frames_eq_prefix, g1OutputPosition, h]
  rfl

theorem encodeG1_getD_outputPosition (r : G1Request) :
    (encodeG1 r).getD (g1OutputPosition r) false = false := by
  simp [List.getD, encodeG1_getElem?_outputPosition]

/-! ## The pure parser -/

/-- Parse one unary run of `unit` frames terminated by a `stop` frame. -/
def parseG1Run (unit stop : G1Frame) : List G1Frame → Option (Nat × List G1Frame)
  | [] => none
  | f :: rest =>
      if f = unit then do
        let (k, tail) ← parseG1Run unit stop rest
        pure (k + 1, tail)
      else if f = stop then some (0, rest)
      else none

@[simp] theorem parseG1Run_encoded {unit stop : G1Frame} (hne : unit ≠ stop)
    (k : Nat) (tail : List G1Frame) :
    parseG1Run unit stop (List.replicate k unit ++ stop :: tail) =
      some (k, tail) := by
  induction k with
  | zero => simp [parseG1Run, Ne.symm hne]
  | succ k ih => simp [List.replicate_succ, parseG1Run, ih]

theorem parseG1Run_eq_some {unit stop : G1Frame} {fs : List G1Frame} {k : Nat}
    {tail : List G1Frame} (h : parseG1Run unit stop fs = some (k, tail)) :
    fs = List.replicate k unit ++ stop :: tail := by
  induction fs generalizing k tail with
  | nil => simp [parseG1Run] at h
  | cons f rest ih =>
      by_cases hu : f = unit
      · subst hu
        simp only [parseG1Run] at h
        cases hp : parseG1Run f stop rest with
        | none => simp [hp] at h
        | some result =>
            rcases result with ⟨k', tail'⟩
            simp [hp] at h
            rcases h with ⟨rfl, rfl⟩
            rw [ih hp]
            simp [List.replicate_succ]
      · by_cases hs : f = stop
        · subst hs
          simp [parseG1Run, hu] at h
          rcases h with ⟨rfl, rfl⟩
          rfl
        · simp [parseG1Run, hu, hs] at h

/-- Parse the data region, terminated by the `output false` destination. -/
def parseG1Data : List G1Frame → Option (List Bool × List G1Frame)
  | .data b :: rest => do
      let (xs, tail) ← parseG1Data rest
      pure (b :: xs, tail)
  | .output false :: rest => some ([], rest)
  | _ => none

@[simp] theorem parseG1Data_encoded (xs : List Bool) (tail : List G1Frame) :
    parseG1Data (xs.map .data ++ .output false :: tail) = some (xs, tail) := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [parseG1Data, ih]

theorem parseG1Data_eq_some {fs : List G1Frame} {vals : List Bool}
    {tail : List G1Frame} (h : parseG1Data fs = some (vals, tail)) :
    fs = vals.map .data ++ .output false :: tail := by
  induction fs generalizing vals tail with
  | nil => simp [parseG1Data] at h
  | cons frame rest ih =>
      cases frame with
      | data bit =>
          simp only [parseG1Data] at h
          cases hp : parseG1Data rest with
          | none => simp [hp] at h
          | some result =>
              rcases result with ⟨vals', tail'⟩
              simp [hp] at h
              rcases h with ⟨rfl, rfl⟩
              rw [ih hp]
              rfl
      | output bit =>
          cases bit with
          | false => simp [parseG1Data] at h; rcases h with ⟨rfl, rfl⟩; rfl
          | true => simp [parseG1Data] at h
      | blank | bof | tag | index | separator | cursor | finish | argSep
      | spent => simp [parseG1Data] at h

/-- The frame-level parser.  It enforces the whole canonical grammar: the
anchor, a tag run of a legal length, both `argSep`-terminated unary index
fields, the separator, the data region, the `output false` destination, the
`finish` terminator with nothing after it, and the unused-field convention. -/
def decodeG1FrameList? : List G1Frame → Option G1Request
  | .bof :: rest => do
      let (g, rest) ← parseG1Run .tag .argSep rest
      let tag ← g1TagOfUnits? g
      let (a1, rest) ← parseG1Run .index .argSep rest
      let (a2, rest) ← parseG1Run .index .separator rest
      let (vals, rest) ← parseG1Data rest
      if rest = [.finish] then
        let r : G1Request := ⟨tag, a1, a2, vals⟩
        if r.Canonical then some r else none
      else none
  | _ => none

/-- Structural decoder used to prove encoder injectivity; unlike the public
parser it does not enforce the unused-field convention. -/
def decodeG1FrameListRaw? : List G1Frame → Option G1Request
  | .bof :: rest => do
      let (g, rest) ← parseG1Run .tag .argSep rest
      let tag ← g1TagOfUnits? g
      let (a1, rest) ← parseG1Run .index .argSep rest
      let (a2, rest) ← parseG1Run .index .separator rest
      let (vals, rest) ← parseG1Data rest
      if rest = [.finish] then some ⟨tag, a1, a2, vals⟩ else none
  | _ => none

@[simp] theorem decodeG1FrameListRaw?_encoded (r : G1Request) :
    decodeG1FrameListRaw? (encodeG1Frames r) = some r := by
  cases r with
  | mk tag arg1 arg2 vals =>
      have hshape : encodeG1Frames ⟨tag, arg1, arg2, vals⟩ =
          .bof :: (List.replicate tag.units .tag ++ .argSep ::
            (List.replicate arg1 .index ++ .argSep ::
              (List.replicate arg2 .index ++ .separator ::
                (vals.map .data ++ [.output false, .finish])))) := by
        simp [encodeG1Frames, List.append_assoc]
      rw [hshape]
      simp [decodeG1FrameListRaw?,
        parseG1Run_encoded (by decide : G1Frame.tag ≠ G1Frame.argSep),
        parseG1Run_encoded (by decide : G1Frame.index ≠ G1Frame.argSep),
        parseG1Run_encoded (by decide : G1Frame.index ≠ G1Frame.separator)]

/-- The frame encoding preserves the complete request, including non-canonical
unused fields. -/
theorem encodeG1Frames_injective : Function.Injective encodeG1Frames := by
  intro r s h
  have hd := congrArg decodeG1FrameListRaw? h
  simpa using hd

/-- The physical bit encoding is injective on all requests. -/
theorem encodeG1_injective : Function.Injective encodeG1 := by
  intro r s h
  have hd := congrArg decodeG1Frames? h
  have hframes : encodeG1Frames r = encodeG1Frames s := by
    simpa [encodeG1] using hd
  exact encodeG1Frames_injective hframes

/-- The physical parser: split into frames, then parse the grammar. -/
def decodeG1Tape? (bits : List Bool) : Option G1Request := do
  decodeG1FrameList? (← decodeG1Frames? bits)

@[simp] theorem decodeG1FrameList?_encoded (r : G1Request) (h : r.Canonical) :
    decodeG1FrameList? (encodeG1Frames r) = some r := by
  cases r with
  | mk tag arg1 arg2 vals =>
      have hshape : encodeG1Frames ⟨tag, arg1, arg2, vals⟩ =
          .bof :: (List.replicate tag.units .tag ++ .argSep ::
            (List.replicate arg1 .index ++ .argSep ::
              (List.replicate arg2 .index ++ .separator ::
                (vals.map .data ++ [.output false, .finish])))) := by
        simp [encodeG1Frames, List.append_assoc]
      rw [hshape]
      simp [decodeG1FrameList?,
        parseG1Run_encoded (by decide : G1Frame.tag ≠ G1Frame.argSep),
        parseG1Run_encoded (by decide : G1Frame.index ≠ G1Frame.argSep),
        parseG1Run_encoded (by decide : G1Frame.index ≠ G1Frame.separator), h]

theorem decodeG1FrameList?_eq_some {fs : List G1Frame} {r : G1Request}
    (h : decodeG1FrameList? fs = some r) :
    fs = encodeG1Frames r ∧ r.Canonical := by
  rcases fs with _ | ⟨frame, rest⟩
  · simp [decodeG1FrameList?] at h
  cases frame with
  | bof =>
      simp only [decodeG1FrameList?] at h
      cases hg : parseG1Run .tag .argSep rest with
      | none => simp [hg] at h
      | some tagResult =>
        rcases tagResult with ⟨g, afterTag⟩
        cases ht : g1TagOfUnits? g with
        | none => simp [hg, ht] at h
        | some tag =>
          cases h1 : parseG1Run .index .argSep afterTag with
          | none => simp [hg, ht, h1] at h
          | some r1 =>
            rcases r1 with ⟨a1, after1⟩
            cases h2 : parseG1Run .index .separator after1 with
            | none => simp [hg, ht, h1, h2] at h
            | some r2 =>
              rcases r2 with ⟨a2, after2⟩
              cases hd : parseG1Data after2 with
              | none => simp [hg, ht, h1, h2, hd] at h
              | some rd =>
                rcases rd with ⟨vals, afterData⟩
                by_cases hfin : afterData = [.finish]
                · by_cases hcan : (⟨tag, a1, a2, vals⟩ : G1Request).Canonical
                  · simp [hg, ht, h1, h2, hd, hfin, hcan] at h
                    subst h
                    refine ⟨?_, hcan⟩
                    rw [parseG1Run_eq_some hg, parseG1Run_eq_some h1,
                      parseG1Run_eq_some h2, parseG1Data_eq_some hd, hfin,
                      g1TagOfUnits?_eq_some ht]
                    simp [encodeG1Frames, List.append_assoc]
                  · simp [hg, ht, h1, h2, hd, hfin, hcan] at h
                · simp [hg, ht, h1, h2, hd, hfin] at h
  | data b | output b => cases b <;> simp [decodeG1FrameList?] at h
  | blank | tag | index | separator | cursor | finish | argSep | spent =>
      simp [decodeG1FrameList?] at h

/-- **Round trip.**  Every canonical request is recovered from its tape. -/
theorem decodeG1Tape_encode (r : G1Request) (h : r.Canonical) :
    decodeG1Tape? (encodeG1 r) = some r := by
  unfold decodeG1Tape? encodeG1
  rw [decodeG1Frames_encoded]
  simpa using decodeG1FrameList?_encoded r h

/-- **Canonicity.**  A successful decode determines the physical tape
exactly, and the decoded request obeys the unused-field convention. -/
theorem decodeG1Tape?_eq_some {bits : List Bool} {r : G1Request}
    (h : decodeG1Tape? bits = some r) : bits = encodeG1 r ∧ r.Canonical := by
  unfold decodeG1Tape? at h
  cases hframes : decodeG1Frames? bits with
  | none => simp [hframes] at h
  | some fs =>
      simp [hframes] at h
      obtain ⟨hfs, hcan⟩ := decodeG1FrameList?_eq_some h
      exact ⟨by rw [decodeG1Frames?_eq_some hframes, hfs]; rfl, hcan⟩

/-- **Parser equivalence.**  Decoding a physical bit list succeeds with `r`
exactly when the list is the canonical encoding of a canonical `r`.  Every
rejection claim of this module is a corollary of this one theorem. -/
theorem decodeG1Tape?_iff (bits : List Bool) (r : G1Request) :
    decodeG1Tape? bits = some r ↔ (bits = encodeG1 r ∧ r.Canonical) := by
  constructor
  · exact decodeG1Tape?_eq_some
  · rintro ⟨rfl, hcan⟩; exact decodeG1Tape_encode r hcan

/-- Encoding a request that violates the unused-field convention is rejected
by the public parser. -/
theorem decodeG1Tape?_encode_not_canonical {r : G1Request}
    (h : ¬ r.Canonical) : decodeG1Tape? (encodeG1 r) = none := by
  cases hd : decodeG1Tape? (encodeG1 r) with
  | none => rfl
  | some s =>
      obtain ⟨heq, hcan⟩ := decodeG1Tape?_eq_some hd
      have hrs : r = s := encodeG1_injective heq
      subst s
      exact absurd hcan h

/-- Concrete bit-level round trip for the ABI. -/
theorem g1_example_tape_roundtrip :
    decodeG1Tape? (encodeG1 ⟨.input, 1, 0, [false, true]⟩) =
      some ⟨.input, 1, 0, [false, true]⟩ :=
  decodeG1Tape_encode _ rfl

/-- The physical and frame-level parsers agree on canonical words. -/
theorem decodeG1Tape?_eq_frameList (r : G1Request) :
    decodeG1Tape? (encodeG1 r) = decodeG1FrameList? (encodeG1Frames r) := by
  unfold decodeG1Tape? encodeG1
  rw [decodeG1Frames_encoded]
  rfl

/-! ## Rejection

The two general rejection theorems below are the ones that are *not* immediate
from `decodeG1Tape?_iff` by inspection of a single concrete word. -/

/-- **Wrong tag count is rejected**, for every illegal run length and every
continuation: a unary tag field of length `0` or `≥ 6` is not a tag. -/
theorem decodeG1FrameList?_reject_tagRun (k : Nat) (hk : g1TagOfUnits? k = none)
    (rest : List G1Frame) :
    decodeG1FrameList?
        ([.bof] ++ List.replicate k .tag ++ [.argSep] ++ rest) = none := by
  have hshape : ([G1Frame.bof] ++ List.replicate k .tag ++ [.argSep] ++ rest) =
      .bof :: (List.replicate k .tag ++ .argSep :: rest) := by
    simp [List.append_assoc]
  rw [hshape]
  simp [decodeG1FrameList?,
    parseG1Run_encoded (by decide : G1Frame.tag ≠ G1Frame.argSep), hk]

/-- **Non-canonical unused fields are rejected.**  Nothing that violates the
arity convention is ever produced by the pure decoder. -/
theorem decodeG1FrameList?_canonical {fs : List G1Frame} {r : G1Request}
    (h : decodeG1FrameList? fs = some r) : r.Canonical :=
  (decodeG1FrameList?_eq_some h).2

end Pnp3.Internal.PsubsetPpoly.TM
