import Complexity.PsubsetPpolyInternal.Bitstring

/-!
# T1 true uniform-seek ABI

The initial word has a unary index field independent of an unannotated data
field.  Four physical bits encode each frame and `0000` is reserved for the
blank tape.  `spent` and `cursor` are decoded frame codes, but are never
produced by the request encoder or accepted by the initial-input grammar.
-/

namespace Pnp3.Internal.PsubsetPpoly.TM

inductive T1Frame
  | blank | bof | index | spent | separator
  | data (value : Bool) | cursor
  | output (value : Bool) | finish
  deriving DecidableEq, Repr

def T1Frame.bits : T1Frame → List Bool
  | .blank        => [false, false, false, false]
  | .bof          => [false, false, false, true ]
  | .index        => [false, false, true,  false]
  | .spent        => [false, false, true,  true ]
  | .separator    => [false, true,  false, false]
  | .data false   => [false, true,  false, true ]
  | .data true    => [false, true,  true,  false]
  | .cursor       => [false, true,  true,  true ]
  | .output false => [true,  false, false, false]
  | .output true  => [true,  false, false, true ]
  | .finish       => [true,  false, true,  false]

@[simp] theorem T1Frame.bits_length (f : T1Frame) : f.bits.length = 4 := by
  cases f with
  | data b | output b => cases b <;> rfl
  | blank | bof | index | spent | separator | cursor | finish => rfl

def decodeT1Frame? : List Bool → Option T1Frame
  | [false, false, false, false] => some .blank
  | [false, false, false, true ] => some .bof
  | [false, false, true,  false] => some .index
  | [false, false, true,  true ] => some .spent
  | [false, true,  false, false] => some .separator
  | [false, true,  false, true ] => some (.data false)
  | [false, true,  true,  false] => some (.data true)
  | [false, true,  true,  true ] => some .cursor
  | [true,  false, false, false] => some (.output false)
  | [true,  false, false, true ] => some (.output true)
  | [true,  false, true,  false] => some .finish
  | _ => none

@[simp] theorem decodeT1Frame_bits (f : T1Frame) :
    decodeT1Frame? f.bits = some f := by
  cases f with
  | data b | output b => cases b <;> rfl
  | blank | bof | index | spent | separator | cursor | finish => rfl

private theorem decodeT1Frame?_eq_some {bits : List Bool} {f : T1Frame}
    (h : decodeT1Frame? bits = some f) : bits = f.bits := by
  rcases bits with _ | ⟨a, bits⟩
  · simp [decodeT1Frame?] at h
  rcases bits with _ | ⟨b, bits⟩
  · simp [decodeT1Frame?] at h
  rcases bits with _ | ⟨c, bits⟩
  · simp [decodeT1Frame?] at h
  rcases bits with _ | ⟨d, bits⟩
  · simp [decodeT1Frame?] at h
  rcases bits with _ | ⟨e, rest⟩
  · cases a <;> cases b <;> cases c <;> cases d <;>
      simp [decodeT1Frame?] at h <;> subst f <;> rfl
  · simp [decodeT1Frame?] at h

def decodeT1Frames? : List Bool → Option (List T1Frame)
  | [] => some []
  | a :: b :: c :: d :: rest => do
      let f ← decodeT1Frame? [a, b, c, d]
      pure (f :: (← decodeT1Frames? rest))
  | _ => none

private theorem decodeT1Frames?_eq_some {bits : List Bool} {fs : List T1Frame}
    (h : decodeT1Frames? bits = some fs) :
    bits = fs.flatMap T1Frame.bits := by
  match bits with
  | [] =>
      simp [decodeT1Frames?] at h
      subst fs
      rfl
  | [a] => simp [decodeT1Frames?] at h
  | [a, b] => simp [decodeT1Frames?] at h
  | [a, b, c] => simp [decodeT1Frames?] at h
  | a :: b :: c :: d :: rest =>
      simp only [decodeT1Frames?] at h
      cases hframe : decodeT1Frame? [a, b, c, d] with
      | none => simp [hframe] at h
      | some frame =>
          cases hrest : decodeT1Frames? rest with
          | none => simp [hframe, hrest] at h
          | some tail =>
              simp [hframe, hrest] at h
              subst fs
              rw [decodeT1Frames?_eq_some hrest]
              simp only [List.flatMap_cons]
              rw [← decodeT1Frame?_eq_some hframe]
              rfl
  termination_by bits.length

structure T1Request where
  index : Nat
  data : List Bool
  deriving DecidableEq, Repr

def encodeT1Frames (r : T1Request) : List T1Frame :=
  [.bof] ++ List.replicate r.index .index ++ [.separator] ++
    r.data.map .data ++ [.output false, .finish]

def encodeT1 (r : T1Request) : List Bool :=
  (encodeT1Frames r).flatMap T1Frame.bits

theorem T1Frame.flatMap_bits_length (fs : List T1Frame) :
    (fs.flatMap T1Frame.bits).length = 4 * fs.length := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [ih, Nat.mul_succ]; omega

@[simp] theorem encodeT1_length (r : T1Request) :
    (encodeT1 r).length = 4 * (r.index + r.data.length + 4) := by
  rw [encodeT1, T1Frame.flatMap_bits_length]
  simp [encodeT1Frames]
  omega

def t1Point (bits : List Bool) : Boolcube.Point bits.length := fun i => bits.get i

def parseT1Index : List T1Frame → Option (Nat × List T1Frame)
  | .index :: rest => do
      let (k, tail) ← parseT1Index rest
      pure (k + 1, tail)
  | .separator :: rest => some (0, rest)
  | _ => none

private theorem parseT1Index_eq_some {fs : List T1Frame} {k : Nat}
    {tail : List T1Frame} (h : parseT1Index fs = some (k, tail)) :
    fs = List.replicate k .index ++ .separator :: tail := by
  induction fs generalizing k tail with
  | nil => simp [parseT1Index] at h
  | cons frame rest ih =>
      cases frame with
      | index =>
          simp only [parseT1Index] at h
          cases hp : parseT1Index rest with
          | none => simp [hp] at h
          | some result =>
              rcases result with ⟨k', tail'⟩
              simp [hp] at h
              rcases h with ⟨rfl, rfl⟩
              rw [ih hp]
              simp [List.replicate_succ]
      | separator =>
          simp [parseT1Index] at h
          rcases h with ⟨rfl, rfl⟩
          rfl
      | data b | output b => cases b <;> simp [parseT1Index] at h
      | blank | bof | spent | cursor | finish => simp [parseT1Index] at h

def parseT1Data : List T1Frame → Option (List Bool × List T1Frame)
  | .data b :: rest => do
      let (xs, tail) ← parseT1Data rest
      pure (b :: xs, tail)
  | .output false :: rest => some ([], rest)
  | _ => none

private theorem parseT1Data_eq_some {fs : List T1Frame} {data : List Bool}
    {tail : List T1Frame} (h : parseT1Data fs = some (data, tail)) :
    fs = data.map .data ++ .output false :: tail := by
  induction fs generalizing data tail with
  | nil => simp [parseT1Data] at h
  | cons frame rest ih =>
      cases frame with
      | data bit =>
          simp only [parseT1Data] at h
          cases hp : parseT1Data rest with
          | none => simp [hp] at h
          | some result =>
              rcases result with ⟨data', tail'⟩
              simp [hp] at h
              rcases h with ⟨rfl, rfl⟩
              rw [ih hp]
              rfl
      | output bit =>
          cases bit with
          | false =>
              simp [parseT1Data] at h
              rcases h with ⟨rfl, rfl⟩
              rfl
          | true => simp [parseT1Data] at h
      | blank | bof | index | spent | separator | cursor | finish =>
          simp [parseT1Data] at h

def decodeT1FrameList? : List T1Frame → Option T1Request
  | .bof :: rest => do
      let (k, rest) ← parseT1Index rest
      let (data, rest) ← parseT1Data rest
      if rest = [.finish] then some ⟨k, data⟩ else none
  | _ => none

private theorem decodeT1FrameList?_eq_some {fs : List T1Frame} {r : T1Request}
    (h : decodeT1FrameList? fs = some r) : fs = encodeT1Frames r := by
  rcases fs with _ | ⟨frame, rest⟩
  · simp [decodeT1FrameList?] at h
  cases frame with
  | bof =>
      simp only [decodeT1FrameList?] at h
      cases hi : parseT1Index rest with
      | none => simp [hi] at h
      | some indexResult =>
          rcases indexResult with ⟨k, afterIndex⟩
          cases hd : parseT1Data afterIndex with
          | none => simp [hi, hd] at h
          | some dataResult =>
              rcases dataResult with ⟨data, afterData⟩
              simp [hi, hd] at h
              rcases h with ⟨rfl, rfl⟩
              rw [parseT1Index_eq_some hi, parseT1Data_eq_some hd]
              simp [encodeT1Frames, List.append_assoc]
  | data b | output b => cases b <;> simp [decodeT1FrameList?] at h
  | blank | index | spent | separator | cursor | finish =>
      simp [decodeT1FrameList?] at h

def decodeT1Tape? (bits : List Bool) : Option T1Request := do
  decodeT1FrameList? (← decodeT1Frames? bits)

/-- Padded physical frame `j`; bits beyond the represented list are blank. -/
def paddedT1FrameAt (bits : List Bool) (j : Nat) : List Bool :=
  [bits.getD (4*j) false, bits.getD (4*j+1) false,
   bits.getD (4*j+2) false, bits.getD (4*j+3) false]

/-- Every represented physical frame is observable (not the blank code).
This predicate is reserved for future malformed/trailing-input theorems; the
current T1a canonical execution results neither consume nor discharge it. -/
def T1Physical (bits : List Bool) : Prop :=
  ∀ j, 4 * j < bits.length → paddedT1FrameAt bits j ≠ T1Frame.blank.bits

@[simp] theorem decodeT1Frames_encoded (fs : List T1Frame) :
    decodeT1Frames? (fs.flatMap T1Frame.bits) = some fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      cases f with
      | data b | output b => cases b <;>
          simp [decodeT1Frames?, decodeT1Frame?, T1Frame.bits, ih]
      | blank | bof | index | spent | separator | cursor | finish =>
          simp [decodeT1Frames?, decodeT1Frame?, T1Frame.bits, ih]

@[simp] theorem parseT1Index_encoded (k : Nat) (tail : List T1Frame) :
    parseT1Index (List.replicate k .index ++ .separator :: tail) = some (k, tail) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, parseT1Index, ih]

@[simp] theorem parseT1Data_encoded (xs : List Bool) (tail : List T1Frame) :
    parseT1Data (xs.map .data ++ .output false :: tail) = some (xs, tail) := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [parseT1Data, ih]

@[simp] theorem decodeT1Tape_encode (r : T1Request) :
    decodeT1Tape? (encodeT1 r) = some r := by
  rcases r with ⟨k, data⟩
  unfold decodeT1Tape? encodeT1
  rw [decodeT1Frames_encoded]
  simp [encodeT1Frames, decodeT1FrameList?]

/-- Successful T1 tape decoding determines the canonical physical encoding. -/
theorem decodeT1Tape?_eq_some {bits : List Bool} {r : T1Request}
    (h : decodeT1Tape? bits = some r) : bits = encodeT1 r := by
  unfold decodeT1Tape? at h
  cases hframes : decodeT1Frames? bits with
  | none => simp [hframes] at h
  | some fs =>
      simp [hframes] at h
      rw [decodeT1Frames?_eq_some hframes,
        decodeT1FrameList?_eq_some h]
      rfl

def t1OutputPosition (r : T1Request) : Nat :=
  4 * (r.index + r.data.length + 2) + 3

end Pnp3.Internal.PsubsetPpoly.TM
