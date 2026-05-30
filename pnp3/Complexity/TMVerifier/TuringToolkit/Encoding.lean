import Complexity.TMVerifier.TuringToolkit.BinaryCounter

namespace Pnp3
namespace Internal
namespace PsubsetPpoly
namespace TM

namespace Encoding

/-- Encode `i : Fin (2^w)` as a `w`-bit little-endian bit list
(LSB first). -/
def encodeFin : (w : Nat) → Fin (2 ^ w) → List Bool
  | 0, _ => []
  | w + 1, i =>
    let b := decide (i.val % 2 = 1)
    have hrest : i.val / 2 < 2 ^ w := by
      have hi_lt := i.isLt
      have heq : (2 : Nat) ^ (w + 1) = 2 ^ w * 2 := by rw [pow_succ]
      apply (Nat.div_lt_iff_lt_mul (by omega : (0 : Nat) < 2)).mpr
      omega
    b :: encodeFin w ⟨i.val / 2, hrest⟩

/-- The encoded bit list always has length `w`. -/
theorem encodeFin_length : ∀ (w : Nat) (i : Fin (2 ^ w)),
    (encodeFin w i).length = w
  | 0, _ => by simp [encodeFin]
  | w + 1, i => by
    simp only [encodeFin, List.length_cons]
    rw [encodeFin_length w]

/-- Decode a bit list as a `Fin (2^w)` value (little-endian: head of
list = LSB).  Returns `none` if the list length mismatches `w`. -/
def decodeFin : (w : Nat) → List Bool → Option (Fin (2 ^ w))
  | 0, [] => some ⟨0, by simp⟩
  | 0, _ :: _ => none
  | _ + 1, [] => none
  | w + 1, b :: bs =>
    match decodeFin w bs with
    | none => none
    | some r =>
      let v := (if b then 1 else 0) + 2 * r.val
      have hv : v < 2 ^ (w + 1) := by
        have hr := r.isLt
        have heq : (2 : Nat) ^ (w + 1) = 2 ^ w * 2 := by rw [pow_succ]
        have hbit_le : (if b then 1 else 0 : Nat) ≤ 1 := by
          split_ifs <;> omega
        omega
      some ⟨v, hv⟩

/-- Round-trip: decoding the encoding recovers the original value. -/
theorem decodeFin_encodeFin : ∀ (w : Nat) (i : Fin (2 ^ w)),
    decodeFin w (encodeFin w i) = some i
  | 0, ⟨0, _⟩ => by
    simp [encodeFin, decodeFin]
  | 0, ⟨_ + 1, h⟩ => by
    simp at h
  | w + 1, i => by
    simp only [encodeFin, decodeFin]
    -- The recursive call at width `w` on the tail reconstructs
    -- `⟨i.val / 2, _⟩` by IH.
    rw [decodeFin_encodeFin w ⟨i.val / 2, _⟩]
    apply Option.some_inj.mpr
    apply Fin.ext
    have hdiv_mod : 2 * (i.val / 2) + i.val % 2 = i.val :=
      Nat.div_add_mod i.val 2
    have hmod_lt : i.val % 2 < 2 := Nat.mod_lt i.val (by omega)
    by_cases hmod : i.val % 2 = 1
    · simp [hmod]; omega
    · have hmod0 : i.val % 2 = 0 := by omega
      simp [hmod]; omega

/-!
### Session 8c: Circuit encoding via `CircuitTree`

The MCSP verifier needs to parse a circuit description off the
witness tape.  We define a local `CircuitTree n` inductive —
structurally identical to `Pnp3.Models.Circuit` — and a recursive
encoder into `List Bool` using the following prefix-free tag
scheme:

* `input i`  → `[false, false, false]` ++ `encodeFin width i`
* `const b`  → `[false, false, true, b]`
* `not c`    → `[false, true, false]` ++ `encode c`
* `and c1 c2`→ `[false, true, true]` ++ `encode c1` ++ `encode c2`
* `or c1 c2` → `[true, false, false]` ++ `encode c1` ++ `encode c2`

Keeping `CircuitTree` local to `Encoding` decouples the toolkit
from MCSP-specific imports; a bridge to `Models.Circuit` can be
supplied in a dedicated session when the MCSP assembly is wired up.

Session 8c delivers the inductive + the encoder + the `size`
measure.  Session 8d delivers the decoder and the round-trip
theorem.
-/

/-- Local mirror of `Pnp3.Models.Circuit`: a tree of AC0-style
Boolean gates over `n` input variables.  Kept separate so the
toolkit stays MCSP-import-free. -/
inductive CircuitTree (n : Nat) where
  | input : Fin n → CircuitTree n
  | const : Bool → CircuitTree n
  | not : CircuitTree n → CircuitTree n
  | and : CircuitTree n → CircuitTree n → CircuitTree n
  | or : CircuitTree n → CircuitTree n → CircuitTree n

namespace CircuitTree

/-- Number of gates in the tree — each node contributes 1. -/
def size {n : Nat} : CircuitTree n → Nat
  | input _ => 1
  | const _ => 1
  | not c => c.size + 1
  | and c1 c2 => c1.size + c2.size + 1
  | or c1 c2 => c1.size + c2.size + 1

end CircuitTree

/-- Prefix-order encoding of a `CircuitTree n` as a bit list,
assuming every `Fin n` index fits in `width` bits. -/
def encodeCircuitTree {n : Nat} (width : Nat)
    (h_width : n ≤ 2 ^ width) : CircuitTree n → List Bool
  | .input i =>
      [false, false, false] ++
        encodeFin width ⟨i.val, lt_of_lt_of_le i.isLt h_width⟩
  | .const b => [false, false, true, b]
  | .not c =>
      [false, true, false] ++ encodeCircuitTree width h_width c
  | .and c1 c2 =>
      [false, true, true] ++
        encodeCircuitTree width h_width c1 ++
        encodeCircuitTree width h_width c2
  | .or c1 c2 =>
      [true, false, false] ++
        encodeCircuitTree width h_width c1 ++
        encodeCircuitTree width h_width c2

/-- Each gate contributes at least 3 tag bits, so the encoded list
has length at least the tree size × 3.  Lower bound — useful later
for showing that the encoded witness fits within the available
certificate room. -/
theorem encodeCircuitTree_length_ge {n : Nat} (width : Nat)
    (h_width : n ≤ 2 ^ width) : ∀ (c : CircuitTree n),
    3 * c.size ≤ (encodeCircuitTree width h_width c).length
  | .input _ => by
    simp [encodeCircuitTree, CircuitTree.size, encodeFin_length]
  | .const _ => by
    simp [encodeCircuitTree, CircuitTree.size]
  | .not c => by
    have ih := encodeCircuitTree_length_ge width h_width c
    simp [encodeCircuitTree, CircuitTree.size]
    omega
  | .and c1 c2 => by
    have ih1 := encodeCircuitTree_length_ge width h_width c1
    have ih2 := encodeCircuitTree_length_ge width h_width c2
    simp [encodeCircuitTree, CircuitTree.size]
    omega
  | .or c1 c2 => by
    have ih1 := encodeCircuitTree_length_ge width h_width c1
    have ih2 := encodeCircuitTree_length_ge width h_width c2
    simp [encodeCircuitTree, CircuitTree.size]
    omega

/-!
### Session 8d: Circuit decoder + round-trip

Structural recursion on a `depth` budget (rather than list length)
gives a clean well-founded definition: each recursive subcall
decrements `depth` by 1.  Passing `c.size` as the initial budget
is always enough since the tree depth is bounded by its size.

The round-trip theorem shows `decodeCircuitTreeAtDepth` (at depth
`c.size`) recovers `c` and leaves any tail unchanged:

  decodeCircuitTreeAtDepth (h_pos : 0 < n) width c.size
      (encodeCircuitTree width h_width c ++ rest)
    = some (c, rest).
-/

/-- Recursive decoder with a structural depth budget.  Returns the
parsed tree plus the remaining bit list, or `none` on malformed
input. -/
def decodeCircuitTreeAtDepth {n : Nat} (h_pos : 0 < n) (width : Nat) :
    Nat → List Bool → Option (CircuitTree n × List Bool)
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, [_] => none
  | _ + 1, [_, _] => none
  | _ + 1, false :: false :: false :: rest =>
    if _ : rest.length < width then none
    else
      let payload := rest.take width
      let remainder := rest.drop width
      match decodeFin width payload with
      | none => none
      | some i_fin =>
        if hv : i_fin.val < n then
          some (CircuitTree.input ⟨i_fin.val, hv⟩, remainder)
        else none
  | _ + 1, false :: false :: true :: b :: rest =>
    some (CircuitTree.const b, rest)
  | d + 1, false :: true :: false :: rest =>
    match decodeCircuitTreeAtDepth h_pos width d rest with
    | none => none
    | some (c, remainder) => some (CircuitTree.not c, remainder)
  | d + 1, false :: true :: true :: rest =>
    match decodeCircuitTreeAtDepth h_pos width d rest with
    | none => none
    | some (c1, rest1) =>
      match decodeCircuitTreeAtDepth h_pos width d rest1 with
      | none => none
      | some (c2, rest2) => some (CircuitTree.and c1 c2, rest2)
  | d + 1, true :: false :: false :: rest =>
    match decodeCircuitTreeAtDepth h_pos width d rest with
    | none => none
    | some (c1, rest1) =>
      match decodeCircuitTreeAtDepth h_pos width d rest1 with
      | none => none
      | some (c2, rest2) => some (CircuitTree.or c1 c2, rest2)
  | _ + 1, _ :: _ :: _ :: _ => none

/-!
### Session 8e: Round-trip — per-constructor lemmas

The cleanest scalable proof splits into per-constructor lemmas
and a combining induction step.  Both the scalar `decodeFin`
round-trip and the `List.take`/`drop` facts line up cleanly at
the constructor level.

Session 8e delivers the `const` and `not` round-trip cases.  The
remaining three constructors (`input`, `and`, `or`) reuse the
same machinery; the `input` case additionally threads
`decodeFin_encodeFin` through the `take`/`drop` split.  Those
are reserved for Session 8f so the current commit keeps its
scope tight and its individual proofs readable.
-/

theorem decode_encode_const {n : Nat} (h_pos : 0 < n) (width : Nat)
    (h_width : n ≤ 2 ^ width) (b : Bool) (d : Nat) (hd : 1 ≤ d)
    (rest : List Bool) :
    decodeCircuitTreeAtDepth h_pos width d
        (encodeCircuitTree width h_width (CircuitTree.const b) ++ rest) =
      some (CircuitTree.const b, rest) := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  simp [encodeCircuitTree, decodeCircuitTreeAtDepth]

theorem decode_encode_not {n : Nat} (h_pos : 0 < n) (width : Nat)
    (h_width : n ≤ 2 ^ width) (c : CircuitTree n) (d : Nat)
    (hd : c.size + 1 ≤ d)
    (rest : List Bool)
    (ih : ∀ (d' : Nat), c.size ≤ d' → ∀ (r : List Bool),
      decodeCircuitTreeAtDepth h_pos width d'
          (encodeCircuitTree width h_width c ++ r) = some (c, r)) :
    decodeCircuitTreeAtDepth h_pos width d
        (encodeCircuitTree width h_width (CircuitTree.not c) ++ rest) =
      some (CircuitTree.not c, rest) := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hd' : c.size ≤ d' := by omega
  simp only [encodeCircuitTree, List.cons_append, List.nil_append,
             decodeCircuitTreeAtDepth]
  rw [ih d' hd' rest]

theorem decode_encode_and {n : Nat} (h_pos : 0 < n) (width : Nat)
    (h_width : n ≤ 2 ^ width) (c1 c2 : CircuitTree n) (d : Nat)
    (hd : c1.size + c2.size + 1 ≤ d)
    (rest : List Bool)
    (ih1 : ∀ (d' : Nat), c1.size ≤ d' → ∀ (r : List Bool),
      decodeCircuitTreeAtDepth h_pos width d'
          (encodeCircuitTree width h_width c1 ++ r) = some (c1, r))
    (ih2 : ∀ (d' : Nat), c2.size ≤ d' → ∀ (r : List Bool),
      decodeCircuitTreeAtDepth h_pos width d'
          (encodeCircuitTree width h_width c2 ++ r) = some (c2, r)) :
    decodeCircuitTreeAtDepth h_pos width d
        (encodeCircuitTree width h_width (CircuitTree.and c1 c2) ++ rest) =
      some (CircuitTree.and c1 c2, rest) := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hd1 : c1.size ≤ d' := by omega
  have hd2 : c2.size ≤ d' := by omega
  simp only [encodeCircuitTree, List.cons_append, List.nil_append,
             List.append_assoc, decodeCircuitTreeAtDepth,
             ih1 d' hd1 (encodeCircuitTree width h_width c2 ++ rest),
             ih2 d' hd2 rest]

theorem decode_encode_or {n : Nat} (h_pos : 0 < n) (width : Nat)
    (h_width : n ≤ 2 ^ width) (c1 c2 : CircuitTree n) (d : Nat)
    (hd : c1.size + c2.size + 1 ≤ d)
    (rest : List Bool)
    (ih1 : ∀ (d' : Nat), c1.size ≤ d' → ∀ (r : List Bool),
      decodeCircuitTreeAtDepth h_pos width d'
          (encodeCircuitTree width h_width c1 ++ r) = some (c1, r))
    (ih2 : ∀ (d' : Nat), c2.size ≤ d' → ∀ (r : List Bool),
      decodeCircuitTreeAtDepth h_pos width d'
          (encodeCircuitTree width h_width c2 ++ r) = some (c2, r)) :
    decodeCircuitTreeAtDepth h_pos width d
        (encodeCircuitTree width h_width (CircuitTree.or c1 c2) ++ rest) =
      some (CircuitTree.or c1 c2, rest) := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hd1 : c1.size ≤ d' := by omega
  have hd2 : c2.size ≤ d' := by omega
  simp only [encodeCircuitTree, List.cons_append, List.nil_append,
             List.append_assoc, decodeCircuitTreeAtDepth,
             ih1 d' hd1 (encodeCircuitTree width h_width c2 ++ rest),
             ih2 d' hd2 rest]

theorem decode_encode_input {n : Nat} (h_pos : 0 < n) (width : Nat)
    (h_width : n ≤ 2 ^ width) (i : Fin n) (d : Nat) (hd : 1 ≤ d)
    (rest : List Bool) :
    decodeCircuitTreeAtDepth h_pos width d
        (encodeCircuitTree width h_width (CircuitTree.input i) ++ rest) =
      some (CircuitTree.input i, rest) := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  set ifin : Fin (2 ^ width) := ⟨i.val, lt_of_lt_of_le i.isLt h_width⟩ with hifin
  -- Helper facts about the input's take/drop split.
  have hlen_not :
      ¬ (encodeFin width ifin ++ rest).length < width := by
    rw [List.length_append, encodeFin_length]; omega
  have htake :
      (encodeFin width ifin ++ rest).take width = encodeFin width ifin := by
    rw [List.take_append_of_le_length (by rw [encodeFin_length])]
    rw [List.take_of_length_le (by rw [encodeFin_length])]
  have hdrop :
      (encodeFin width ifin ++ rest).drop width = rest := by
    rw [List.drop_append_of_le_length (by rw [encodeFin_length])]
    rw [List.drop_of_length_le (by rw [encodeFin_length])]
    simp
  have hvlt : ifin.val < n := by rw [hifin]; exact i.isLt
  -- Reduce the goal to the exposed decoder-match form.
  show decodeCircuitTreeAtDepth h_pos width (d' + 1)
      (false :: false :: false :: (encodeFin width ifin ++ rest)) =
    some (CircuitTree.input i, rest)
  unfold decodeCircuitTreeAtDepth
  rw [dif_neg hlen_not, htake, hdrop]
  -- Reduce the `have payload := encodeFin width ifin` binding.
  show (match decodeFin width (encodeFin width ifin) with
        | none => none
        | some i_fin =>
          if hv : i_fin.val < n then
            some (CircuitTree.input ⟨i_fin.val, hv⟩, rest)
          else none) = some (CircuitTree.input i, rest)
  rw [decodeFin_encodeFin]
  -- Reduce `match some ifin with ...` via iota.
  show (if hv : ifin.val < n then
          some (CircuitTree.input ⟨ifin.val, hv⟩, rest)
        else none) = some (CircuitTree.input i, rest)
  rw [dif_pos hvlt]

/-- Full round-trip: combines all five constructor-level lemmas
into a single induction on the circuit tree. -/
theorem decodeCircuitTreeAtDepth_encodeCircuitTree
    {n : Nat} (h_pos : 0 < n) (width : Nat)
    (h_width : n ≤ 2 ^ width) (c : CircuitTree n) :
    ∀ (d : Nat), c.size ≤ d →
    ∀ (rest : List Bool),
      decodeCircuitTreeAtDepth h_pos width d
          (encodeCircuitTree width h_width c ++ rest) = some (c, rest) := by
  induction c with
  | input i =>
    intro d h_d rest
    exact decode_encode_input h_pos width h_width i d
      (by simpa [CircuitTree.size] using h_d) rest
  | const b =>
    intro d h_d rest
    exact decode_encode_const h_pos width h_width b d
      (by simpa [CircuitTree.size] using h_d) rest
  | not c ih =>
    intro d h_d rest
    exact decode_encode_not h_pos width h_width c d
      (by simpa [CircuitTree.size] using h_d) rest ih
  | and c1 c2 ih1 ih2 =>
    intro d h_d rest
    exact decode_encode_and h_pos width h_width c1 c2 d
      (by simpa [CircuitTree.size] using h_d) rest ih1 ih2
  | or c1 c2 ih1 ih2 =>
    intro d h_d rest
    exact decode_encode_or h_pos width h_width c1 c2 d
      (by simpa [CircuitTree.size] using h_d) rest ih1 ih2

/-!
## Session 9a: Straight-line program + pure evaluator

The MCSP verifier's evaluation phase naturally matches a
straight-line program: each gate is computed once, from already-
computed prior values.  This is much easier to realise on a TM
than tree-recursive evaluation of `CircuitTree`.

`SLProgram` is a flat sequence of gates.  References to prior
gates are via raw `Nat` indices; `eval` returns `Option Bool`,
yielding `none` on malformed inputs (reference out of range).
Well-formed programs (every reference to a prior index)
evaluate to `some`.

Session 9b will bridge from `CircuitTree` to `SLProgram` via
post-order flattening.  Session 9c will add the bit-level
encoder/decoder on top of Session 8's `encodeFin`.
-/

/-- Single gate in a straight-line program, with references to prior
gates as raw `Nat` indices. -/
inductive SLGate (n : Nat) where
  | input : Fin n → SLGate n
  | const : Bool → SLGate n
  | notGate : Nat → SLGate n
  | andGate : Nat → Nat → SLGate n
  | orGate : Nat → Nat → SLGate n

/-- Evaluate one gate given the input vector and the list of already-
computed prior gate values.  Returns `none` on out-of-range refs. -/
def SLGate.compute {n : Nat} (g : SLGate n) (x : Fin n → Bool)
    (vals : List Bool) : Option Bool :=
  match g with
  | .input i => some (x i)
  | .const b => some b
  | .notGate k => vals[k]?.map (!·)
  | .andGate k l =>
    match vals[k]?, vals[l]? with
    | some a, some b => some (a && b)
    | _, _ => none
  | .orGate k l =>
    match vals[k]?, vals[l]? with
    | some a, some b => some (a || b)
    | _, _ => none

/-- A straight-line program: an ordered list of gates. -/
structure SLProgram (n : Nat) where
  gates : List (SLGate n)

/-- Evaluate a list of gates sequentially from left to right,
accumulating computed values.  `vals` is the initial accumulator
(typically `[]`). -/
def SLProgram.evalAux {n : Nat} (x : Fin n → Bool) :
    List (SLGate n) → List Bool → Option (List Bool)
  | [], vals => some vals
  | g :: rest, vals =>
    match g.compute x vals with
    | none => none
    | some v => SLProgram.evalAux x rest (vals ++ [v])

/-- Evaluate all gates of a straight-line program, returning the full
list of gate values on success. -/
def SLProgram.evalAll {n : Nat} (p : SLProgram n) (x : Fin n → Bool) :
    Option (List Bool) :=
  SLProgram.evalAux x p.gates []

/-- The output value of a straight-line program: the last gate's
computed value (or `none` if the program is empty or malformed). -/
def SLProgram.eval {n : Nat} (p : SLProgram n) (x : Fin n → Bool) :
    Option Bool :=
  (p.evalAll x).bind List.getLast?

/-! ### Basic simp lemmas for `SLGate.compute` -/

@[simp] theorem SLGate.compute_input {n : Nat} (i : Fin n)
    (x : Fin n → Bool) (vals : List Bool) :
    (SLGate.input i).compute x vals = some (x i) := rfl

@[simp] theorem SLGate.compute_const {n : Nat} (b : Bool)
    (x : Fin n → Bool) (vals : List Bool) :
    (SLGate.const b : SLGate n).compute x vals = some b := rfl

@[simp] theorem SLProgram.evalAux_nil {n : Nat} (x : Fin n → Bool)
    (vals : List Bool) :
    SLProgram.evalAux x [] vals = some vals := rfl

theorem SLProgram.evalAux_cons {n : Nat} (x : Fin n → Bool)
    (g : SLGate n) (rest : List (SLGate n)) (vals : List Bool) :
    SLProgram.evalAux x (g :: rest) vals =
      (g.compute x vals).bind
        (fun v => SLProgram.evalAux x rest (vals ++ [v])) := by
  cases hg : g.compute x vals with
  | none => simp [SLProgram.evalAux, hg]
  | some v => simp [SLProgram.evalAux, hg]

/-- After processing a list of `k` gates, the value list has exactly
`k` more entries than the starting accumulator — provided evaluation
succeeds. -/
theorem SLProgram.evalAux_length {n : Nat} (x : Fin n → Bool) :
    ∀ (gates : List (SLGate n)) (vals : List Bool) (result : List Bool),
      SLProgram.evalAux x gates vals = some result →
      result.length = vals.length + gates.length
  | [], vals, result, h => by
    simp [SLProgram.evalAux] at h
    rw [← h]; simp
  | g :: rest, vals, result, h => by
    rw [SLProgram.evalAux_cons] at h
    cases hg : g.compute x vals with
    | none => rw [hg] at h; exact absurd h (by simp)
    | some v =>
      rw [hg] at h
      simp only [Option.bind_some] at h
      have ih := SLProgram.evalAux_length x rest (vals ++ [v]) result h
      simp only [List.length_append, List.length_cons, List.length_nil] at ih
      show result.length = vals.length + (rest.length + 1)
      omega

/-- The full `evalAll` result has length equal to the number of gates
(when evaluation succeeds). -/
theorem SLProgram.evalAll_length {n : Nat} (p : SLProgram n)
    (x : Fin n → Bool) (result : List Bool) :
    p.evalAll x = some result → result.length = p.gates.length := by
  intro h
  have := SLProgram.evalAux_length x p.gates [] result h
  simpa using this

/-- Concatenating two gate lists distributes `evalAux` through
`Option.bind`.  Useful for splitting flattened circuit evaluation. -/
theorem SLProgram.evalAux_append {n : Nat} (x : Fin n → Bool) :
    ∀ (gs1 gs2 : List (SLGate n)) (vals : List Bool),
    SLProgram.evalAux x (gs1 ++ gs2) vals =
      (SLProgram.evalAux x gs1 vals).bind
        (fun vals' => SLProgram.evalAux x gs2 vals')
  | [], _, _ => by simp [SLProgram.evalAux]
  | g :: rest, gs2, vals => by
    simp only [List.cons_append, SLProgram.evalAux_cons]
    cases hg : g.compute x vals with
    | none => simp
    | some v =>
      simp only [Option.bind_some]
      exact SLProgram.evalAux_append x rest gs2 (vals ++ [v])

/-!
## Session 9b: `CircuitTree → SLProgram` flattening

Post-order flatten: each subtree emits its own gates first; the
current node is appended at the end, referencing subtree outputs
by their absolute positions.  The offset parameter shifts
references so the flattened program can sit at any position within
a larger accumulator.

The semantic equivalence theorem shows that pure `evalCircuitTree`
applied to `c` matches `SLProgram.eval` applied to the flattened
straight-line program.
-/

/-- Pure-Lean tree evaluator for `CircuitTree` — mirrors
`Models.Circuit.eval` but lives local to the Encoding namespace. -/
def evalCircuitTree {n : Nat} : CircuitTree n → (Fin n → Bool) → Bool
  | .input i, x => x i
  | .const b, _ => b
  | .not c, x => !(evalCircuitTree c x)
  | .and c1 c2, x => evalCircuitTree c1 x && evalCircuitTree c2 x
  | .or c1 c2, x => evalCircuitTree c1 x || evalCircuitTree c2 x

/-- Post-order flatten with an explicit offset.  The offset tells
`flattenAt` how many gates are already in the accumulator before it
starts emitting its own. -/
def CircuitTree.flattenAt {n : Nat} (offset : Nat) :
    CircuitTree n → List (SLGate n)
  | .input i => [SLGate.input i]
  | .const b => [SLGate.const b]
  | .not c =>
    let sub := CircuitTree.flattenAt offset c
    sub ++ [SLGate.notGate (offset + sub.length - 1)]
  | .and c1 c2 =>
    let sub1 := CircuitTree.flattenAt offset c1
    let sub2 := CircuitTree.flattenAt (offset + sub1.length) c2
    sub1 ++ sub2 ++ [SLGate.andGate
                       (offset + sub1.length - 1)
                       (offset + sub1.length + sub2.length - 1)]
  | .or c1 c2 =>
    let sub1 := CircuitTree.flattenAt offset c1
    let sub2 := CircuitTree.flattenAt (offset + sub1.length) c2
    sub1 ++ sub2 ++ [SLGate.orGate
                      (offset + sub1.length - 1)
                      (offset + sub1.length + sub2.length - 1)]

/-- Convenience: flatten starting at offset 0. -/
def CircuitTree.flatten {n : Nat} (c : CircuitTree n) : SLProgram n :=
  ⟨CircuitTree.flattenAt 0 c⟩

/-- The flattened length equals the circuit's tree size: each node
contributes exactly one gate, independent of the offset. -/
theorem CircuitTree.flattenAt_length {n : Nat} (offset : Nat) :
    ∀ (c : CircuitTree n), (CircuitTree.flattenAt offset c).length = c.size
  | .input _ => by simp [CircuitTree.flattenAt, CircuitTree.size]
  | .const _ => by simp [CircuitTree.flattenAt, CircuitTree.size]
  | .not c => by
    simp only [CircuitTree.flattenAt, CircuitTree.size,
               List.length_append, List.length_cons, List.length_nil]
    have := CircuitTree.flattenAt_length offset c
    omega
  | .and c1 c2 => by
    simp only [CircuitTree.flattenAt, CircuitTree.size,
               List.length_append, List.length_cons, List.length_nil]
    have h1 := CircuitTree.flattenAt_length offset c1
    have h2 := CircuitTree.flattenAt_length
      (offset + (CircuitTree.flattenAt offset c1).length) c2
    omega
  | .or c1 c2 => by
    simp only [CircuitTree.flattenAt, CircuitTree.size,
               List.length_append, List.length_cons, List.length_nil]
    have h1 := CircuitTree.flattenAt_length offset c1
    have h2 := CircuitTree.flattenAt_length
      (offset + (CircuitTree.flattenAt offset c1).length) c2
    omega

/-- Flatten at offset 0 gives the circuit's size as the gate count. -/
@[simp] theorem CircuitTree.flatten_length {n : Nat} (c : CircuitTree n) :
    (CircuitTree.flatten c).gates.length = c.size := by
  unfold CircuitTree.flatten
  exact CircuitTree.flattenAt_length 0 c

/-!
### Flattening correctness: evaluating a flattened circuit yields
the same bit as the tree evaluator.

The core lemma `flattenAt_evalAux_spec` captures the invariant:
when the initial accumulator has length equal to the flatten's
offset, `evalAux` extends the accumulator by a sequence of values
whose last entry equals `evalCircuitTree c x`.

From this, `flatten_eval` (the public lemma) follows by
specialising to offset = 0 and extracting the last entry via
`getLast?`.
-/

/-- For any initial accumulator `vals`, flattening `c` with offset
`vals.length` extends the accumulator by `c.size` values, whose last
element is `evalCircuitTree c x`. -/
theorem CircuitTree.flattenAt_evalAux_spec {n : Nat} :
    ∀ (c : CircuitTree n) (x : Fin n → Bool) (vals : List Bool),
      ∃ (sub_vals : List Bool),
        sub_vals.length = c.size ∧
        sub_vals.getLast? = some (evalCircuitTree c x) ∧
        SLProgram.evalAux x (c.flattenAt vals.length) vals =
          some (vals ++ sub_vals)
  | .input i, x, vals => by
    refine ⟨[x i], ?_, ?_, ?_⟩
    · simp [CircuitTree.size]
    · simp [evalCircuitTree]
    · simp [CircuitTree.flattenAt, SLProgram.evalAux, SLGate.compute]
  | .const b, x, vals => by
    refine ⟨[b], ?_, ?_, ?_⟩
    · simp [CircuitTree.size]
    · simp [evalCircuitTree]
    · simp [CircuitTree.flattenAt, SLProgram.evalAux, SLGate.compute]
  | .not c, x, vals => by
    obtain ⟨sub_c, hlen_c, hlast_c, heval_c⟩ :=
      CircuitTree.flattenAt_evalAux_spec c x vals
    -- The extra gate at the tail references position
    -- `vals.length + |flattenAt vals.length c| - 1`.
    have hlen_flat : (c.flattenAt vals.length).length = c.size :=
      CircuitTree.flattenAt_length _ _
    set ext_vals := vals ++ sub_c with hext
    have hext_len : ext_vals.length = vals.length + c.size := by
      rw [hext, List.length_append, hlen_c]
    -- After processing `flattenAt vals.length c`, we're at
    -- `ext_vals`.  One more gate: notGate at the last index.
    set k : Nat := vals.length + (c.flattenAt vals.length).length - 1 with hk_def
    have hk : k = ext_vals.length - 1 := by
      rw [hext_len, hk_def, hlen_flat]
    have hsize_pos : 0 < c.size := by
      cases c <;> simp [CircuitTree.size]
    have hlen_c_pos : 0 < sub_c.length := by rw [hlen_c]; exact hsize_pos
    have hk_in_sub : k ≥ vals.length := by
      rw [hk_def, hlen_flat]; omega
    have hk_sub_val : k - vals.length = sub_c.length - 1 := by
      rw [hk_def, hlen_flat, hlen_c]; omega
    -- Look up at position k in ext_vals = vals ++ sub_c.
    have hget :
        ext_vals[k]? = sub_c.getLast? := by
      rw [hext, List.getElem?_append_right hk_in_sub, hk_sub_val,
          ← List.getLast?_eq_getElem?]
    have hcompute_not :
        (SLGate.notGate k : SLGate n).compute x ext_vals =
          some (!(evalCircuitTree c x)) := by
      simp only [SLGate.compute, hget, hlast_c, Option.map_some]
    -- Assemble the result.
    refine ⟨sub_c ++ [!(evalCircuitTree c x)], ?_, ?_, ?_⟩
    · simp [hlen_c, CircuitTree.size]
    · simp [evalCircuitTree]
    · show SLProgram.evalAux x
          ((c.flattenAt vals.length) ++ [SLGate.notGate k]) vals =
          some (vals ++ (sub_c ++ [!(evalCircuitTree c x)]))
      rw [SLProgram.evalAux_append, heval_c, Option.bind_some]
      show SLProgram.evalAux x [SLGate.notGate k] ext_vals =
          some (vals ++ (sub_c ++ [!(evalCircuitTree c x)]))
      rw [SLProgram.evalAux_cons, hcompute_not, Option.bind_some,
          SLProgram.evalAux_nil]
      simp [hext]
  | .and c1 c2, x, vals => by
    obtain ⟨sub_c1, hlen1, hlast1, heval1⟩ :=
      CircuitTree.flattenAt_evalAux_spec c1 x vals
    set ext_vals1 := vals ++ sub_c1 with hext1
    have hext1_len : ext_vals1.length = vals.length + c1.size := by
      rw [hext1, List.length_append, hlen1]
    obtain ⟨sub_c2, hlen2, hlast2, heval2⟩ :=
      CircuitTree.flattenAt_evalAux_spec c2 x ext_vals1
    set ext_vals2 := ext_vals1 ++ sub_c2 with hext2
    have hext2_len : ext_vals2.length = vals.length + c1.size + c2.size := by
      rw [hext2, List.length_append, hlen2, hext1_len]
    -- Gate positions for the and gate.
    have hlen_flat1 : (c1.flattenAt vals.length).length = c1.size :=
      CircuitTree.flattenAt_length _ _
    have hlen_flat2 :
        (c2.flattenAt (vals.length + c1.size)).length = c2.size :=
      CircuitTree.flattenAt_length _ _
    set kL : Nat := vals.length + (c1.flattenAt vals.length).length - 1 with hkL_def
    set kR : Nat := vals.length + (c1.flattenAt vals.length).length +
        (c2.flattenAt (vals.length + (c1.flattenAt vals.length).length)).length - 1
        with hkR_def
    have hsize1_pos : 0 < c1.size := by cases c1 <;> simp [CircuitTree.size]
    have hsize2_pos : 0 < c2.size := by cases c2 <;> simp [CircuitTree.size]
    have hkL_ge : kL ≥ vals.length := by
      rw [hkL_def, hlen_flat1]; omega
    have hkL_sub : kL - vals.length = sub_c1.length - 1 := by
      rw [hkL_def, hlen_flat1, hlen1]; omega
    have hkR_ge : kR ≥ ext_vals1.length := by
      rw [hkR_def, hlen_flat1, hlen_flat2, hext1_len]; omega
    have hkR_sub : kR - ext_vals1.length = sub_c2.length - 1 := by
      rw [hkR_def, hlen_flat1, hlen_flat2, hext1_len, hlen2]; omega
    -- get? at kL in ext_vals2 = vals ++ sub_c1 ++ sub_c2.
    -- Since kL is in the c1 range.
    have hkL_lt_ext1 : kL < ext_vals1.length := by
      rw [hext1_len, hkL_def, hlen_flat1]; omega
    have hget_kL : ext_vals2[kL]? = sub_c1.getLast? := by
      rw [hext2,
          List.getElem?_append_left hkL_lt_ext1, hext1,
          List.getElem?_append_right hkL_ge, hkL_sub,
          ← List.getLast?_eq_getElem?]
    have hget_kR : ext_vals2[kR]? = sub_c2.getLast? := by
      rw [hext2,
          List.getElem?_append_right hkR_ge, hkR_sub,
          ← List.getLast?_eq_getElem?]
    have hcompute_and :
        (SLGate.andGate kL kR : SLGate n).compute x ext_vals2 =
          some (evalCircuitTree c1 x && evalCircuitTree c2 x) := by
      simp only [SLGate.compute, hget_kL, hlast1, hget_kR, hlast2]
    refine ⟨sub_c1 ++ sub_c2 ++ [evalCircuitTree c1 x && evalCircuitTree c2 x],
        ?_, ?_, ?_⟩
    · simp [hlen1, hlen2, CircuitTree.size]; omega
    · simp [evalCircuitTree]
    · show SLProgram.evalAux x
          ((c1.flattenAt vals.length) ++
            (c2.flattenAt (vals.length + (c1.flattenAt vals.length).length)) ++
            [SLGate.andGate kL kR]) vals =
          some (vals ++ (sub_c1 ++ sub_c2 ++
            [evalCircuitTree c1 x && evalCircuitTree c2 x]))
      rw [SLProgram.evalAux_append, SLProgram.evalAux_append, heval1,
          Option.bind_some]
      show (SLProgram.evalAux x
              (c2.flattenAt (vals.length + (c1.flattenAt vals.length).length))
              ext_vals1).bind
            (fun vals' => SLProgram.evalAux x [SLGate.andGate kL kR] vals') =
          some (vals ++ (sub_c1 ++ sub_c2 ++ _))
      rw [show vals.length + (c1.flattenAt vals.length).length = ext_vals1.length
            from by rw [hlen_flat1, hext1_len]]
      rw [heval2, Option.bind_some]
      show SLProgram.evalAux x [SLGate.andGate kL kR] ext_vals2 =
          some (vals ++ (sub_c1 ++ sub_c2 ++ _))
      rw [SLProgram.evalAux_cons, hcompute_and, Option.bind_some,
          SLProgram.evalAux_nil]
      simp [hext2, hext1, List.append_assoc]
  | .or c1 c2, x, vals => by
    -- Symmetric to `.and`; duplicate the proof with `||` instead of `&&`.
    obtain ⟨sub_c1, hlen1, hlast1, heval1⟩ :=
      CircuitTree.flattenAt_evalAux_spec c1 x vals
    set ext_vals1 := vals ++ sub_c1 with hext1
    have hext1_len : ext_vals1.length = vals.length + c1.size := by
      rw [hext1, List.length_append, hlen1]
    obtain ⟨sub_c2, hlen2, hlast2, heval2⟩ :=
      CircuitTree.flattenAt_evalAux_spec c2 x ext_vals1
    set ext_vals2 := ext_vals1 ++ sub_c2 with hext2
    have hext2_len : ext_vals2.length = vals.length + c1.size + c2.size := by
      rw [hext2, List.length_append, hlen2, hext1_len]
    have hlen_flat1 : (c1.flattenAt vals.length).length = c1.size :=
      CircuitTree.flattenAt_length _ _
    have hlen_flat2 :
        (c2.flattenAt (vals.length + c1.size)).length = c2.size :=
      CircuitTree.flattenAt_length _ _
    set kL : Nat := vals.length + (c1.flattenAt vals.length).length - 1 with hkL_def
    set kR : Nat := vals.length + (c1.flattenAt vals.length).length +
        (c2.flattenAt (vals.length + (c1.flattenAt vals.length).length)).length - 1
        with hkR_def
    have hsize1_pos : 0 < c1.size := by cases c1 <;> simp [CircuitTree.size]
    have hsize2_pos : 0 < c2.size := by cases c2 <;> simp [CircuitTree.size]
    have hkL_ge : kL ≥ vals.length := by rw [hkL_def, hlen_flat1]; omega
    have hkL_sub : kL - vals.length = sub_c1.length - 1 := by
      rw [hkL_def, hlen_flat1, hlen1]; omega
    have hkR_ge : kR ≥ ext_vals1.length := by
      rw [hkR_def, hlen_flat1, hlen_flat2, hext1_len]; omega
    have hkR_sub : kR - ext_vals1.length = sub_c2.length - 1 := by
      rw [hkR_def, hlen_flat1, hlen_flat2, hext1_len, hlen2]; omega
    have hkL_lt_ext1 : kL < ext_vals1.length := by
      rw [hext1_len, hkL_def, hlen_flat1]; omega
    have hget_kL : ext_vals2[kL]? = sub_c1.getLast? := by
      rw [hext2,
          List.getElem?_append_left hkL_lt_ext1, hext1,
          List.getElem?_append_right hkL_ge, hkL_sub,
          ← List.getLast?_eq_getElem?]
    have hget_kR : ext_vals2[kR]? = sub_c2.getLast? := by
      rw [hext2,
          List.getElem?_append_right hkR_ge, hkR_sub,
          ← List.getLast?_eq_getElem?]
    have hcompute_or :
        (SLGate.orGate kL kR : SLGate n).compute x ext_vals2 =
          some (evalCircuitTree c1 x || evalCircuitTree c2 x) := by
      simp only [SLGate.compute, hget_kL, hlast1, hget_kR, hlast2]
    refine ⟨sub_c1 ++ sub_c2 ++ [evalCircuitTree c1 x || evalCircuitTree c2 x],
        ?_, ?_, ?_⟩
    · simp [hlen1, hlen2, CircuitTree.size]; omega
    · simp [evalCircuitTree]
    · show SLProgram.evalAux x
          ((c1.flattenAt vals.length) ++
            (c2.flattenAt (vals.length + (c1.flattenAt vals.length).length)) ++
            [SLGate.orGate kL kR]) vals =
          some (vals ++ (sub_c1 ++ sub_c2 ++
            [evalCircuitTree c1 x || evalCircuitTree c2 x]))
      rw [SLProgram.evalAux_append, SLProgram.evalAux_append, heval1,
          Option.bind_some]
      show (SLProgram.evalAux x
              (c2.flattenAt (vals.length + (c1.flattenAt vals.length).length))
              ext_vals1).bind
            (fun vals' => SLProgram.evalAux x [SLGate.orGate kL kR] vals') =
          some (vals ++ (sub_c1 ++ sub_c2 ++ _))
      rw [show vals.length + (c1.flattenAt vals.length).length = ext_vals1.length
            from by rw [hlen_flat1, hext1_len]]
      rw [heval2, Option.bind_some]
      show SLProgram.evalAux x [SLGate.orGate kL kR] ext_vals2 =
          some (vals ++ (sub_c1 ++ sub_c2 ++ _))
      rw [SLProgram.evalAux_cons, hcompute_or, Option.bind_some,
          SLProgram.evalAux_nil]
      simp [hext2, hext1, List.append_assoc]

/-- Public form: flatten and evaluate = pure tree evaluation. -/
theorem CircuitTree.flatten_eval {n : Nat} (c : CircuitTree n)
    (x : Fin n → Bool) :
    (CircuitTree.flatten c).eval x = some (evalCircuitTree c x) := by
  obtain ⟨sub_vals, _hlen, hlast, heval⟩ :=
    CircuitTree.flattenAt_evalAux_spec c x []
  unfold CircuitTree.flatten SLProgram.eval SLProgram.evalAll
  show (SLProgram.evalAux x (c.flattenAt 0) []).bind List.getLast? =
      some (evalCircuitTree c x)
  rw [show (0 : Nat) = ([] : List Bool).length from rfl]
  rw [heval]
  simp [hlast]

/-!
## Session 9c: SLProgram bit encoding

Flat bit encoding of straight-line programs using Session 8a's
`encodeFin` primitive.  Two width parameters:

* `widthN`: bits for input indices (requires `n ≤ 2^widthN`).
* `widthS`: bits for gate references (requires caller to ensure
  references `< 2^widthS`).

Tag scheme (3 bits):
* `000` — `.input i`     → followed by `widthN` bits for the `Fin n`.
* `001` — `.const b`     → followed by a single bit.
* `010` — `.notGate k`   → followed by `widthS` bits for `k`.
* `011` — `.andGate k l` → followed by `widthS + widthS` bits.
* `100` — `.orGate k l`  → followed by `widthS + widthS` bits.

Each gate's encoding is at most `3 + max(widthN, 1, 2·widthS)` bits,
which we simplify to the uniform upper bound `3 + widthN + 2·widthS`.
A decoder + round-trip theorem are the natural next step; this
session 9c delivers only the encoder + length bound, leaving the
decoder for Session 9d.
-/

/-- Encode a single straight-line gate as a bit list.  Gate-reference
arguments that overflow `2^widthS` are silently clamped to a
zero-filled encoding; the encoder assumes valid refs and the
round-trip theorem (Session 9d) will handle this formally. -/
def SLGate.encode {n : Nat} (widthN widthS : Nat)
    (h_widthN : n ≤ 2 ^ widthN) : SLGate n → List Bool
  | .input i =>
    [false, false, false] ++
      encodeFin widthN ⟨i.val, lt_of_lt_of_le i.isLt h_widthN⟩
  | .const b => [false, false, true, b]
  | .notGate k =>
    [false, true, false] ++
      encodeFin widthS (if h : k < 2 ^ widthS then ⟨k, h⟩ else ⟨0, Nat.two_pow_pos widthS⟩)
  | .andGate k l =>
    [false, true, true] ++
      encodeFin widthS (if h : k < 2 ^ widthS then ⟨k, h⟩ else ⟨0, Nat.two_pow_pos widthS⟩) ++
      encodeFin widthS (if h : l < 2 ^ widthS then ⟨l, h⟩ else ⟨0, Nat.two_pow_pos widthS⟩)
  | .orGate k l =>
    [true, false, false] ++
      encodeFin widthS (if h : k < 2 ^ widthS then ⟨k, h⟩ else ⟨0, Nat.two_pow_pos widthS⟩) ++
      encodeFin widthS (if h : l < 2 ^ widthS then ⟨l, h⟩ else ⟨0, Nat.two_pow_pos widthS⟩)

/-- Uniform upper bound on a gate's encoding length.  The constant
4 accounts for `.const`'s 4-bit encoding (3 tag + 1 payload),
which can otherwise exceed a tighter `3 + widthN + 2·widthS`
bound when both widths are small. -/
theorem SLGate.encode_length_le {n : Nat} (widthN widthS : Nat)
    (h_widthN : n ≤ 2 ^ widthN) : ∀ (g : SLGate n),
    (g.encode widthN widthS h_widthN).length ≤ 4 + widthN + 2 * widthS
  | .input _ => by
    simp [SLGate.encode, encodeFin_length]
    omega
  | .const _ => by
    show (4 : Nat) ≤ 4 + widthN + 2 * widthS
    omega
  | .notGate _ => by
    simp [SLGate.encode, encodeFin_length]
    omega
  | .andGate _ _ => by
    simp [SLGate.encode, encodeFin_length]
    omega
  | .orGate _ _ => by
    simp [SLGate.encode, encodeFin_length]
    omega

/-- Encode a straight-line program as the concatenation of its gate
encodings. -/
def SLProgram.encode {n : Nat} (widthN widthS : Nat)
    (h_widthN : n ≤ 2 ^ widthN) (p : SLProgram n) : List Bool :=
  p.gates.foldr (fun g acc => g.encode widthN widthS h_widthN ++ acc) []

/-- Total encoding length is bounded by (per-gate cap) × (number of
gates).  Used to show the witness budget suffices. -/
theorem SLProgram.encode_length_le {n : Nat} (widthN widthS : Nat)
    (h_widthN : n ≤ 2 ^ widthN) (p : SLProgram n) :
    (p.encode widthN widthS h_widthN).length ≤
      (4 + widthN + 2 * widthS) * p.gates.length := by
  unfold SLProgram.encode
  induction p.gates with
  | nil => simp
  | cons g rest ih =>
    simp only [List.foldr_cons, List.length_append, List.length_cons]
    have hg := SLGate.encode_length_le widthN widthS h_widthN g
    set N : Nat := 4 + widthN + 2 * widthS
    have hsucc : N * (rest.length + 1) = N * rest.length + N :=
      Nat.mul_succ N rest.length
    rw [hsucc]
    omega

/-!
## Session 9d: SLProgram decoder + round-trip

Decoder parses a bit list gate-by-gate into an `SLGate n × List Bool`
(gate + remaining tail).  The full `SLProgram.decode` reads exactly
the specified gate count.

Round-trip holds under a well-formedness condition: gate references
must fit in `2^widthS`.  Invalid references are clamped by the
encoder (to 0), so without the hypothesis the round-trip would
decode a *normalised* version of the gate rather than the original.
-/

/-- Well-formedness predicate for a single gate: references fit in the
declared width bound. -/
def SLGate.wellFormedUnder (widthS : Nat) {n : Nat} : SLGate n → Prop
  | .input _ => True
  | .const _ => True
  | .notGate k => k < 2 ^ widthS
  | .andGate k l => k < 2 ^ widthS ∧ l < 2 ^ widthS
  | .orGate k l => k < 2 ^ widthS ∧ l < 2 ^ widthS

/-- Well-formedness predicate for a program: every gate's
references fit. -/
def SLProgram.wellFormedUnder (widthS : Nat) {n : Nat} (p : SLProgram n) : Prop :=
  ∀ g ∈ p.gates, g.wellFormedUnder widthS

/-- Decode a single gate from a bit list.  On success, returns the gate
paired with the remaining tail.  Returns `none` on malformed input. -/
def SLGate.decode {n : Nat} (widthN widthS : Nat) (_h_pos : 0 < n) :
    List Bool → Option (SLGate n × List Bool)
  | [] => none
  | _ :: [] => none
  | _ :: _ :: [] => none
  | false :: false :: false :: rest =>
    if _ : rest.length < widthN then none
    else
      match decodeFin widthN (rest.take widthN) with
      | none => none
      | some i_fin =>
        if hv : i_fin.val < n then
          some (SLGate.input ⟨i_fin.val, hv⟩, rest.drop widthN)
        else none
  | false :: false :: true :: b :: rest =>
    some (SLGate.const b, rest)
  | false :: true :: false :: rest =>
    if _ : rest.length < widthS then none
    else
      match decodeFin widthS (rest.take widthS) with
      | none => none
      | some k_fin =>
        some (SLGate.notGate k_fin.val, rest.drop widthS)
  | false :: true :: true :: rest =>
    if _ : rest.length < widthS then none
    else
      match decodeFin widthS (rest.take widthS) with
      | none => none
      | some k_fin =>
        let rest' := rest.drop widthS
        if _ : rest'.length < widthS then none
        else
          match decodeFin widthS (rest'.take widthS) with
          | none => none
          | some l_fin =>
            some (SLGate.andGate k_fin.val l_fin.val, rest'.drop widthS)
  | true :: false :: false :: rest =>
    if _ : rest.length < widthS then none
    else
      match decodeFin widthS (rest.take widthS) with
      | none => none
      | some k_fin =>
        let rest' := rest.drop widthS
        if _ : rest'.length < widthS then none
        else
          match decodeFin widthS (rest'.take widthS) with
          | none => none
          | some l_fin =>
            some (SLGate.orGate k_fin.val l_fin.val, rest'.drop widthS)
  | _ :: _ :: _ :: _ => none

/-- Decode `N` gates in sequence from a bit list.  Returns the parsed
program and the remaining tail. -/
def SLProgram.decode {n : Nat} (widthN widthS : Nat) (h_pos : 0 < n) :
    Nat → List Bool → Option (SLProgram n × List Bool)
  | 0, bs => some (⟨[]⟩, bs)
  | N + 1, bs =>
    match SLGate.decode widthN widthS h_pos bs with
    | none => none
    | some (g, rest) =>
      match SLProgram.decode widthN widthS h_pos N rest with
      | none => none
      | some (⟨gs⟩, rest') =>
        some (⟨g :: gs⟩, rest')

/-!
### Per-constructor round-trip lemmas for `SLGate.decode`

Each lemma assumes the gate's references (if any) are within
`2^widthS` so the encoder is lossless.  `.input` additionally
relies on `n ≤ 2^widthN` (the encoder's precondition) to fit
the index into the bit-level encoding.
-/

theorem SLGate.decode_encode_input {n : Nat} (widthN widthS : Nat)
    (h_pos : 0 < n) (h_widthN : n ≤ 2 ^ widthN)
    (i : Fin n) (rest : List Bool) :
    SLGate.decode widthN widthS h_pos
        ((SLGate.input i).encode widthN widthS h_widthN ++ rest) =
      some (SLGate.input i, rest) := by
  set ifin : Fin (2 ^ widthN) := ⟨i.val, lt_of_lt_of_le i.isLt h_widthN⟩ with hifin
  simp only [SLGate.encode, List.cons_append, List.nil_append,
             SLGate.decode]
  have hlen_not : ¬ (encodeFin widthN ifin ++ rest).length < widthN := by
    rw [List.length_append, encodeFin_length]; omega
  rw [dif_neg hlen_not]
  have htake :
      (encodeFin widthN ifin ++ rest).take widthN = encodeFin widthN ifin := by
    rw [List.take_append_of_le_length (by rw [encodeFin_length])]
    rw [List.take_of_length_le (by rw [encodeFin_length])]
  have hdrop :
      (encodeFin widthN ifin ++ rest).drop widthN = rest := by
    rw [List.drop_append_of_le_length (by rw [encodeFin_length])]
    rw [List.drop_of_length_le (by rw [encodeFin_length])]
    simp
  show (match decodeFin widthN
            ((encodeFin widthN ifin ++ rest).take widthN) with
        | none => none
        | some i_fin =>
          if hv : i_fin.val < n then
            some (SLGate.input ⟨i_fin.val, hv⟩,
              (encodeFin widthN ifin ++ rest).drop widthN)
          else none) = some (SLGate.input i, rest)
  rw [htake, hdrop, decodeFin_encodeFin]
  show (if hv : ifin.val < n then
          some (SLGate.input ⟨ifin.val, hv⟩, rest)
        else none) = some (SLGate.input i, rest)
  have hv : ifin.val < n := by rw [hifin]; exact i.isLt
  rw [dif_pos hv]

theorem SLGate.decode_encode_const {n : Nat} (widthN widthS : Nat)
    (h_pos : 0 < n) (h_widthN : n ≤ 2 ^ widthN)
    (b : Bool) (rest : List Bool) :
    SLGate.decode widthN widthS h_pos
        ((SLGate.const b : SLGate n).encode widthN widthS h_widthN ++ rest) =
      some (SLGate.const b, rest) := by
  simp [SLGate.encode, SLGate.decode]

theorem SLGate.decode_encode_not {n : Nat} (widthN widthS : Nat)
    (h_pos : 0 < n) (h_widthN : n ≤ 2 ^ widthN)
    (k : Nat) (hk : k < 2 ^ widthS) (rest : List Bool) :
    SLGate.decode widthN widthS h_pos
        ((SLGate.notGate k : SLGate n).encode widthN widthS h_widthN ++ rest) =
      some (SLGate.notGate k, rest) := by
  set kfin : Fin (2 ^ widthS) := ⟨k, hk⟩ with hkfin
  simp only [SLGate.encode, List.cons_append, List.nil_append,
             SLGate.decode]
  rw [dif_pos hk]
  have hlen_not :
      ¬ (encodeFin widthS kfin ++ rest).length < widthS := by
    rw [List.length_append, encodeFin_length]; omega
  rw [dif_neg hlen_not]
  have htake :
      (encodeFin widthS kfin ++ rest).take widthS = encodeFin widthS kfin := by
    rw [List.take_append_of_le_length (by rw [encodeFin_length])]
    rw [List.take_of_length_le (by rw [encodeFin_length])]
  have hdrop :
      (encodeFin widthS kfin ++ rest).drop widthS = rest := by
    rw [List.drop_append_of_le_length (by rw [encodeFin_length])]
    rw [List.drop_of_length_le (by rw [encodeFin_length])]
    simp
  show (match decodeFin widthS
            ((encodeFin widthS kfin ++ rest).take widthS) with
        | none => none
        | some k_fin =>
          some (SLGate.notGate k_fin.val,
            (encodeFin widthS kfin ++ rest).drop widthS)) =
      some (SLGate.notGate k, rest)
  rw [htake, hdrop, decodeFin_encodeFin]

theorem SLGate.decode_encode_and {n : Nat} (widthN widthS : Nat)
    (h_pos : 0 < n) (h_widthN : n ≤ 2 ^ widthN)
    (k l : Nat) (hk : k < 2 ^ widthS) (hl : l < 2 ^ widthS)
    (rest : List Bool) :
    SLGate.decode widthN widthS h_pos
        ((SLGate.andGate k l : SLGate n).encode widthN widthS h_widthN ++ rest) =
      some (SLGate.andGate k l, rest) := by
  set kfin : Fin (2 ^ widthS) := ⟨k, hk⟩ with hkfin
  set lfin : Fin (2 ^ widthS) := ⟨l, hl⟩ with hlfin
  simp only [SLGate.encode, List.cons_append, List.nil_append,
             List.append_assoc, SLGate.decode]
  rw [dif_pos hk, dif_pos hl]
  set tail_after_k := encodeFin widthS lfin ++ rest with htail_k_def
  have hlen_full : ¬ (encodeFin widthS kfin ++ tail_after_k).length < widthS := by
    rw [List.length_append, encodeFin_length]; omega
  rw [dif_neg hlen_full]
  have htake_k :
      (encodeFin widthS kfin ++ tail_after_k).take widthS = encodeFin widthS kfin := by
    rw [List.take_append_of_le_length (by rw [encodeFin_length])]
    rw [List.take_of_length_le (by rw [encodeFin_length])]
  have hdrop_k :
      (encodeFin widthS kfin ++ tail_after_k).drop widthS = tail_after_k := by
    rw [List.drop_append_of_le_length (by rw [encodeFin_length])]
    rw [List.drop_of_length_le (by rw [encodeFin_length])]
    simp
  show (match decodeFin widthS
            ((encodeFin widthS kfin ++ tail_after_k).take widthS) with
        | none => none
        | some k_fin =>
          let rest' := (encodeFin widthS kfin ++ tail_after_k).drop widthS
          if hlen' : rest'.length < widthS then none
          else
            match decodeFin widthS (rest'.take widthS) with
            | none => none
            | some l_fin =>
              some (SLGate.andGate k_fin.val l_fin.val, rest'.drop widthS)) =
      some (SLGate.andGate k l, rest)
  rw [htake_k, hdrop_k, decodeFin_encodeFin]
  show (let rest' := tail_after_k
        if hlen' : rest'.length < widthS then none
        else
          match decodeFin widthS (rest'.take widthS) with
          | none => none
          | some l_fin =>
            some (SLGate.andGate kfin.val l_fin.val, rest'.drop widthS)) =
      some (SLGate.andGate k l, rest)
  have hlen_l : ¬ tail_after_k.length < widthS := by
    rw [htail_k_def, List.length_append, encodeFin_length]; omega
  rw [dif_neg hlen_l]
  have htake_l :
      tail_after_k.take widthS = encodeFin widthS lfin := by
    rw [htail_k_def, List.take_append_of_le_length (by rw [encodeFin_length])]
    rw [List.take_of_length_le (by rw [encodeFin_length])]
  have hdrop_l :
      tail_after_k.drop widthS = rest := by
    rw [htail_k_def, List.drop_append_of_le_length (by rw [encodeFin_length])]
    rw [List.drop_of_length_le (by rw [encodeFin_length])]
    simp
  show (match decodeFin widthS (tail_after_k.take widthS) with
        | none => none
        | some l_fin =>
          some (SLGate.andGate kfin.val l_fin.val, tail_after_k.drop widthS)) =
      some (SLGate.andGate k l, rest)
  rw [htake_l, hdrop_l, decodeFin_encodeFin]

theorem SLGate.decode_encode_or {n : Nat} (widthN widthS : Nat)
    (h_pos : 0 < n) (h_widthN : n ≤ 2 ^ widthN)
    (k l : Nat) (hk : k < 2 ^ widthS) (hl : l < 2 ^ widthS)
    (rest : List Bool) :
    SLGate.decode widthN widthS h_pos
        ((SLGate.orGate k l : SLGate n).encode widthN widthS h_widthN ++ rest) =
      some (SLGate.orGate k l, rest) := by
  -- Symmetric to `.and`, swapping tag `011` for `100` and constructor
  -- `andGate` for `orGate`.
  set kfin : Fin (2 ^ widthS) := ⟨k, hk⟩ with hkfin
  set lfin : Fin (2 ^ widthS) := ⟨l, hl⟩ with hlfin
  simp only [SLGate.encode, List.cons_append, List.nil_append,
             List.append_assoc, SLGate.decode]
  rw [dif_pos hk, dif_pos hl]
  set tail_after_k := encodeFin widthS lfin ++ rest with htail_k_def
  have hlen_full : ¬ (encodeFin widthS kfin ++ tail_after_k).length < widthS := by
    rw [List.length_append, encodeFin_length]; omega
  rw [dif_neg hlen_full]
  have htake_k :
      (encodeFin widthS kfin ++ tail_after_k).take widthS = encodeFin widthS kfin := by
    rw [List.take_append_of_le_length (by rw [encodeFin_length])]
    rw [List.take_of_length_le (by rw [encodeFin_length])]
  have hdrop_k :
      (encodeFin widthS kfin ++ tail_after_k).drop widthS = tail_after_k := by
    rw [List.drop_append_of_le_length (by rw [encodeFin_length])]
    rw [List.drop_of_length_le (by rw [encodeFin_length])]
    simp
  show (match decodeFin widthS
            ((encodeFin widthS kfin ++ tail_after_k).take widthS) with
        | none => none
        | some k_fin =>
          let rest' := (encodeFin widthS kfin ++ tail_after_k).drop widthS
          if hlen' : rest'.length < widthS then none
          else
            match decodeFin widthS (rest'.take widthS) with
            | none => none
            | some l_fin =>
              some (SLGate.orGate k_fin.val l_fin.val, rest'.drop widthS)) =
      some (SLGate.orGate k l, rest)
  rw [htake_k, hdrop_k, decodeFin_encodeFin]
  show (let rest' := tail_after_k
        if hlen' : rest'.length < widthS then none
        else
          match decodeFin widthS (rest'.take widthS) with
          | none => none
          | some l_fin =>
            some (SLGate.orGate kfin.val l_fin.val, rest'.drop widthS)) =
      some (SLGate.orGate k l, rest)
  have hlen_l : ¬ tail_after_k.length < widthS := by
    rw [htail_k_def, List.length_append, encodeFin_length]; omega
  rw [dif_neg hlen_l]
  have htake_l :
      tail_after_k.take widthS = encodeFin widthS lfin := by
    rw [htail_k_def, List.take_append_of_le_length (by rw [encodeFin_length])]
    rw [List.take_of_length_le (by rw [encodeFin_length])]
  have hdrop_l :
      tail_after_k.drop widthS = rest := by
    rw [htail_k_def, List.drop_append_of_le_length (by rw [encodeFin_length])]
    rw [List.drop_of_length_le (by rw [encodeFin_length])]
    simp
  show (match decodeFin widthS (tail_after_k.take widthS) with
        | none => none
        | some l_fin =>
          some (SLGate.orGate kfin.val l_fin.val, tail_after_k.drop widthS)) =
      some (SLGate.orGate k l, rest)
  rw [htake_l, hdrop_l, decodeFin_encodeFin]

/-- Combined round-trip for a single gate under well-formedness. -/
theorem SLGate.decode_encode {n : Nat} (widthN widthS : Nat)
    (h_pos : 0 < n) (h_widthN : n ≤ 2 ^ widthN)
    (g : SLGate n) (hwf : g.wellFormedUnder widthS)
    (rest : List Bool) :
    SLGate.decode widthN widthS h_pos
        (g.encode widthN widthS h_widthN ++ rest) = some (g, rest) := by
  cases g with
  | input i => exact SLGate.decode_encode_input widthN widthS h_pos h_widthN i rest
  | const b => exact SLGate.decode_encode_const widthN widthS h_pos h_widthN b rest
  | notGate k =>
    have hk : k < 2 ^ widthS := hwf
    exact SLGate.decode_encode_not widthN widthS h_pos h_widthN k hk rest
  | andGate k l =>
    obtain ⟨hk, hl⟩ := hwf
    exact SLGate.decode_encode_and widthN widthS h_pos h_widthN k l hk hl rest
  | orGate k l =>
    obtain ⟨hk, hl⟩ := hwf
    exact SLGate.decode_encode_or widthN widthS h_pos h_widthN k l hk hl rest

/-- Full round-trip for a straight-line program under program-level
well-formedness. -/
theorem SLProgram.decode_encode {n : Nat} (widthN widthS : Nat)
    (h_pos : 0 < n) (h_widthN : n ≤ 2 ^ widthN) :
    ∀ (p : SLProgram n) (_hwf : p.wellFormedUnder widthS)
      (rest : List Bool),
      SLProgram.decode widthN widthS h_pos p.gates.length
          (p.encode widthN widthS h_widthN ++ rest) = some (p, rest) := by
  intro p
  rcases p with ⟨gates⟩
  induction gates with
  | nil =>
    intro _ rest
    simp [SLProgram.encode, SLProgram.decode]
  | cons g gs ih =>
    intro hwf rest
    have hg_wf : g.wellFormedUnder widthS := hwf g (by simp)
    have hgs_wf : (⟨gs⟩ : SLProgram n).wellFormedUnder widthS := by
      intro g' hg'
      exact hwf g' (by simp [hg'])
    have ih' := ih hgs_wf rest
    -- encode (g :: gs) ++ rest = encode g ++ encode gs ++ rest
    -- Unfold the concrete encode/decode forms into their step shapes.
    have hencode :
        (⟨g :: gs⟩ : SLProgram n).encode widthN widthS h_widthN =
          SLGate.encode widthN widthS h_widthN g ++
            (⟨gs⟩ : SLProgram n).encode widthN widthS h_widthN := by
      simp [SLProgram.encode]
    rw [show ((⟨g :: gs⟩ : SLProgram n).gates.length = gs.length + 1) from rfl,
        hencode, List.append_assoc]
    show (match SLGate.decode widthN widthS h_pos
              (SLGate.encode widthN widthS h_widthN g ++
                ((⟨gs⟩ : SLProgram n).encode widthN widthS h_widthN ++ rest)) with
          | none => none
          | some (g', rest') =>
            match SLProgram.decode widthN widthS h_pos gs.length rest' with
            | none => none
            | some (⟨gs'⟩, rest'') =>
              some ((⟨g' :: gs'⟩ : SLProgram n), rest'')) =
        some ((⟨g :: gs⟩ : SLProgram n), rest)
    rw [SLGate.decode_encode widthN widthS h_pos h_widthN g hg_wf]
    show (match SLProgram.decode widthN widthS h_pos gs.length
              ((⟨gs⟩ : SLProgram n).encode widthN widthS h_widthN ++ rest) with
          | none => none
          | some (⟨gs'⟩, rest'') =>
            some ((⟨g :: gs'⟩ : SLProgram n), rest'')) =
        some ((⟨g :: gs⟩ : SLProgram n), rest)
    rw [ih']

/-!
## Session 9e-a: Evaluator tape layout

The MCSP evaluator TM needs a canonical tape arrangement with three
disjoint regions: input vector, encoded SL program, scratch (for
gate values).  `TapeLayout n` packages the offsets + length +
ordering invariants so downstream session-9e infrastructure can
work with symbolic addresses rather than raw tape arithmetic.

Three regions (canonical ordering):
* **Input** — positions `[0, n)`: bits of `x : Fin n → Bool`.
* **Circuit** — positions `[circuitStart, circuitStart + circuitLen)`:
  encoded SL program.
* **Scratch** — positions `[scratchStart, scratchStart + scratchLen)`:
  gate values computed so far (one bit per gate).

All regions are disjoint; the layout invariants `h_inputEnd`,
`h_circuitEnd`, and `h_scratchEnd` enforce the ordering + fit.
-/

/-- Tape-layout descriptor for the evaluator TM with `n` input bits. -/
structure TapeLayout (n : Nat) where
  /-- Total tape length (must be at least the right edge of scratch). -/
  tapeLen : Nat
  /-- First position of the circuit-encoding region. -/
  circuitStart : Nat
  /-- Length of the circuit-encoding region. -/
  circuitLen : Nat
  /-- First position of the scratch (gate-values) region. -/
  scratchStart : Nat
  /-- Length of the scratch region. -/
  scratchLen : Nat
  /-- Input sits before circuit. -/
  h_inputEnd : n ≤ circuitStart
  /-- Circuit sits before scratch. -/
  h_circuitEnd : circuitStart + circuitLen ≤ scratchStart
  /-- Scratch fits within the tape. -/
  h_scratchEnd : scratchStart + scratchLen ≤ tapeLen

namespace TapeLayout

variable {n : Nat}

/-- Right edge of input region. -/
@[simp] def inputEnd (_ : TapeLayout n) : Nat := n

/-- Right edge of circuit region. -/
def circuitEnd (L : TapeLayout n) : Nat := L.circuitStart + L.circuitLen

/-- Right edge of scratch region. -/
def scratchEnd (L : TapeLayout n) : Nat := L.scratchStart + L.scratchLen

/-- Predicate: tape position `p` lies in the input region. -/
def inInput (_ : TapeLayout n) (p : Nat) : Prop := p < n

/-- Predicate: tape position `p` lies in the circuit region. -/
def inCircuit (L : TapeLayout n) (p : Nat) : Prop :=
  L.circuitStart ≤ p ∧ p < L.circuitEnd

/-- Predicate: tape position `p` lies in the scratch region. -/
def inScratch (L : TapeLayout n) (p : Nat) : Prop :=
  L.scratchStart ≤ p ∧ p < L.scratchEnd

/-- Position of input bit `i`. -/
def inputPos (_ : TapeLayout n) (i : Fin n) : Nat := i.val

/-- Position of circuit-encoding bit `p`. -/
def circuitPos (L : TapeLayout n) (p : Nat) : Nat := L.circuitStart + p

/-- Position of scratch (gate value) cell `k`. -/
def scratchPos (L : TapeLayout n) (k : Nat) : Nat := L.scratchStart + k

/-! ### Region containment -/

theorem inputPos_inInput (L : TapeLayout n) (i : Fin n) :
    L.inInput (L.inputPos i) := i.isLt

theorem circuitPos_inCircuit (L : TapeLayout n) (p : Nat)
    (hp : p < L.circuitLen) : L.inCircuit (L.circuitPos p) := by
  refine ⟨?_, ?_⟩
  · show L.circuitStart ≤ L.circuitStart + p; omega
  · show L.circuitStart + p < L.circuitEnd
    unfold circuitEnd; omega

theorem scratchPos_inScratch (L : TapeLayout n) (k : Nat)
    (hk : k < L.scratchLen) : L.inScratch (L.scratchPos k) := by
  refine ⟨?_, ?_⟩
  · show L.scratchStart ≤ L.scratchStart + k; omega
  · show L.scratchStart + k < L.scratchEnd
    unfold scratchEnd; omega

/-! ### Pairwise disjointness -/

theorem inInput_not_inCircuit (L : TapeLayout n) {p : Nat}
    (h : L.inInput p) : ¬ L.inCircuit p := by
  intro hC
  have h₁ : p < n := h
  have h₂ : n ≤ L.circuitStart := L.h_inputEnd
  have h₃ : L.circuitStart ≤ p := hC.1
  omega

theorem inCircuit_not_inScratch (L : TapeLayout n) {p : Nat}
    (h : L.inCircuit p) : ¬ L.inScratch p := by
  intro hS
  have h₁ : p < L.circuitEnd := h.2
  have h₂ : L.circuitEnd ≤ L.scratchStart := by
    unfold circuitEnd; exact L.h_circuitEnd
  have h₃ : L.scratchStart ≤ p := hS.1
  omega

theorem inInput_not_inScratch (L : TapeLayout n) {p : Nat}
    (h : L.inInput p) : ¬ L.inScratch p := by
  intro hS
  have h₁ : p < n := h
  have h₂ : n ≤ L.circuitStart := L.h_inputEnd
  have h₃ : L.circuitStart + L.circuitLen ≤ L.scratchStart := L.h_circuitEnd
  have h₄ : L.scratchStart ≤ p := hS.1
  omega

/-! ### Bounds: positions fit within `tapeLen` -/

theorem inputPos_lt_tapeLen (L : TapeLayout n) (i : Fin n) :
    L.inputPos i < L.tapeLen := by
  have h₁ : i.val < n := i.isLt
  have h₂ : n ≤ L.circuitStart := L.h_inputEnd
  have h₃ : L.circuitStart + L.circuitLen ≤ L.scratchStart := L.h_circuitEnd
  have h₄ : L.scratchStart + L.scratchLen ≤ L.tapeLen := L.h_scratchEnd
  show i.val < L.tapeLen
  omega

theorem circuitPos_lt_tapeLen (L : TapeLayout n) (p : Nat)
    (hp : p < L.circuitLen) : L.circuitPos p < L.tapeLen := by
  have h₁ : L.circuitStart + L.circuitLen ≤ L.scratchStart := L.h_circuitEnd
  have h₂ : L.scratchStart + L.scratchLen ≤ L.tapeLen := L.h_scratchEnd
  show L.circuitStart + p < L.tapeLen
  omega

theorem scratchPos_lt_tapeLen (L : TapeLayout n) (k : Nat)
    (hk : k < L.scratchLen) : L.scratchPos k < L.tapeLen := by
  have h₁ : L.scratchStart + L.scratchLen ≤ L.tapeLen := L.h_scratchEnd
  show L.scratchStart + k < L.tapeLen
  omega

end TapeLayout

/-!
## Session 9e-b: `TapeMatches` — tape content ↔ logical view

The evaluator TM's correctness will be stated relative to a
`TapeMatches` predicate: "the tape of this configuration correctly
encodes the input vector `x`, the SL program encoding, and the
first `k` gate values".

Reasoning about the evaluator reduces to: show `TapeMatches`
holds initially; show each gate-step preserves the
`TapeMatches` invariant while extending `gateVals` by one bit;
conclude the final scratch cell matches `SLProgram.eval`.
-/

end Encoding

/-- Read a tape cell by absolute position; returns `false` outside
the tape bounds.  Helper for stating `TapeMatches` cleanly. -/
def Configuration.tapeAt {M : TM.{0}} {n_tm : Nat}
    (c : Configuration (M := M) n_tm) (p : Nat) : Bool :=
  if h : p < M.tapeLength n_tm then c.tape ⟨p, h⟩ else false

namespace Encoding

/-- The tape correctly encodes: the input vector `x`, the circuit
encoding bits, and the list of gate values computed so far. -/
structure TapeMatches {M : TM.{0}} {n_tm : Nat} {n : Nat}
    (L : TapeLayout n)
    (c : Configuration (M := M) n_tm)
    (x : Fin n → Bool)
    (encoding : List Bool)
    (gateVals : List Bool) : Prop where
  /-- The layout's tape length fits inside the TM's. -/
  tape_fits : L.tapeLen ≤ M.tapeLength n_tm
  /-- Encoding fits in the circuit region. -/
  encoding_fits : encoding.length ≤ L.circuitLen
  /-- Gate values fit in the scratch region. -/
  gateVals_fits : gateVals.length ≤ L.scratchLen
  /-- Input bits are correctly placed. -/
  input_match : ∀ i : Fin n,
    c.tapeAt (L.inputPos i) = x i
  /-- Circuit-encoding bits are correctly placed. -/
  circuit_match : ∀ p : Nat, (hp : p < encoding.length) →
    c.tapeAt (L.circuitPos p) = encoding[p]
  /-- Gate-value bits are correctly placed. -/
  scratch_match : ∀ k : Nat, (hk : k < gateVals.length) →
    c.tapeAt (L.scratchPos k) = gateVals[k]

namespace TapeMatches

variable {M : TM.{0}} {n_tm n : Nat} {L : TapeLayout n}
  {c : Configuration (M := M) n_tm}
  {x : Fin n → Bool} {encoding gateVals : List Bool}

/-- Empty gate-values case: `TapeMatches` is discharged with just the
input and circuit commitments. -/
theorem of_empty_gateVals
    (hFit : L.tapeLen ≤ M.tapeLength n_tm)
    (hEnc : encoding.length ≤ L.circuitLen)
    (hIn : ∀ i : Fin n, c.tapeAt (L.inputPos i) = x i)
    (hC : ∀ p : Nat, (hp : p < encoding.length) →
      c.tapeAt (L.circuitPos p) = encoding[p]) :
    TapeMatches L c x encoding [] where
  tape_fits := hFit
  encoding_fits := hEnc
  gateVals_fits := Nat.zero_le _
  input_match := hIn
  circuit_match := hC
  scratch_match := fun k hk => absurd hk (by simp)

/-- Transfer `TapeMatches` from one configuration to another that
agrees on every relevant cell. -/
theorem of_tape_eq
    {c' : Configuration (M := M) n_tm}
    (h : TapeMatches L c x encoding gateVals)
    (hInput : ∀ i : Fin n, c'.tapeAt (L.inputPos i) = c.tapeAt (L.inputPos i))
    (hCircuit : ∀ p : Nat, p < encoding.length →
      c'.tapeAt (L.circuitPos p) = c.tapeAt (L.circuitPos p))
    (hScratch : ∀ k : Nat, k < gateVals.length →
      c'.tapeAt (L.scratchPos k) = c.tapeAt (L.scratchPos k)) :
    TapeMatches L c' x encoding gateVals where
  tape_fits := h.tape_fits
  encoding_fits := h.encoding_fits
  gateVals_fits := h.gateVals_fits
  input_match := fun i => by
    rw [hInput i]; exact h.input_match i
  circuit_match := fun p hp => by
    rw [hCircuit p hp]; exact h.circuit_match p hp
  scratch_match := fun k hk => by
    rw [hScratch k hk]; exact h.scratch_match k hk

/-- Extension: if the current config agrees with the old one on
input/circuit and on the first `|gateVals|` scratch cells, AND
writes value `v` at the *next* scratch position, then
`TapeMatches` extends to `gateVals ++ [v]`. -/
theorem extend_scratch
    {c' : Configuration (M := M) n_tm} (v : Bool)
    (h : TapeMatches L c x encoding gateVals)
    (hInput : ∀ i : Fin n, c'.tapeAt (L.inputPos i) = c.tapeAt (L.inputPos i))
    (hCircuit : ∀ p : Nat, p < encoding.length →
      c'.tapeAt (L.circuitPos p) = c.tapeAt (L.circuitPos p))
    (hScratch : ∀ k : Nat, k < gateVals.length →
      c'.tapeAt (L.scratchPos k) = c.tapeAt (L.scratchPos k))
    (hNew : c'.tapeAt (L.scratchPos gateVals.length) = v)
    (hSpace : gateVals.length < L.scratchLen) :
    TapeMatches L c' x encoding (gateVals ++ [v]) where
  tape_fits := h.tape_fits
  encoding_fits := h.encoding_fits
  gateVals_fits := by
    have := h.gateVals_fits
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  input_match := fun i => by rw [hInput i]; exact h.input_match i
  circuit_match := fun p hp => by
    rw [hCircuit p hp]; exact h.circuit_match p hp
  scratch_match := fun k hk => by
    simp only [List.length_append, List.length_cons, List.length_nil] at hk
    rcases Nat.lt_or_ge k gateVals.length with hk_old | hk_new
    · rw [hScratch k hk_old]
      have := h.scratch_match k hk_old
      rw [List.getElem_append_left hk_old]
      exact this
    · have hk_eq : k = gateVals.length := by omega
      subst hk_eq
      rw [hNew]
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp

/-- If the scratch cells up to `gateVals.length - 1` are committed
by `TapeMatches`, the tape at the last scratch position equals the
last `gateVals` element (assuming nonempty). -/
theorem output_matches
    (h : TapeMatches L c x encoding gateVals)
    (hNonEmpty : 0 < gateVals.length) :
    c.tapeAt (L.scratchPos (gateVals.length - 1)) =
      gateVals[gateVals.length - 1]'(by omega) :=
  h.scratch_match (gateVals.length - 1) (by omega)

end TapeMatches

/-!
### Bridge: `SLProgram.eval` → `evalAll`'s last element
-/

/-- `SLProgram.eval` matches the last element of `evalAll`'s result
when evaluation succeeds on a non-empty gate list.  Uses Mathlib's
`List.getLast?_eq_getLast_of_ne_nil` + `List.getLast_eq_getElem`. -/
theorem SLProgram.eval_eq_last_evalAll {n : Nat} (p : SLProgram n)
    (x : Fin n → Bool) (gateVals : List Bool)
    (hEval : p.evalAll x = some gateVals)
    (hNE : 0 < gateVals.length) :
    p.eval x = some (gateVals[gateVals.length - 1]'(by omega)) := by
  unfold SLProgram.eval
  rw [hEval]
  simp only [Option.bind_some]
  have hNil : gateVals ≠ [] := by
    intro h; rw [h] at hNE; simp at hNE
  rw [List.getLast?_eq_getLast_of_ne_nil hNil]
  congr 1
  exact List.getLast_eq_getElem hNil

end Encoding

/-!
## Session 9e-d: `seekRightProgram` primitive

`seekRightProgram Δ` is a `PhasedProgram` that moves the tape head
right by exactly `Δ` cells, leaving the tape contents unchanged.
It has `Δ + 1` phases: phase `i < Δ` emits `Move.right` and writes
the scanned bit back unchanged; phase `Δ` is the accepting idle
phase.

This is the most basic TM-evaluator building block: before reading
any specific cell, the evaluator needs to position the head.  With
composable seek + read primitives, the full evaluator assembles
as a chain of such phases.

Correctness: starting in phase 0 with the head at position `h`,
after `Δ` steps the head is at position `h + Δ` (assuming tape
width allows) and the tape is unchanged.
-/


end TM

end PsubsetPpoly
end Internal
end Pnp3
