import Pnp4.Frontier.ContractExpansion.TreeMCSPGateRecordLayout

/-!
# On-tape gate-record **stream** layout (NP-verifier track — decoder brick D2, spec foundation)

D1b's `gateOneRecordDecoder` reads exactly one gate record (`TM_VERIFIER_STRATEGY.md` §6k); D2 iterates
it across the witness region.  This file fixes the **stream spec** the eventual on-tape stream decoder
must match: a circuit is a contiguous concatenation of `encodeGateRecord` records, decoded by reading
exactly `gateCount` records in sequence.

Scope (D2 spec foundation): the stream encoder/decoder on `List (SLGate n)` plus their round-trip and
size lemmas — the D0-analogue lifted from one record to a record stream.  **Not** here, and explicitly
the hard remaining parts of D2:
* the on-tape stream-decoder TM (a *head-advancing* loop over D1b — `repeatBody` as built keeps the head
  fixed, so a new combinator is needed);
* the gate-count field that says how many records to read;
* the §9 reconciliation with `treeCircuitWitnessCodec` (the toolkit's `CircuitTree` binary layout, a
  *different* byte layout from this unary-record stream) — the hardest single brick.

**Progress classification (AGENTS.md): Infrastructure** — toolkit toward the NP-membership leg of
`VerifiedNPDAGLowerBoundSource`; it does not itself reduce a source obligation and is **not** reportable
as `P ≠ NP` mainline progress.
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open Pnp3.Internal.PsubsetPpoly.TM.Encoding

/-- Encode a list of gates as a contiguous stream of `encodeGateRecord` records. -/
def encodeGateRecordStream {n : Nat} : List (SLGate n) → List Bool
  | [] => []
  | g :: gs => encodeGateRecord g ++ encodeGateRecordStream gs

/-- Decode `count` consecutive gate records off the front of a bit stream, returning the gates and the
remaining bits.  Fails (`none`) as soon as any record is malformed (the route the verifier sends to its
reject sink). -/
def decodeGateRecordStream (n : Nat) : Nat → List Bool → Option (List (SLGate n) × List Bool)
  | 0, bs => some ([], bs)
  | (k + 1), bs =>
    match decodeGateRecord n bs with
    | none => none
    | some (g, rest) =>
      match decodeGateRecordStream n k rest with
      | none => none
      | some (gs, rest') => some (g :: gs, rest')

@[simp] theorem decodeGateRecordStream_zero (n : Nat) (bs : List Bool) :
    decodeGateRecordStream n 0 bs = some ([], bs) := rfl

/-- **Stream round-trip**: decoding `gs.length` records off `encodeGateRecordStream gs ++ rest` recovers
`gs` exactly and leaves the suffix untouched.  Lifts D0's one-record round-trip
(`decodeGateRecord_encodeGateRecord`) to the whole stream by induction on the gate list. -/
theorem decodeGateRecordStream_encodeGateRecordStream {n : Nat} (gs : List (SLGate n))
    (rest : List Bool) :
    decodeGateRecordStream n gs.length (encodeGateRecordStream gs ++ rest) = some (gs, rest) := by
  induction gs generalizing rest with
  | nil => simp [encodeGateRecordStream]
  | cons g gs ih =>
      simp only [encodeGateRecordStream, List.length_cons, List.append_assoc, decodeGateRecordStream,
        decodeGateRecord_encodeGateRecord, ih]

/-! ### Stream size (for the polynomial layout budget) -/

/-- Exact length of an encoded gate-record stream: the sum of the per-record sizes. -/
@[simp] theorem encodeGateRecordStream_length {n : Nat} (gs : List (SLGate n)) :
    (encodeGateRecordStream gs).length = (gs.map gateRecordSize).sum := by
  induction gs with
  | nil => simp [encodeGateRecordStream]
  | cons g gs ih =>
      simp only [encodeGateRecordStream, List.map_cons, List.sum_cons, List.length_append,
        encodeGateRecord_length, ih]

/-! ### Bridge to the circuit codec: a flattened circuit's record stream is faithful

Connecting the stream layout to the **real** circuit semantics via the toolkit's verified
`CircuitTree.flatten` (`Encoding.lean`): flatten a circuit tree to a straight-line gate list, encode
that list as a record stream, decode it back — the recovered gate list **computes the circuit's
function** (`CircuitTree.flatten_eval`).  This is the spec-level faithfulness the D2 on-tape transcoder
must realise (the §9 witness→records step: the witness is a recursive `CircuitTree`; flattening +
re-encoding as unary records is the interpreter's internal format). -/

/-- Decoding the record stream of a flattened circuit recovers exactly the flattened gate list
(`c.size` records). -/
theorem decodeGateRecordStream_flatten {n : Nat} (c : CircuitTree n) (rest : List Bool) :
    decodeGateRecordStream n c.size
        (encodeGateRecordStream (CircuitTree.flatten c).gates ++ rest)
      = some ((CircuitTree.flatten c).gates, rest) := by
  have h := decodeGateRecordStream_encodeGateRecordStream (CircuitTree.flatten c).gates rest
  rwa [CircuitTree.flatten_length] at h

/-- **Faithfulness**: the gate list recovered from a flattened circuit's record stream evaluates (as a
straight-line program) to the circuit's value — tying the D2 stream layout to `evalCircuitTree` through
the toolkit's verified flattening (`CircuitTree.flatten_eval`). -/
theorem decodeGateRecordStream_flatten_eval {n : Nat} (c : CircuitTree n) (x : Fin n → Bool)
    (rest : List Bool) :
    ∃ gates : List (SLGate n),
      decodeGateRecordStream n c.size
          (encodeGateRecordStream (CircuitTree.flatten c).gates ++ rest) = some (gates, rest)
      ∧ SLProgram.eval ⟨gates⟩ x = some (evalCircuitTree c x) := by
  refine ⟨(CircuitTree.flatten c).gates, decodeGateRecordStream_flatten c rest, ?_⟩
  exact CircuitTree.flatten_eval c x

/-! ### Self-delimiting stream: a unary gate-count prefix

The on-tape stream decoder must learn *how many* records to read; prefixing the record stream with the
gate count as a unary field `1^count 0` makes the stream self-delimiting (the count is read first, by
the same `decodeUnaryField`/`selfLoopScanRightOne` the records use).  This is the D2 gate-count field. -/

/-- A self-delimiting gate stream: the gate count as a unary prefix, then the record stream. -/
def encodeGateStream {n : Nat} (gs : List (SLGate n)) : List Bool :=
  unaryField gs.length ++ encodeGateRecordStream gs

/-- Decode a self-delimiting gate stream: read the unary gate-count prefix, then that many records. -/
def decodeGateStream (n : Nat) (bs : List Bool) : Option (List (SLGate n) × List Bool) :=
  match decodeUnaryField bs with
  | none => none
  | some (count, rest) => decodeGateRecordStream n count rest

/-- **Self-delimiting round-trip**: a count-prefixed gate stream decodes back to the gate list, leaving
the suffix untouched (no external count needed — it is read from the prefix). -/
theorem decodeGateStream_encodeGateStream {n : Nat} (gs : List (SLGate n)) (rest : List Bool) :
    decodeGateStream n (encodeGateStream gs ++ rest) = some (gs, rest) := by
  simp only [decodeGateStream, encodeGateStream, List.append_assoc, decodeUnaryField_unaryField,
    decodeGateRecordStream_encodeGateRecordStream]

/-- The self-delimiting stream of a flattened circuit decodes back to the flattened gate list — the
gate count is recovered from the prefix as `c.size`. -/
theorem decodeGateStream_flatten {n : Nat} (c : CircuitTree n) (rest : List Bool) :
    decodeGateStream n (encodeGateStream (CircuitTree.flatten c).gates ++ rest)
      = some ((CircuitTree.flatten c).gates, rest) :=
  decodeGateStream_encodeGateStream (CircuitTree.flatten c).gates rest

end ContractExpansion
end Frontier
end Pnp4
