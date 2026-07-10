import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.CanonicalCutOffsets

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Faithful padding of the canonical alpha data

The concrete crossing extractor returns a variable-length list, of length at
most `K = T / b`.  This file embeds that list into a fixed-length word without
silently choosing a default crossing: occupied prefix slots contain `some`
tokens and the remaining slots contain `none`.  Decoding stops at the first
empty slot, and exactly recovers every list whose length is at most `K`.

A token keeps the selected full-bucket identity and the crossing payload.  It
does not repeat the physical cut, because the cut is reconstructed from that
bucket and the separately retained canonical offset vector.  The resulting
offsets-plus-padded-word type is an injective finite ambient encoding of the
data extracted from one run.  It is not a local-validity predicate, a
branching program, a count of reachable transcripts, or a compression
theorem.
-/

/-- A crossing token retains its full-bucket identity and machine payload.
The corresponding physical cut is recovered from the offset vector. -/
abbrev CanonicalCrossingToken (State : Type) (T b : Nat) :=
  Fin (T / b) × CrossingRecordPayload State T

/-- A fixed-length word with an explicit empty marker. -/
abbrev PaddedCanonicalCrossingWord (State : Type) (T b : Nat) :=
  Fin (T / b) → Option (CanonicalCrossingToken State T b)

/-- Prefix-pad a list into exactly `K` optional slots.  No default element of
`Token` is used: a short list is followed by `none`. -/
def encodePaddedWord {Token : Type} :
    (K : Nat) → List Token → Fin K → Option Token
  | 0, _, i => Fin.elim0 i
  | _ + 1, [], _ => none
  | K + 1, token :: tokens, i =>
      Fin.cases (some token) (encodePaddedWord K tokens) i

/-- Decode the occupied prefix of a padded word, stopping at its first empty
slot.  Words with a later occupied slot after a `none` are legal ambient words,
but those later slots are deliberately outside this prefix decoder. -/
def decodePaddedWord {Token : Type} :
    (K : Nat) → (Fin K → Option Token) → List Token
  | 0, _ => []
  | K + 1, word =>
      match word 0 with
      | none => []
      | some token =>
          token :: decodePaddedWord K (fun i => word i.succ)

/-- Prefix padding faithfully recovers every list that fits in `K` slots. -/
theorem decode_encodePaddedWord {Token : Type} (K : Nat)
    (tokens : List Token) (hLength : tokens.length ≤ K) :
    decodePaddedWord K (encodePaddedWord K tokens) = tokens := by
  induction K generalizing tokens with
  | zero =>
      have hEmpty : tokens = [] :=
        List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hLength)
      subst tokens
      rfl
  | succ K ih =>
      cases tokens with
      | nil => rfl
      | cons token tokens =>
          have hTail : tokens.length ≤ K := by
            simpa using hLength
          simp [encodePaddedWord, decodePaddedWord, ih tokens hTail]

/-- In particular, prefix padding is injective on lists of length at most
`K`; different admissible variable-length transcripts cannot collide. -/
theorem encodePaddedWord_injective_of_length_le {Token : Type} (K : Nat)
    {left right : List Token}
    (hLeft : left.length ≤ K) (hRight : right.length ≤ K)
    (hEncoded : encodePaddedWord K left = encodePaddedWord K right) :
    left = right := by
  rw [← decode_encodePaddedWord K left hLeft,
    ← decode_encodePaddedWord K right hRight, hEncoded]

/-- Forget the physical-cut field after retaining exactly the information
needed to reconstruct it from the canonical offsets. -/
def canonicalCrossingTokenOfRecord {State : Type} {T b : Nat}
    (record : CanonicalCrossingRecord State T b) :
    CanonicalCrossingToken State T b :=
  (record.selectedCut, record.payload)

/-- The token list extracted from all actual selected-cut crossings. -/
noncomputable def canonicalCrossingTokens
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    List (CanonicalCrossingToken machine.State T b) :=
  (canonicalCrossingRecords machine input T b hb).map
    canonicalCrossingTokenOfRecord

@[simp]
theorem length_canonicalCrossingTokens
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    (canonicalCrossingTokens machine input T b hb).length =
      (canonicalCrossingRecords machine input T b hb).length := by
  simp [canonicalCrossingTokens]

/-- The actual token list fits into exactly `K = T / b` padding slots. -/
theorem length_canonicalCrossingTokens_le_div
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    (canonicalCrossingTokens machine input T b hb).length ≤ T / b := by
  rw [length_canonicalCrossingTokens]
  exact length_canonicalCrossingRecords_le_div machine input T b hb

/-- Recover the physical cut named by a token from the retained offset
vector. -/
def physicalCutOfCanonicalToken {State : Type} {T b : Nat}
    (offsets : CanonicalCutOffsets T b)
    (token : CanonicalCrossingToken State T b) : Fin T :=
  fullBucketBoundary token.1 (offsets token.1)

/-- For every concrete crossing occurrence, dropping its physical-cut field
to a token loses no information once the concrete canonical offsets are kept. -/
theorem canonicalCrossingRecord_physicalCut_recovered
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (occurrence : CanonicalCrossingOccurrence machine input T b hb) :
    (canonicalCrossingRecordOfOccurrence machine input T b hb occurrence).physicalCut =
      physicalCutOfCanonicalToken
        (canonicalCutOffsets machine input T b hb)
        (canonicalCrossingTokenOfRecord
          (canonicalCrossingRecordOfOccurrence machine input T b hb occurrence)) := by
  rw [canonicalCrossingRecordOfOccurrence_physicalCut]
  rfl

/-- Every record in the concrete extracted list has its physical cut recovered
from its token and the canonical offset vector. -/
theorem mem_canonicalCrossingRecords_physicalCut_recovered
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b)
    (record : CanonicalCrossingRecord machine.State T b)
    (hRecord : record ∈ canonicalCrossingRecords machine input T b hb) :
    record.physicalCut =
      physicalCutOfCanonicalToken
        (canonicalCutOffsets machine input T b hb)
        (canonicalCrossingTokenOfRecord record) := by
  rw [canonicalCrossingRecords] at hRecord
  rcases List.mem_map.mp hRecord with ⟨occurrence, _, rfl⟩
  exact canonicalCrossingRecord_physicalCut_recovered
    machine input T b hb occurrence

/-- The complete fixed-size ambient alpha carrier: canonical offsets together
with a padded word of bucket-labelled crossing payloads. -/
structure PaddedCanonicalAlpha (State : Type) (T b : Nat) where
  offsets : CanonicalCutOffsets T b
  word : PaddedCanonicalCrossingWord State T b
deriving Fintype

/-- Embed the actual canonical data of one run into the padded ambient carrier. -/
noncomputable def canonicalPaddedAlpha
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    PaddedCanonicalAlpha machine.State T b :=
  { offsets := canonicalCutOffsets machine input T b hb
    word := encodePaddedWord (T / b)
      (canonicalCrossingTokens machine input T b hb) }

/-- Decoding the word component of the concrete padded alpha returns exactly
the variable-length actual token list. -/
theorem decode_canonicalPaddedAlpha_word
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    decodePaddedWord (T / b)
        (canonicalPaddedAlpha machine input T b hb).word =
      canonicalCrossingTokens machine input T b hb := by
  exact decode_encodePaddedWord (T / b)
    (canonicalCrossingTokens machine input T b hb)
    (length_canonicalCrossingTokens_le_div machine input T b hb)

/-- Exact size of the bucket-labelled token alphabet. -/
theorem card_canonicalCrossingToken
    (State : Type) [Fintype State] (T b : Nat) :
    Fintype.card (CanonicalCrossingToken State T b) =
      (T / b) * (2 * Fintype.card State * (T + 1)) := by
  rw [Fintype.card_prod, Fintype.card_fin,
    card_crossingRecordPayload]

/-- Exact size of the full optional-token word carrier.  This counts all
words, including non-prefix-shaped and locally inconsistent ones. -/
theorem card_paddedCanonicalCrossingWord
    (State : Type) [Fintype State] (T b : Nat) :
    Fintype.card (PaddedCanonicalCrossingWord State T b) =
      (1 + (T / b) * (2 * Fintype.card State * (T + 1))) ^ (T / b) := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_option,
    card_canonicalCrossingToken]
  congr 1
  omega

/-- The padded alpha carrier is the product of its offset vector and optional
token word. -/
def paddedCanonicalAlphaEquiv (State : Type) (T b : Nat) :
    PaddedCanonicalAlpha State T b ≃
      CanonicalCutOffsets T b × PaddedCanonicalCrossingWord State T b where
  toFun alpha := (alpha.offsets, alpha.word)
  invFun fields := { offsets := fields.1, word := fields.2 }
  left_inv alpha := by cases alpha; rfl
  right_inv fields := by rcases fields with ⟨offsets, word⟩; rfl

/-- Exact full ambient count
`b^K * (1 + K * (2 * |State| * (T + 1)))^K`, where `K = T / b`.

This is the size of an injective finite ambient encoding carrier.  It does not
assert local validity, reachable-transcript semantics, or a branching-program
simulation. -/
theorem card_paddedCanonicalAlpha
    (State : Type) [Fintype State] (T b : Nat) :
    Fintype.card (PaddedCanonicalAlpha State T b) =
      b ^ (T / b) *
        (1 + (T / b) * (2 * Fintype.card State * (T + 1))) ^ (T / b) := by
  rw [Fintype.card_congr (paddedCanonicalAlphaEquiv State T b),
    Fintype.card_prod, card_canonicalCutOffsets,
    card_paddedCanonicalCrossingWord]

end OneTapeMagnification
end Frontier
end Pnp4
