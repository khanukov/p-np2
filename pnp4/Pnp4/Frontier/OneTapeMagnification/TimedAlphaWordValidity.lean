import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.TimedCanonicalAlpha

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Syntactic validity of the padded timed-alpha word

The ambient timed-alpha carrier deliberately admits garbage after the first
`none`, repeated or decreasing source times, and other unreachable words.
Before block visits can be derived from a fixed alpha, those purely syntactic
ambiguities must be rejected.

This file defines an exact prefix-shape check and a strict chronological-time
check.  Prefix shape means that re-encoding the decoded prefix reproduces the
entire fixed word, so an occupied slot after the first `none` is rejected.
The extracted alpha of every concrete run passes both checks.

These predicates do not yet check crossing directions, endpoint chaining,
terminal consistency, local replay, or leftmost-minimum cut selection.
-/

/-- Decoding a `K`-slot word can never produce more than `K` tokens, even for
an arbitrary non-prefix-shaped ambient word. -/
theorem length_decodePaddedWord_le {Token : Type} (K : Nat)
    (word : Fin K → Option Token) :
    (decodePaddedWord K word).length ≤ K := by
  induction K with
  | zero => rfl
  | succ K ih =>
      simp only [decodePaddedWord]
      split
      · simp
      · simp only [List.length_cons, Nat.succ_le_succ_iff]
        exact ih _

/-- The occupied prefix is the whole padded word: after the first `none`, all
remaining slots must also be `none`. -/
def TimedAlphaWordPrefixShaped
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b) : Prop :=
  alpha.word = encodePaddedWord (T / b)
    (decodePaddedWord (T / b) alpha.word)

/-- The decoded crossing source times are strictly increasing. -/
def TimedAlphaWordTimesStrict
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b) : Prop :=
  ((decodePaddedWord (T / b) alpha.word).map
    TimedCanonicalCrossingToken.sourceTime).Pairwise
      (fun earlier later => earlier < later)

/-- Purely syntactic timed-word validity.  This is intentionally narrower
than full crossing/slab validity. -/
def TimedAlphaWordSyntacticallyValid
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b) : Prop :=
  TimedAlphaWordPrefixShaped alpha ∧ TimedAlphaWordTimesStrict alpha

/-- Executable check for the syntactic timed-word predicate.  Equality on the
finite control-state type is an explicit input to the checker. -/
def timedAlphaWordSyntacticCheck
    {State : Type} [DecidableEq State] {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b) : Bool :=
  decide (alpha.word = encodePaddedWord (T / b)
      (decodePaddedWord (T / b) alpha.word)) &&
    decide (((decodePaddedWord (T / b) alpha.word).map
      TimedCanonicalCrossingToken.sourceTime).Pairwise
        (fun earlier later => earlier < later))

theorem timedAlphaWordSyntacticCheck_eq_true_iff
    {State : Type} [DecidableEq State] {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b) :
    timedAlphaWordSyntacticCheck alpha = true ↔
      TimedAlphaWordSyntacticallyValid alpha := by
  simp [timedAlphaWordSyntacticCheck,
    TimedAlphaWordSyntacticallyValid,
    TimedAlphaWordPrefixShaped, TimedAlphaWordTimesStrict]

/-- Prefix-shaped words are uniquely determined by their decoded token list. -/
theorem timedAlphaWord_eq_of_prefixShaped_of_decode_eq
    {State : Type} {T b : Nat}
    {left right : AmbientTimedCanonicalAlpha State T b}
    (hleft : TimedAlphaWordPrefixShaped left)
    (hright : TimedAlphaWordPrefixShaped right)
    (hdecode : decodePaddedWord (T / b) left.word =
      decodePaddedWord (T / b) right.word) :
    left.word = right.word := by
  rw [hleft, hright, hdecode]

/-- The concrete extracted timed word is exactly prefix-shaped. -/
theorem chronologicalTimedCanonicalAlpha_word_prefixShaped
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    TimedAlphaWordPrefixShaped
      (chronologicalTimedCanonicalAlpha machine input T b hb) := by
  unfold TimedAlphaWordPrefixShaped
  rw [decode_chronologicalTimedCanonicalAlpha_word]
  rfl

/-- The concrete extracted timed word has strictly increasing source times. -/
theorem chronologicalTimedCanonicalAlpha_word_timesStrict
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    TimedAlphaWordTimesStrict
      (chronologicalTimedCanonicalAlpha machine input T b hb) := by
  unfold TimedAlphaWordTimesStrict
  rw [decode_chronologicalTimedCanonicalAlpha_word]
  exact chronologicalTimedCanonicalCrossingTokens_times_pairwise_lt
    machine input T b hb

/-- Every true extracted timed alpha passes the complete syntactic word
check. -/
theorem chronologicalTimedCanonicalAlpha_word_syntacticallyValid
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    TimedAlphaWordSyntacticallyValid
      (chronologicalTimedCanonicalAlpha machine input T b hb) := by
  exact ⟨chronologicalTimedCanonicalAlpha_word_prefixShaped
      machine input T b hb,
    chronologicalTimedCanonicalAlpha_word_timesStrict
      machine input T b hb⟩

end OneTapeMagnification
end Frontier
end Pnp4
