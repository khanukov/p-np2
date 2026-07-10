import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.ChronologicalCanonicalAlpha

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Timed canonical alpha metadata

The chronological extractor retains each selected crossing's source time, but
`chronologicalCanonicalPaddedAlpha` intentionally erases that time before
padding.  A fixed metadata value then knows the crossing order but not the
number of machine steps assigned to the intervening segments.

This file closes only that finite-metadata gap.  A timed token pairs a source
time in `Fin T` with the existing bucket-labelled crossing token.  A separate
terminal endpoint stores the final bounded control state and both head
positions.  The concrete timed list is prefix-padded into `T / b` slots and
decodes exactly.

The ambient carrier deliberately contains non-prefix-shaped words, unordered
or repeated times, inconsistent crossings, and unreachable terminal endpoints.
Its cardinality is therefore an exact carrier count, not a reachable-transcript
count.  Retaining times and a terminal endpoint pays an explicit transcript
factor.  Nothing here supplies destination-slab contents, slab glue, local
validity, a branching program, or a width bound.
-/

/-- A canonical crossing token together with the transition time at which its
crossing occurs. -/
structure TimedCanonicalCrossingToken (State : Type) (T b : Nat) where
  sourceTime : Fin T
  token : CanonicalCrossingToken State T b
deriving Fintype

/-- The timed token is exactly the displayed product. -/
def timedCanonicalCrossingTokenEquiv (State : Type) (T b : Nat) :
    TimedCanonicalCrossingToken State T b ≃
      Fin T × CanonicalCrossingToken State T b where
  toFun timed := (timed.sourceTime, timed.token)
  invFun fields := ⟨fields.1, fields.2⟩
  left_inv timed := by cases timed; rfl
  right_inv fields := by rcases fields with ⟨time, token⟩; rfl

/-- Exact size of the timed crossing-token alphabet.  The leading factor `T`
is the cost of retaining the source time. -/
theorem card_timedCanonicalCrossingToken
    (State : Type) [Fintype State] (T b : Nat) :
    Fintype.card (TimedCanonicalCrossingToken State T b) =
      T * ((T / b) * (2 * Fintype.card State * (T + 1))) := by
  rw [Fintype.card_congr
      (timedCanonicalCrossingTokenEquiv State T b),
    Fintype.card_prod, Fintype.card_fin,
    card_canonicalCrossingToken]

/-- The bounded endpoint at the fixed terminal time `T`.  The work tape is not
stored: this is endpoint metadata, not a restartable configuration interface. -/
structure BoundedTerminalEndpoint (State : Type) (T : Nat) where
  state : State
  inputHead : Fin (T + 1)
  workHead : Fin (T + 1)
deriving Fintype

/-- The terminal endpoint is exactly the product of its three finite fields. -/
def boundedTerminalEndpointEquiv (State : Type) (T : Nat) :
    BoundedTerminalEndpoint State T ≃
      State × Fin (T + 1) × Fin (T + 1) where
  toFun endpoint := (endpoint.state, endpoint.inputHead, endpoint.workHead)
  invFun fields := ⟨fields.1, fields.2.1, fields.2.2⟩
  left_inv endpoint := by cases endpoint; rfl
  right_inv fields := by
    rcases fields with ⟨state, inputHead, workHead⟩
    rfl

/-- Exact size of the full bounded terminal-endpoint carrier. -/
theorem card_boundedTerminalEndpoint
    (State : Type) [Fintype State] (T : Nat) :
    Fintype.card (BoundedTerminalEndpoint State T) =
      Fintype.card State * (T + 1) * (T + 1) := by
  rw [Fintype.card_congr (boundedTerminalEndpointEquiv State T)]
  simp [Nat.mul_assoc]

/-- Extract the exact endpoint reached after `T` transitions. -/
def boundedTerminalEndpointAtRun
    (machine : DeterministicMachine) (input : List Bool) (T : Nat) :
    BoundedTerminalEndpoint machine.State T :=
  { state := (run machine input T).state
    inputHead :=
      ⟨(run machine input T).inputHead,
        Nat.lt_succ_of_le
          (inputHead_run_le_time_for_crossingRecord machine input T)⟩
    workHead :=
      ⟨(run machine input T).workHead, by
        exact Nat.lt_succ_of_le (by
          simpa [workHeadTrajectory, workHeadTrajectoryFrom, run] using
            (workHeadTrajectory_le_time machine input T))⟩ }

@[simp]
theorem boundedTerminalEndpointAtRun_state
    (machine : DeterministicMachine) (input : List Bool) (T : Nat) :
    (boundedTerminalEndpointAtRun machine input T).state =
      (run machine input T).state :=
  rfl

@[simp]
theorem boundedTerminalEndpointAtRun_inputHead_val
    (machine : DeterministicMachine) (input : List Bool) (T : Nat) :
    (boundedTerminalEndpointAtRun machine input T).inputHead.val =
      (run machine input T).inputHead :=
  rfl

@[simp]
theorem boundedTerminalEndpointAtRun_workHead_val
    (machine : DeterministicMachine) (input : List Bool) (T : Nat) :
    (boundedTerminalEndpointAtRun machine input T).workHead.val =
      (run machine input T).workHead :=
  rfl

/-- Retain the source time while forgetting the reconstructible physical-cut
field of a chronological record. -/
def timedCanonicalCrossingTokenOfEntry
    {State : Type} {T b : Nat}
    (entry : ChronologicalCanonicalCrossingEntry State T b) :
    TimedCanonicalCrossingToken State T b :=
  { sourceTime := entry.time
    token := canonicalCrossingTokenOfRecord entry.record }

/-- The actual timed crossing tokens, in their proved chronological order. -/
noncomputable def chronologicalTimedCanonicalCrossingTokens
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    List (TimedCanonicalCrossingToken machine.State T b) :=
  (chronologicalCanonicalCrossingEntries machine input T b hb).map
    timedCanonicalCrossingTokenOfEntry

/-- Projecting source times from the timed list recovers the actual selected
crossing-time list exactly. -/
theorem map_sourceTime_chronologicalTimedCanonicalCrossingTokens
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    (chronologicalTimedCanonicalCrossingTokens machine input T b hb).map
        TimedCanonicalCrossingToken.sourceTime =
      actualSelectedBoundaryCrossingTimes machine input T b hb := by
  simpa [chronologicalTimedCanonicalCrossingTokens,
    timedCanonicalCrossingTokenOfEntry, List.map_map] using
      (map_time_chronologicalCanonicalCrossingEntries
        machine input T b hb)

/-- Hence the retained source times are strictly increasing. -/
theorem chronologicalTimedCanonicalCrossingTokens_times_pairwise_lt
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    ((chronologicalTimedCanonicalCrossingTokens machine input T b hb).map
      TimedCanonicalCrossingToken.sourceTime).Pairwise
        (fun earlier later => earlier < later) := by
  rw [map_sourceTime_chronologicalTimedCanonicalCrossingTokens]
  exact actualSelectedBoundaryCrossingTimes_pairwise_lt
    machine input T b hb

/-- The timed list has exactly as many entries as the selected crossing-time
list. -/
theorem length_chronologicalTimedCanonicalCrossingTokens_eq_times
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    (chronologicalTimedCanonicalCrossingTokens machine input T b hb).length =
      (actualSelectedBoundaryCrossingTimes machine input T b hb).length := by
  have h := congrArg List.length
    (map_sourceTime_chronologicalTimedCanonicalCrossingTokens
      machine input T b hb)
  simpa using h

/-- Canonical charging still bounds the number of timed entries by `T / b`. -/
theorem length_chronologicalTimedCanonicalCrossingTokens_le_div
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    (chronologicalTimedCanonicalCrossingTokens machine input T b hb).length ≤
      T / b := by
  rw [length_chronologicalTimedCanonicalCrossingTokens_eq_times]
  exact length_actualSelectedBoundaryCrossingTimes_le_div
    machine input T b hb

/-- A fixed `T / b`-slot word over optional timed crossing tokens. -/
abbrev PaddedTimedCanonicalCrossingWord
    (State : Type) (T b : Nat) :=
  Fin (T / b) → Option (TimedCanonicalCrossingToken State T b)

/-- Exact size of the full optional timed-word carrier.  Non-prefix-shaped and
chronologically inconsistent words are included. -/
theorem card_paddedTimedCanonicalCrossingWord
    (State : Type) [Fintype State] (T b : Nat) :
    Fintype.card (PaddedTimedCanonicalCrossingWord State T b) =
      (1 + T * ((T / b) *
        (2 * Fintype.card State * (T + 1)))) ^ (T / b) := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_option,
    card_timedCanonicalCrossingToken]
  congr 1
  omega

/-- Ambient fixed-size metadata: canonical cut offsets, a padded timed token
word, and a bounded terminal endpoint. -/
structure AmbientTimedCanonicalAlpha (State : Type) (T b : Nat) where
  offsets : CanonicalCutOffsets T b
  word : PaddedTimedCanonicalCrossingWord State T b
  terminal : BoundedTerminalEndpoint State T
deriving Fintype

/-- The ambient timed alpha is exactly the product of its three fields. -/
def ambientTimedCanonicalAlphaEquiv (State : Type) (T b : Nat) :
    AmbientTimedCanonicalAlpha State T b ≃
      CanonicalCutOffsets T b ×
        PaddedTimedCanonicalCrossingWord State T b ×
          BoundedTerminalEndpoint State T where
  toFun alpha := (alpha.offsets, alpha.word, alpha.terminal)
  invFun fields := ⟨fields.1, fields.2.1, fields.2.2⟩
  left_inv alpha := by cases alpha; rfl
  right_inv fields := by
    rcases fields with ⟨offsets, word, terminal⟩
    rfl

/-- Exact full ambient timed-alpha count.

The factor `T` inside the word alphabet pays for crossing times; the final
factor pays for the terminal endpoint.  This formula counts the carrier only
and supplies no local consistency or reachability conclusion. -/
theorem card_ambientTimedCanonicalAlpha
    (State : Type) [Fintype State] (T b : Nat) :
    Fintype.card (AmbientTimedCanonicalAlpha State T b) =
      b ^ (T / b) *
        (1 + T * ((T / b) *
          (2 * Fintype.card State * (T + 1)))) ^ (T / b) *
        (Fintype.card State * (T + 1) * (T + 1)) := by
  rw [Fintype.card_congr (ambientTimedCanonicalAlphaEquiv State T b),
    Fintype.card_prod, Fintype.card_prod,
    card_canonicalCutOffsets, card_paddedTimedCanonicalCrossingWord,
    card_boundedTerminalEndpoint]
  simp [Nat.mul_assoc]

/-- Extract the actual timed metadata of one deterministic run. -/
noncomputable def chronologicalTimedCanonicalAlpha
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    AmbientTimedCanonicalAlpha machine.State T b :=
  { offsets := canonicalCutOffsets machine input T b hb
    word := encodePaddedWord (T / b)
      (chronologicalTimedCanonicalCrossingTokens machine input T b hb)
    terminal := boundedTerminalEndpointAtRun machine input T }

/-- Prefix decoding exactly recovers the actual chronological timed-token
list. -/
theorem decode_chronologicalTimedCanonicalAlpha_word
    (machine : DeterministicMachine) (input : List Bool)
    (T b : Nat) (hb : 0 < b) :
    decodePaddedWord (T / b)
        (chronologicalTimedCanonicalAlpha machine input T b hb).word =
      chronologicalTimedCanonicalCrossingTokens machine input T b hb := by
  exact decode_encodePaddedWord (T / b)
    (chronologicalTimedCanonicalCrossingTokens machine input T b hb)
    (length_chronologicalTimedCanonicalCrossingTokens_le_div
      machine input T b hb)

end OneTapeMagnification
end Frontier
end Pnp4
