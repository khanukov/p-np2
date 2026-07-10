import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.CanonicalBlockSlabs

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Cardinality of the already-proved local replay state

`LocalBlockReplay` proves exact deterministic replay while the work head is
inside a fixed slab.  This file packages only the finite data visible in that
lemma at a horizon `T` and slab width `w`:

* the finite control state;
* an input-head position in `0, ..., T`;
* a work-head position relative to the slab; and
* the Boolean contents of the slab.

Its cardinality is exactly

`|Q| * (T + 1) * w * 2^w`.

This carrier deliberately omits the boundary-minimality counters, replay
phase/schedule, and local-validation data needed in a Viola-style argument.
Those extra components are expected to cost roughly `O(b * log T)` bits in
the intended analysis, but no such bound is proved here.  In particular, the
cardinality below is not claimed to be the width of a complete branching
program.
-/

/-- The finite portion of a configuration already covered by exact slab
replay.  Both head fields are bounded coordinates: `inputHead.val <= T`, and
`relativeWorkHead` names the currently scanned cell of the width-`w` slab. -/
structure LocalReplayState (State : Type) (T w : Nat) where
  control : State
  inputHead : Fin (T + 1)
  relativeWorkHead : Fin w
  workSlab : WorkSlab w
deriving Fintype

/-- The local replay structure is just the displayed product of its four
finite fields. -/
def localReplayStateEquiv (State : Type) (T w : Nat) :
    LocalReplayState State T w ≃
      State × Fin (T + 1) × Fin w × WorkSlab w where
  toFun state :=
    (state.control, state.inputHead, state.relativeWorkHead, state.workSlab)
  invFun fields :=
    ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2⟩
  left_inv state := by cases state; rfl
  right_inv fields := by rcases fields with ⟨control, inputHead,
    relativeWorkHead, workSlab⟩; rfl

/-- Exact size of the finite local replay carrier. -/
theorem card_localReplayState (machine : DeterministicMachine) (T w : Nat) :
    letI := machine.stateFintype
    Fintype.card (LocalReplayState machine.State T w) =
      Fintype.card machine.State * (T + 1) * w * 2 ^ w := by
  letI := machine.stateFintype
  rw [Fintype.card_congr
    (localReplayStateEquiv machine.State T w)]
  simp [Nat.mul_assoc]

/-- The local carrier for the explicit slab assigned to one canonical work
block. -/
abbrev CanonicalLocalReplayState {T b : Nat} (hb : 0 < b)
    (crossings : Fin T -> Nat) (machine : DeterministicMachine)
    (block : Fin (T / b + 1)) :=
  LocalReplayState machine.State T
    (canonicalBlockWidth hb crossings block)

/-- A canonical slab has a genuine relative head coordinate, so its local
carrier is nonempty.  This is the point at which the positive-width theorem
is used, rather than silently treating `Fin 0` as a possible head type. -/
theorem canonicalLocalReplayState_card_pos {T b : Nat} (hb : 0 < b)
    (crossings : Fin T -> Nat) (machine : DeterministicMachine)
    (block : Fin (T / b + 1)) :
    letI := machine.stateFintype
    0 < Fintype.card
      (CanonicalLocalReplayState hb crossings machine block) := by
  letI := machine.stateFintype
  rw [card_localReplayState]
  have hState : 0 < Fintype.card machine.State :=
    Fintype.card_pos_iff.mpr ⟨machine.startState⟩
  have hWidth : 0 < canonicalBlockWidth hb crossings block :=
    canonicalBlockWidth_pos hb crossings block
  positivity

/-- Honest ambient cardinal bound for the already-proved replay state of any
canonical block.  It uses only the established width bound `w <= 2 * b`; it
does not account for the additional validator/counter state omitted above. -/
theorem canonicalLocalReplayState_card_le {T b : Nat} (hb : 0 < b)
    (crossings : Fin T -> Nat) (machine : DeterministicMachine)
    (block : Fin (T / b + 1)) :
    letI := machine.stateFintype
    Fintype.card (CanonicalLocalReplayState hb crossings machine block) <=
      Fintype.card machine.State * (T + 1) * (2 * b) * 2 ^ (2 * b) := by
  letI := machine.stateFintype
  rw [card_localReplayState]
  have hWidth : canonicalBlockWidth hb crossings block <= 2 * b :=
    canonicalBlockWidth_le_two_mul hb crossings block
  have hPow :
      2 ^ canonicalBlockWidth hb crossings block <= 2 ^ (2 * b) := by
    exact Nat.pow_le_pow_right (by omega) hWidth
  exact Nat.mul_le_mul
    (Nat.mul_le_mul_left
      (Fintype.card machine.State * (T + 1)) hWidth)
    hPow

/-- Combined nonemptiness and ambient-size statement.  The lower fact comes
from positive canonical width; the upper fact comes from width at most
`2 * b`. -/
theorem canonicalLocalReplayState_card_bounds {T b : Nat} (hb : 0 < b)
    (crossings : Fin T -> Nat) (machine : DeterministicMachine)
    (block : Fin (T / b + 1)) :
    letI := machine.stateFintype
    0 < Fintype.card
        (CanonicalLocalReplayState hb crossings machine block) /\
      Fintype.card
          (CanonicalLocalReplayState hb crossings machine block) <=
        Fintype.card machine.State * (T + 1) * (2 * b) * 2 ^ (2 * b) := by
  letI := machine.stateFintype
  exact ⟨canonicalLocalReplayState_card_pos hb crossings machine block,
    canonicalLocalReplayState_card_le hb crossings machine block⟩

end OneTapeMagnification
end Frontier
end Pnp4
