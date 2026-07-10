import Pnp4.Frontier.OneTapeMagnification.LocalBlockReplay

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Honest composition of two local slab replays

`runFrom_sameOnWorkSlab_same_input` preserves agreement on the slab in which
the replayed work head stays.  Its conclusion also preserves the control state
and both head positions, even when the final transition leaves that slab.
Those three equalities can be reused at the entry of a second segment.

What the first replay does **not** provide is agreement on the work-tape
restriction of a different destination slab.  The main theorem below keeps
that missing equality as an explicit hypothesis and then applies the local
replay theorem a second time.  A small corollary accepts the stronger statement
that the two midpoint configurations already agree on both slabs.

This is only a two-segment composition lemma.  It does not construct the
missing destination-slab equality, a fixed-alpha validator, a branching
program, or a width bound.
-/

/-- Agreement on two named slabs at once.  The state and head equalities are
intentionally repeated through the existing `SameOnWorkSlab` interface; this
keeps the strengthening transparent and avoids introducing a new global tape
interface. -/
def SameOnTwoWorkSlabs {State : Type}
    (firstBase firstWidth secondBase secondWidth : Nat)
    (left right : Configuration State) : Prop :=
  SameOnWorkSlab firstBase firstWidth left right ∧
    SameOnWorkSlab secondBase secondWidth left right

/-- Compose two same-input slab replays.

After the first segment, agreement on its slab supplies equality of the
control state and both heads.  To change to the second slab, equality of that
slab's complete restriction is required explicitly.  The final transition of
either segment may leave its slab, because the inside hypotheses range only
over pre-transition times. -/
theorem runFrom_sameOn_two_workSlabs
    (machine : DeterministicMachine) (input : List Bool)
    {left right : Configuration machine.State}
    {firstBase firstWidth secondBase secondWidth : Nat}
    {firstSteps secondSteps : Nat}
    (hEntry : SameOnWorkSlab firstBase firstWidth left right)
    (hInsideFirst : ∀ time, time < firstSteps →
      WorkCellInSlab firstBase firstWidth
        (runFrom machine input left time).workHead)
    (hSecondTapeAtMidpoint :
      restrictWorkSlab secondBase secondWidth
          (runFrom machine input left firstSteps).workTape =
        restrictWorkSlab secondBase secondWidth
          (runFrom machine input right firstSteps).workTape)
    (hInsideSecond : ∀ time, time < secondSteps →
      WorkCellInSlab secondBase secondWidth
        (runFrom machine input
          (runFrom machine input left firstSteps) time).workHead) :
    SameOnWorkSlab secondBase secondWidth
      (runFrom machine input left (firstSteps + secondSteps))
      (runFrom machine input right (firstSteps + secondSteps)) := by
  have hFirstExit : SameOnWorkSlab firstBase firstWidth
      (runFrom machine input left firstSteps)
      (runFrom machine input right firstSteps) :=
    runFrom_sameOnWorkSlab_same_input machine input hEntry hInsideFirst
  have hSecondEntry : SameOnWorkSlab secondBase secondWidth
      (runFrom machine input left firstSteps)
      (runFrom machine input right firstSteps) := by
    exact ⟨hFirstExit.1, hFirstExit.2.1, hFirstExit.2.2.1,
      hSecondTapeAtMidpoint⟩
  have hSecondExit := runFrom_sameOnWorkSlab_same_input machine input
    hSecondEntry hInsideSecond
  simpa only [runFrom_add] using hSecondExit

/-- Strong-interface corollary: if the midpoint configurations are already
known to agree on both slabs, their second-slab component supplies the explicit
restriction equality required by `runFrom_sameOn_two_workSlabs`.

The first-slab replay hypotheses are retained to make this a direct corollary
of the composition theorem; the stronger midpoint assumption is not claimed
to follow from them. -/
theorem runFrom_sameOn_two_workSlabs_of_sameOnTwoAtMidpoint
    (machine : DeterministicMachine) (input : List Bool)
    {left right : Configuration machine.State}
    {firstBase firstWidth secondBase secondWidth : Nat}
    {firstSteps secondSteps : Nat}
    (hEntry : SameOnWorkSlab firstBase firstWidth left right)
    (hInsideFirst : ∀ time, time < firstSteps →
      WorkCellInSlab firstBase firstWidth
        (runFrom machine input left time).workHead)
    (hBothAtMidpoint : SameOnTwoWorkSlabs
      firstBase firstWidth secondBase secondWidth
      (runFrom machine input left firstSteps)
      (runFrom machine input right firstSteps))
    (hInsideSecond : ∀ time, time < secondSteps →
      WorkCellInSlab secondBase secondWidth
        (runFrom machine input
          (runFrom machine input left firstSteps) time).workHead) :
    SameOnWorkSlab secondBase secondWidth
      (runFrom machine input left (firstSteps + secondSteps))
      (runFrom machine input right (firstSteps + secondSteps)) := by
  apply runFrom_sameOn_two_workSlabs machine input hEntry hInsideFirst
      hBothAtMidpoint.2.2.2.2 hInsideSecond

end OneTapeMagnification
end Frontier
end Pnp4
