import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.AdvertisedCutBlockSlabs
import Pnp4.Frontier.OneTapeMagnification.FixedAlphaBlockVisitReplay

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Endpoints forced by an advertised timed crossing token

For a fixed ambient alpha, a token's selected-bucket field and the matching
advertised offset reconstruct one physical cut.  Its direction then determines
the source/destination block labels and the exact pre/post work-head positions.
The payload already stores the post-transition control state and input head,
so the full bounded post endpoint is determined without any actual-run data.

The resulting source head lies in the source advertised slab and the post head
lies in the destination slab.  These are geometry and finite-interface facts;
they do not assert that the token is reachable, chronologically chained to its
neighbors, locally replayable, or attached to a leftmost-minimum cut.
-/

/-- Reconstruct the physical cut named by one timed token and fixed offsets. -/
def advertisedTimedCrossingPhysicalCut
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (crossing : TimedCanonicalCrossingToken State T b) : Fin T :=
  physicalCutOfCanonicalToken alpha.offsets crossing.token

/-- The work block from which the advertised crossing departs. -/
def advertisedTimedCrossingSourceBlock
    {State : Type} {T b : Nat}
    (crossing : TimedCanonicalCrossingToken State T b) :
    Fin (T / b + 1) :=
  match crossing.token.2.direction with
  | .leftToRight => advertisedCutLeftBlock crossing.token.1
  | .rightToLeft => advertisedCutRightBlock crossing.token.1

/-- The work block entered by the advertised crossing. -/
def advertisedTimedCrossingDestinationBlock
    {State : Type} {T b : Nat}
    (crossing : TimedCanonicalCrossingToken State T b) :
    Fin (T / b + 1) :=
  match crossing.token.2.direction with
  | .leftToRight => advertisedCutRightBlock crossing.token.1
  | .rightToLeft => advertisedCutLeftBlock crossing.token.1

/-- Bounded pre-transition work-head position forced by cut and direction. -/
def advertisedTimedCrossingPreWorkHead
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (crossing : TimedCanonicalCrossingToken State T b) : Fin (T + 1) :=
  match crossing.token.2.direction with
  | .leftToRight => Fin.castSucc
      (advertisedTimedCrossingPhysicalCut alpha crossing)
  | .rightToLeft => Fin.succ
      (advertisedTimedCrossingPhysicalCut alpha crossing)

/-- Bounded post-transition work-head position forced by cut and direction. -/
def advertisedTimedCrossingPostWorkHead
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (crossing : TimedCanonicalCrossingToken State T b) : Fin (T + 1) :=
  match crossing.token.2.direction with
  | .leftToRight => Fin.succ
      (advertisedTimedCrossingPhysicalCut alpha crossing)
  | .rightToLeft => Fin.castSucc
      (advertisedTimedCrossingPhysicalCut alpha crossing)

/-- Complete bounded post-transition endpoint determined by one token. -/
def advertisedTimedCrossingPostEndpoint
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (crossing : TimedCanonicalCrossingToken State T b) :
    FixedAlphaVisitEndpoint State T :=
  { state := crossing.token.2.postState
    inputHead := crossing.token.2.postInputHead
    workHead := advertisedTimedCrossingPostWorkHead alpha crossing }

/-- Crossing source and destination labels are always the two distinct blocks
adjacent to the advertised cut. -/
theorem advertisedTimedCrossing_sourceBlock_ne_destinationBlock
    {State : Type} {T b : Nat}
    (crossing : TimedCanonicalCrossingToken State T b) :
    advertisedTimedCrossingSourceBlock crossing ≠
      advertisedTimedCrossingDestinationBlock crossing := by
  cases hdirection : crossing.token.2.direction <;>
    simp [advertisedTimedCrossingSourceBlock,
      advertisedTimedCrossingDestinationBlock, hdirection, Fin.ext_iff]

/-- The forced pre-transition head belongs to the advertised source slab. -/
theorem advertisedTimedCrossing_preWorkHead_in_sourceSlab
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (crossing : TimedCanonicalCrossingToken State T b) :
    WorkCellInSlab
      (advertisedBlockLower alpha.offsets
        (advertisedTimedCrossingSourceBlock crossing))
      (advertisedBlockWidth alpha.offsets
        (advertisedTimedCrossingSourceBlock crossing))
      (advertisedTimedCrossingPreWorkHead alpha crossing).val := by
  cases hdirection : crossing.token.2.direction
  · simpa [advertisedTimedCrossingSourceBlock,
      advertisedTimedCrossingPreWorkHead,
      advertisedTimedCrossingPhysicalCut, physicalCutOfCanonicalToken,
      hdirection] using
        (advertisedPhysicalCut_mem_leftBlockSlab
          alpha.offsets crossing.token.1)
  · simpa [advertisedTimedCrossingSourceBlock,
      advertisedTimedCrossingPreWorkHead,
      advertisedTimedCrossingPhysicalCut, physicalCutOfCanonicalToken,
      hdirection] using
        (advertisedPhysicalCut_succ_mem_rightBlockSlab
          alpha.offsets crossing.token.1)

/-- The forced post-transition head belongs to the advertised destination
slab. -/
theorem advertisedTimedCrossing_postWorkHead_in_destinationSlab
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (crossing : TimedCanonicalCrossingToken State T b) :
    WorkCellInSlab
      (advertisedBlockLower alpha.offsets
        (advertisedTimedCrossingDestinationBlock crossing))
      (advertisedBlockWidth alpha.offsets
        (advertisedTimedCrossingDestinationBlock crossing))
      (advertisedTimedCrossingPostWorkHead alpha crossing).val := by
  cases hdirection : crossing.token.2.direction
  · simpa [advertisedTimedCrossingDestinationBlock,
      advertisedTimedCrossingPostWorkHead,
      advertisedTimedCrossingPhysicalCut, physicalCutOfCanonicalToken,
      hdirection] using
        (advertisedPhysicalCut_succ_mem_rightBlockSlab
          alpha.offsets crossing.token.1)
  · simpa [advertisedTimedCrossingDestinationBlock,
      advertisedTimedCrossingPostWorkHead,
      advertisedTimedCrossingPhysicalCut, physicalCutOfCanonicalToken,
      hdirection] using
        (advertisedPhysicalCut_mem_leftBlockSlab
          alpha.offsets crossing.token.1)

@[simp]
theorem advertisedTimedCrossingPostEndpoint_state
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (crossing : TimedCanonicalCrossingToken State T b) :
    (advertisedTimedCrossingPostEndpoint alpha crossing).state =
      crossing.token.2.postState :=
  rfl

@[simp]
theorem advertisedTimedCrossingPostEndpoint_inputHead
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (crossing : TimedCanonicalCrossingToken State T b) :
    (advertisedTimedCrossingPostEndpoint alpha crossing).inputHead =
      crossing.token.2.postInputHead :=
  rfl

@[simp]
theorem advertisedTimedCrossingPostEndpoint_workHead
    {State : Type} {T b : Nat}
    (alpha : AmbientTimedCanonicalAlpha State T b)
    (crossing : TimedCanonicalCrossingToken State T b) :
    (advertisedTimedCrossingPostEndpoint alpha crossing).workHead =
      advertisedTimedCrossingPostWorkHead alpha crossing :=
  rfl

end OneTapeMagnification
end Frontier
end Pnp4
