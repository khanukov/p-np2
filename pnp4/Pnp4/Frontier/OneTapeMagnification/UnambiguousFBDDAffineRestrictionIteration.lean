import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDPaddedRestriction
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDOneRoundFoolingBound

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Affine padded restrictions and finite round telescoping

An ordinary padded partial assignment represents the frozen coordinates of
`maskedInput base mask input`, but it does not by itself represent the XOR by
`base` on a live coordinate.  When both `mask q` and `base q` are true, the
restricted function reads the negation of `input q`; a branching program for
that function must swap the false and true successors of query `q`.

This file supplies that missing structural closure operation.  Frozen queries
retain one selected successor twice, live queries with false base are kept,
and live queries with true base have their successors swapped.  The operation
has exactly the semantics of `maskedInput`, preserves every query event and
the vertex type, and hence preserves syntactic read-once, unambiguity, and a
full-read premise.  A list-level version gives exact recursive masked
composition.

The final section is deliberately model-independent: it proves the finite
telescoping inequality that turns a uniform per-round error into `L * error`
and appends an arbitrary zero-tail cost.  Its quantitative specialization has
the DPTW-shaped expression

`L * S * p ^ m + N * (1 - p) ^ L`.

No one-round Fourier or low-degree estimate is proved here.
-/

open FiniteBooleanRestrictionMoment

namespace FiniteUFBDDNode

/-- Query-preserving affine restriction.  A false mask freezes the query at
`base`; a true mask keeps it live, swapping its two successors when the base
bit is true. -/
def affinePaddedRestrictBy {n : Nat} {Vertex : Type}
    (base mask : Fin n -> Bool) :
    FiniteUFBDDNode n Vertex -> FiniteUFBDDNode n Vertex
  | .query queryIndex ifFalse ifTrue =>
      match mask queryIndex, base queryIndex with
      | false, false => .query queryIndex ifFalse ifFalse
      | false, true => .query queryIndex ifTrue ifTrue
      | true, false => .query queryIndex ifFalse ifTrue
      | true, true => .query queryIndex ifTrue ifFalse
  | .choice children => .choice children
  | .sink => .sink

/-- Every edge of an affine padded node is an edge of the original node. -/
theorem hasChild_of_affinePaddedRestrictBy_hasChild
    {n : Nat} {Vertex : Type}
    (base mask : Fin n -> Bool)
    (node : FiniteUFBDDNode n Vertex) (target : Vertex)
    (hchild : (node.affinePaddedRestrictBy base mask).HasChild target) :
    node.HasChild target := by
  cases node with
  | query queryIndex ifFalse ifTrue =>
      cases hmask : mask queryIndex <;> cases hbase : base queryIndex
      · have htarget : target = ifFalse := by
          simpa [affinePaddedRestrictBy, HasChild, hmask, hbase] using hchild
        exact Or.inl htarget
      · have htarget : target = ifTrue := by
          simpa [affinePaddedRestrictBy, HasChild, hmask, hbase] using hchild
        exact Or.inr htarget
      · simpa [affinePaddedRestrictBy, HasChild, hmask, hbase] using hchild
      · simpa [affinePaddedRestrictBy, HasChild, hmask, hbase, or_comm]
          using hchild
  | choice children =>
      simpa [affinePaddedRestrictBy, HasChild] using hchild
  | sink =>
      simp [affinePaddedRestrictBy, HasChild] at hchild

end FiniteUFBDDNode

namespace FiniteUnambiguousFBDD

/-- A finite uFBDD for the affine-masked function
`input |-> B (maskedInput base mask input)`. -/
def affinePaddedRestrictBy {n : Nat} (B : FiniteUnambiguousFBDD n)
    (base mask : Fin n -> Bool) : FiniteUnambiguousFBDD n where
  Vertex := B.Vertex
  vertexFintype := B.vertexFintype
  vertexDecidableEq := B.vertexDecidableEq
  start := B.start
  accept := B.accept
  node vertex := (B.node vertex).affinePaddedRestrictBy base mask
  accept_sink := by
    simp [FiniteUFBDDNode.affinePaddedRestrictBy, B.accept_sink]
  rank := B.rank
  rank_child := by
    intro source target hchild
    exact B.rank_child
      (FiniteUFBDDNode.hasChild_of_affinePaddedRestrictBy_hasChild
        base mask (B.node source) target hchild)

@[simp]
theorem affinePaddedRestrictBy_start {n : Nat}
    (B : FiniteUnambiguousFBDD n) (base mask : Fin n -> Bool) :
    (B.affinePaddedRestrictBy base mask).start = B.start := rfl

@[simp]
theorem affinePaddedRestrictBy_accept {n : Nat}
    (B : FiniteUnambiguousFBDD n) (base mask : Fin n -> Bool) :
    (B.affinePaddedRestrictBy base mask).accept = B.accept := rfl

/-- Affine padded restriction preserves the vertex count definitionally. -/
theorem affinePaddedRestrictBy_vertex_card {n : Nat}
    (B : FiniteUnambiguousFBDD n) (base mask : Fin n -> Bool) :
    @Fintype.card (B.affinePaddedRestrictBy base mask).Vertex
        (B.affinePaddedRestrictBy base mask).vertexFintype =
      @Fintype.card B.Vertex B.vertexFintype := rfl

/-- A compatible transformed edge is exactly an original edge compatible
with the affine-masked input. -/
theorem affinePaddedRestrictBy_compatibleEdge_iff
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (base mask input : Fin n -> Bool) (source target : B.Vertex) :
    (B.affinePaddedRestrictBy base mask).CompatibleEdge input source target <->
      B.CompatibleEdge (maskedInput base mask input) source target := by
  cases hnode : B.node source with
  | query queryIndex ifFalse ifTrue =>
      cases hmask : mask queryIndex <;>
        cases hbase : base queryIndex <;>
          cases hinput : input queryIndex <;>
            simp [CompatibleEdge, affinePaddedRestrictBy,
              FiniteUFBDDNode.affinePaddedRestrictBy, maskedInput,
              hnode, hmask, hbase, hinput]
  | choice children =>
      simp [CompatibleEdge, affinePaddedRestrictBy,
        FiniteUFBDDNode.affinePaddedRestrictBy, hnode]
  | sink =>
      simp [CompatibleEdge, affinePaddedRestrictBy,
        FiniteUFBDDNode.affinePaddedRestrictBy, hnode]

/-- Every transformed graph edge is an original graph edge. -/
theorem edge_of_affinePaddedRestrictBy_edge
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (base mask : Fin n -> Bool) {source target : B.Vertex}
    (edge : (B.affinePaddedRestrictBy base mask).Edge source target) :
    B.Edge source target :=
  FiniteUFBDDNode.hasChild_of_affinePaddedRestrictBy_hasChild
    base mask (B.node source) target edge

namespace AffinePaddedRestrictionWalk

/-- Forget that a walk lives in an affine padded diagram. -/
def toOriginal {n : Nat} {B : FiniteUnambiguousFBDD n}
    {base mask : Fin n -> Bool} {source target : B.Vertex} :
    (B.affinePaddedRestrictBy base mask).Walk source target ->
      B.Walk source target
  | .nil vertex => @FiniteUnambiguousFBDD.Walk.nil n B vertex
  | .cons edge tail =>
      @FiniteUnambiguousFBDD.Walk.cons n B _ _ _
        (B.edge_of_affinePaddedRestrictBy_edge base mask edge)
        (toOriginal (B := B) (base := base) (mask := mask) tail)

/-- Walk compatibility is transported exactly by `maskedInput`. -/
theorem toOriginal_compatible_iff
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {base mask : Fin n -> Bool} (input : Fin n -> Bool)
    {source target : B.Vertex}
    (walk : (B.affinePaddedRestrictBy base mask).Walk source target) :
    FiniteUnambiguousFBDD.Walk.Compatible
        (B := B.affinePaddedRestrictBy base mask) input walk <->
      FiniteUnambiguousFBDD.Walk.Compatible
        (B := B) (maskedInput base mask input)
          (toOriginal (B := B) (base := base) (mask := mask) walk) := by
  refine FiniteUnambiguousFBDD.Walk.recOn
    (motive := fun source target currentWalk =>
      FiniteUnambiguousFBDD.Walk.Compatible
          (B := B.affinePaddedRestrictBy base mask) input currentWalk <->
        FiniteUnambiguousFBDD.Walk.Compatible
          (B := B) (maskedInput base mask input)
            (toOriginal (B := B) (base := base) (mask := mask) currentWalk))
    walk ?_ ?_
  · intro vertex
    simp [toOriginal, FiniteUnambiguousFBDD.Walk.Compatible]
  · intro source middle target edge tail ih
    simp only [FiniteUnambiguousFBDD.Walk.Compatible, toOriginal]
    rw [B.affinePaddedRestrictBy_compatibleEdge_iff
      base mask input source middle, ih]

/-- Rebuild a transformed walk from an original compatible walk. -/
def ofOriginalCompatible
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {base mask : Fin n -> Bool} (input : Fin n -> Bool) :
    {source target : B.Vertex} ->
    (walk : B.Walk source target) ->
    FiniteUnambiguousFBDD.Walk.Compatible
      (B := B) (maskedInput base mask input) walk ->
    (B.affinePaddedRestrictBy base mask).Walk source target
  | _, _, .nil vertex, _ =>
      @FiniteUnambiguousFBDD.Walk.nil n
        (B.affinePaddedRestrictBy base mask) vertex
  | _, _, .cons (source := source) (middle := middle) _edge tail,
      hcompatible =>
      @FiniteUnambiguousFBDD.Walk.cons n
        (B.affinePaddedRestrictBy base mask) source middle _
          ((B.affinePaddedRestrictBy base mask).edge_of_compatibleEdge input
            ((B.affinePaddedRestrictBy_compatibleEdge_iff
              base mask input source middle).mpr hcompatible.1))
          (ofOriginalCompatible input tail hcompatible.2)

/-- The rebuilt transformed walk is compatible with the transformed input. -/
theorem ofOriginalCompatible_compatible
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {base mask : Fin n -> Bool} (input : Fin n -> Bool)
    {source target : B.Vertex} (walk : B.Walk source target)
    (hcompatible : FiniteUnambiguousFBDD.Walk.Compatible
      (B := B) (maskedInput base mask input) walk) :
    FiniteUnambiguousFBDD.Walk.Compatible
      (B := B.affinePaddedRestrictBy base mask) input
        (ofOriginalCompatible input walk hcompatible) := by
  refine (FiniteUnambiguousFBDD.Walk.recOn
    (motive := fun source target currentWalk =>
      forall hcurrent : FiniteUnambiguousFBDD.Walk.Compatible
          (B := B) (maskedInput base mask input) currentWalk,
        FiniteUnambiguousFBDD.Walk.Compatible
          (B := B.affinePaddedRestrictBy base mask) input
            (ofOriginalCompatible input currentWalk hcurrent))
    walk ?_ ?_) hcompatible
  · intro vertex hcurrent
    cases hcurrent
    rw [ofOriginalCompatible]
    trivial
  · intro source middle target edge tail ih hcurrent
    rcases hcurrent with ⟨hhead, htail⟩
    rw [ofOriginalCompatible]
    exact ⟨(B.affinePaddedRestrictBy_compatibleEdge_iff
      base mask input source middle).mpr hhead, ih htail⟩

/-- Forgetting a rebuilt transformed walk returns the original walk. -/
theorem toOriginal_ofOriginalCompatible
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {base mask : Fin n -> Bool} (input : Fin n -> Bool)
    {source target : B.Vertex} (walk : B.Walk source target)
    (hcompatible : FiniteUnambiguousFBDD.Walk.Compatible
      (B := B) (maskedInput base mask input) walk) :
    toOriginal (B := B) (base := base) (mask := mask)
        (ofOriginalCompatible input walk hcompatible) = walk := by
  refine (FiniteUnambiguousFBDD.Walk.recOn
    (motive := fun source target currentWalk =>
      forall hcurrent : FiniteUnambiguousFBDD.Walk.Compatible
          (B := B) (maskedInput base mask input) currentWalk,
        toOriginal (B := B) (base := base) (mask := mask)
            (ofOriginalCompatible input currentWalk hcurrent) = currentWalk)
    walk ?_ ?_) hcompatible
  · intro vertex hcurrent
    cases hcurrent
    rw [ofOriginalCompatible]
    rfl
  · intro source middle target edge tail ih hcurrent
    rcases hcurrent with ⟨hhead, htail⟩
    rw [ofOriginalCompatible]
    change @FiniteUnambiguousFBDD.Walk.cons n B source middle target _
        (toOriginal (B := B) (base := base) (mask := mask)
          (ofOriginalCompatible input tail htail)) =
      @FiniteUnambiguousFBDD.Walk.cons n B source middle target edge tail
    rw [ih htail]

/-- Forgetting preserves the vertex sequence. -/
theorem toOriginal_vertices
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {base mask : Fin n -> Bool} {source target : B.Vertex}
    (walk : (B.affinePaddedRestrictBy base mask).Walk source target) :
    (toOriginal (B := B) (base := base) (mask := mask) walk).vertices =
      walk.vertices := by
  refine FiniteUnambiguousFBDD.Walk.recOn
    (motive := fun source target currentWalk =>
      (toOriginal (B := B) (base := base) (mask := mask)
        currentWalk).vertices = currentWalk.vertices)
    walk ?_ ?_
  · intro vertex
    rfl
  · intro source middle target edge tail ih
    simp [toOriginal, FiniteUnambiguousFBDD.Walk.vertices, ih]

/-- Forgetting affine padding is injective on walks. -/
theorem toOriginal_injective
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {base mask : Fin n -> Bool} {source target : B.Vertex} :
    Function.Injective
      (toOriginal (B := B) (base := base) (mask := mask) :
        (B.affinePaddedRestrictBy base mask).Walk source target ->
          B.Walk source target) := by
  intro left right heq
  apply FiniteUnambiguousFBDD.Walk.eq_of_vertices_eq left right
  rw [← toOriginal_vertices (B := B) (base := base) (mask := mask) left,
    ← toOriginal_vertices (B := B) (base := base) (mask := mask) right, heq]

/-- Affine padding preserves all query events, including frozen queries. -/
theorem toOriginal_queryEvents
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {base mask : Fin n -> Bool} {source target : B.Vertex}
    (walk : (B.affinePaddedRestrictBy base mask).Walk source target) :
    (toOriginal (B := B) (base := base) (mask := mask) walk).queryEvents =
      walk.queryEvents := by
  refine FiniteUnambiguousFBDD.Walk.recOn
    (motive := fun source target currentWalk =>
      (toOriginal (B := B) (base := base) (mask := mask)
        currentWalk).queryEvents = currentWalk.queryEvents)
    walk ?_ ?_
  · intro vertex
    rfl
  · intro source middle target edge tail ih
    cases hnode : B.node source with
    | query queryIndex ifFalse ifTrue =>
        cases hmask : mask queryIndex <;> cases hbase : base queryIndex <;>
          simp [toOriginal, FiniteUnambiguousFBDD.Walk.queryEvents,
            affinePaddedRestrictBy, FiniteUFBDDNode.affinePaddedRestrictBy,
            FiniteUFBDDNode.queryEvent?, hnode, hmask, hbase, ih]
    | choice children =>
        simp [toOriginal, FiniteUnambiguousFBDD.Walk.queryEvents,
          affinePaddedRestrictBy, FiniteUFBDDNode.affinePaddedRestrictBy,
          FiniteUFBDDNode.queryEvent?, hnode, ih]
    | sink =>
        simp [FiniteUnambiguousFBDD.Edge, affinePaddedRestrictBy,
          FiniteUFBDDNode.affinePaddedRestrictBy,
          FiniteUFBDDNode.HasChild, hnode] at edge

/-- Affine padding preserves the query trace exactly. -/
theorem toOriginal_queryTrace
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {base mask : Fin n -> Bool} {source target : B.Vertex}
    (walk : (B.affinePaddedRestrictBy base mask).Walk source target) :
    (toOriginal (B := B) (base := base) (mask := mask) walk).queryTrace =
      walk.queryTrace := by
  simp [FiniteUnambiguousFBDD.Walk.queryTrace, toOriginal_queryEvents]

/-- Affine padding preserves the set of queried coordinates exactly. -/
theorem toOriginal_queryVars
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {base mask : Fin n -> Bool} {source target : B.Vertex}
    (walk : (B.affinePaddedRestrictBy base mask).Walk source target) :
    (toOriginal (B := B) (base := base) (mask := mask) walk).queryVars =
      walk.queryVars := by
  simp [FiniteUnambiguousFBDD.Walk.queryVars, toOriginal_queryTrace]

end AffinePaddedRestrictionWalk

/-- Exact acceptance semantics of an affine padded restriction. -/
theorem affinePaddedRestrictBy_accepts_iff
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (base mask input : Fin n -> Bool) :
    (B.affinePaddedRestrictBy base mask).Accepts input <->
      B.Accepts (maskedInput base mask input) := by
  constructor
  · rintro ⟨path⟩
    refine ⟨⟨AffinePaddedRestrictionWalk.toOriginal
      (B := B) (base := base) (mask := mask) path.walk, ?_⟩⟩
    exact (AffinePaddedRestrictionWalk.toOriginal_compatible_iff
      (B := B) (base := base) (mask := mask) input path.walk).mp
        path.compatible
  · rintro ⟨path⟩
    let restrictedWalk := AffinePaddedRestrictionWalk.ofOriginalCompatible
      (B := B) (base := base) (mask := mask)
      input path.walk path.compatible
    refine ⟨⟨restrictedWalk, ?_⟩⟩
    exact AffinePaddedRestrictionWalk.ofOriginalCompatible_compatible
      (B := B) (base := base) (mask := mask)
      input path.walk path.compatible

/-- Exact rational-indicator semantics of affine padded restriction. -/
theorem affinePaddedRestrictBy_ratAcceptanceIndicator_eq_maskedInput
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (base mask input : Fin n -> Bool) :
    (B.affinePaddedRestrictBy base mask).ratAcceptanceIndicator input =
      B.ratAcceptanceIndicator (maskedInput base mask input) := by
  classical
  unfold ratAcceptanceIndicator
  rw [B.affinePaddedRestrictBy_accepts_iff base mask input]

/-- Affine padded restriction preserves syntactic read-once. -/
theorem affinePaddedRestrictBy_isSyntacticallyReadOnce
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (base mask : Fin n -> Bool) (hreadOnce : B.IsSyntacticallyReadOnce) :
    (B.affinePaddedRestrictBy base mask).IsSyntacticallyReadOnce := by
  intro target walk
  rw [← AffinePaddedRestrictionWalk.toOriginal_queryTrace
    (B := B) (base := base) (mask := mask) walk]
  exact hreadOnce target
    (AffinePaddedRestrictionWalk.toOriginal
      (B := B) (base := base) (mask := mask) walk)

/-- Affine padded restriction preserves unambiguity. -/
theorem affinePaddedRestrictBy_isUnambiguous
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (base mask : Fin n -> Bool) (hunambiguous : B.IsUnambiguous) :
    (B.affinePaddedRestrictBy base mask).IsUnambiguous := by
  intro input left right hleft hright
  apply AffinePaddedRestrictionWalk.toOriginal_injective
    (B := B) (base := base) (mask := mask)
  exact hunambiguous (maskedInput base mask input)
    (AffinePaddedRestrictionWalk.toOriginal
      (B := B) (base := base) (mask := mask) left)
    (AffinePaddedRestrictionWalk.toOriginal
      (B := B) (base := base) (mask := mask) right)
    ((AffinePaddedRestrictionWalk.toOriginal_compatible_iff
      (B := B) (base := base) (mask := mask) input left).mp hleft)
    ((AffinePaddedRestrictionWalk.toOriginal_compatible_iff
      (B := B) (base := base) (mask := mask) input right).mp hright)

/-- A full-read premise transfers to every affine padded restriction. -/
theorem affinePaddedRestrictBy_acceptingPath_queryVars_eq_univ
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (base mask : Fin n -> Bool)
    (hreadsAll : forall input (path : B.AcceptingPath input),
      path.walk.queryVars = Finset.univ)
    (input : Fin n -> Bool)
    (path : (B.affinePaddedRestrictBy base mask).AcceptingPath input) :
    path.walk.queryVars = Finset.univ := by
  let originalPath : B.AcceptingPath (maskedInput base mask input) := {
    walk := AffinePaddedRestrictionWalk.toOriginal
      (B := B) (base := base) (mask := mask) path.walk
    compatible := (AffinePaddedRestrictionWalk.toOriginal_compatible_iff
      (B := B) (base := base) (mask := mask) input path.walk).mp
        path.compatible
  }
  rw [← AffinePaddedRestrictionWalk.toOriginal_queryVars
    (B := B) (base := base) (mask := mask) path.walk]
  exact hreadsAll (maskedInput base mask input) originalPath

end FiniteUnambiguousFBDD

/-! ## Exact recursive masked composition -/

/-- One affine restriction round. -/
structure AffineRestrictionRound (n : Nat) where
  base : Fin n -> Bool
  mask : Fin n -> Bool

/-- Apply a list of masked rounds from the outside inward. -/
def applyAffineRestrictionRounds {n : Nat} :
    List (AffineRestrictionRound n) -> (Fin n -> Bool) -> Fin n -> Bool
  | [], input => input
  | round :: rounds, input =>
      maskedInput round.base round.mask
        (applyAffineRestrictionRounds rounds input)

namespace FiniteUnambiguousFBDD

/-- Iteratively transform a program by the listed affine padded rounds. -/
def affinePaddedRestrictByRounds {n : Nat} (B : FiniteUnambiguousFBDD n) :
    List (AffineRestrictionRound n) -> FiniteUnambiguousFBDD n
  | [] => B
  | round :: rounds =>
      (B.affinePaddedRestrictBy round.base round.mask)
        |>.affinePaddedRestrictByRounds rounds

/-- Iterated affine padding computes the exact recursively masked input. -/
theorem affinePaddedRestrictByRounds_ratAcceptanceIndicator_eq
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (rounds : List (AffineRestrictionRound n)) (input : Fin n -> Bool) :
    (B.affinePaddedRestrictByRounds rounds).ratAcceptanceIndicator input =
      B.ratAcceptanceIndicator (applyAffineRestrictionRounds rounds input) := by
  induction rounds generalizing B with
  | nil => rfl
  | cons round rounds ih =>
      rw [affinePaddedRestrictByRounds, ih]
      exact B.affinePaddedRestrictBy_ratAcceptanceIndicator_eq_maskedInput
        round.base round.mask (applyAffineRestrictionRounds rounds input)

/-- Iterated affine padding preserves the vertex count. -/
theorem affinePaddedRestrictByRounds_vertex_card
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (rounds : List (AffineRestrictionRound n)) :
    @Fintype.card (B.affinePaddedRestrictByRounds rounds).Vertex
        (B.affinePaddedRestrictByRounds rounds).vertexFintype =
      @Fintype.card B.Vertex B.vertexFintype := by
  induction rounds generalizing B with
  | nil => rfl
  | cons round rounds ih =>
      rw [affinePaddedRestrictByRounds, ih]
      exact B.affinePaddedRestrictBy_vertex_card round.base round.mask

/-- Iterated affine padding preserves syntactic read-once. -/
theorem affinePaddedRestrictByRounds_isSyntacticallyReadOnce
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (rounds : List (AffineRestrictionRound n))
    (hreadOnce : B.IsSyntacticallyReadOnce) :
    (B.affinePaddedRestrictByRounds rounds).IsSyntacticallyReadOnce := by
  induction rounds generalizing B with
  | nil => exact hreadOnce
  | cons round rounds ih =>
      exact ih (B := B.affinePaddedRestrictBy round.base round.mask)
        (B.affinePaddedRestrictBy_isSyntacticallyReadOnce
          round.base round.mask hreadOnce)

/-- Iterated affine padding preserves unambiguity. -/
theorem affinePaddedRestrictByRounds_isUnambiguous
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (rounds : List (AffineRestrictionRound n))
    (hunambiguous : B.IsUnambiguous) :
    (B.affinePaddedRestrictByRounds rounds).IsUnambiguous := by
  induction rounds generalizing B with
  | nil => exact hunambiguous
  | cons round rounds ih =>
      exact ih (B := B.affinePaddedRestrictBy round.base round.mask)
        (B.affinePaddedRestrictBy_isUnambiguous
          round.base round.mask hunambiguous)

/-- Iterated affine padding preserves a full-read premise. -/
theorem affinePaddedRestrictByRounds_acceptingPath_queryVars_eq_univ
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (rounds : List (AffineRestrictionRound n))
    (hreadsAll : forall input (path : B.AcceptingPath input),
      path.walk.queryVars = Finset.univ) :
    forall input
      (path : (B.affinePaddedRestrictByRounds rounds).AcceptingPath input),
        path.walk.queryVars = Finset.univ := by
  induction rounds generalizing B with
  | nil => exact hreadsAll
  | cons round rounds ih =>
      exact ih (B := B.affinePaddedRestrictBy round.base round.mask)
        (B.affinePaddedRestrictBy_acceptingPath_queryVars_eq_univ
          round.base round.mask hreadsAll)

/-- The existing full one-round theorem applies uniformly after any fixed
affine prefix.  This is the exact structural hypothesis needed at every
telescoping hybrid; the vertex factor remains that of the original program. -/
theorem affinePaddedRestrictByRounds_oneRoundAverage_sub_uniformAverage_abs_le_card_mul_pow
    {n m : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed]
    [Nonempty DSeed] [Nonempty TSeed]
    (B : FiniteUnambiguousFBDD n)
    (rounds : List (AffineRestrictionRound n))
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hunambiguous : B.IsUnambiguous)
    (hreadsAll : forall input (path : B.AcceptingPath input),
      path.walk.queryVars = Finset.univ)
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool)
    (p : Rat) (hp : 0 <= p)
    (hD : FiniteBooleanBoundedIndependence.IsKWisePatternUnbiased (4 * m) D)
    (hT : FiniteBooleanBoundedIndependence.IsKWisePatternFalseBiased
      (2 * m) p T) :
    |finiteAverage (fun seed : DSeed × TSeed =>
        finiteAverage (fun uniform : Fin n -> Bool =>
          (B.affinePaddedRestrictByRounds rounds).ratAcceptanceIndicator
            (maskedInput (D seed.1) (T seed.2) uniform))) -
      finiteAverage
        (B.affinePaddedRestrictByRounds rounds).ratAcceptanceIndicator| <=
      (Fintype.card B.Vertex : Rat) * p ^ m := by
  have hbound :=
    (B.affinePaddedRestrictByRounds rounds).ratAcceptanceIndicator_oneRoundAverage_sub_uniformAverage_abs_le_card_mul_pow
      (B.affinePaddedRestrictByRounds_isSyntacticallyReadOnce
        rounds hreadOnce)
      (B.affinePaddedRestrictByRounds_isUnambiguous rounds hunambiguous)
      (B.affinePaddedRestrictByRounds_acceptingPath_queryVars_eq_univ
        rounds hreadsAll)
      D T p hp hD hT
  rw [B.affinePaddedRestrictByRounds_vertex_card rounds] at hbound
  exact hbound

end FiniteUnambiguousFBDD

/-! ## Model-independent finite telescoping -/

namespace FiniteRoundTelescoping

/-- A uniform adjacent-hybrid error accumulates linearly in the number of
rounds. -/
theorem abs_value_sub_initial_le_rounds_mul
    (value : Nat -> Rat) (rounds : Nat) (error : Rat)
    (hstep : forall round, round < rounds ->
      |value (round + 1) - value round| <= error) :
    |value rounds - value 0| <= (rounds : Rat) * error := by
  induction rounds with
  | zero => simp
  | succ rounds ih =>
      calc
        |value (rounds + 1) - value 0| =
            |(value (rounds + 1) - value rounds) +
              (value rounds - value 0)| := by ring_nf
        _ <= |value (rounds + 1) - value rounds| +
              |value rounds - value 0| := abs_add _ _
        _ <= error + (rounds : Rat) * error := by
          gcongr
          · exact hstep rounds (Nat.lt_succ_self rounds)
          · exact ih (fun round hround =>
              hstep round (Nat.lt_trans hround (Nat.lt_succ_self rounds)))
        _ = (rounds + 1 : Nat) * error := by
          push_cast
          ring

/-- Append an arbitrary terminal replacement cost to the accumulated hybrid
error. -/
theorem abs_initial_sub_terminal_le_rounds_mul_add
    (value : Nat -> Rat) (terminal : Rat) (rounds : Nat)
    (error tailCost : Rat)
    (hstep : forall round, round < rounds ->
      |value (round + 1) - value round| <= error)
    (htail : |value rounds - terminal| <= tailCost) :
    |value 0 - terminal| <= (rounds : Rat) * error + tailCost := by
  calc
    |value 0 - terminal| =
        |(value 0 - value rounds) + (value rounds - terminal)| := by ring_nf
    _ <= |value 0 - value rounds| + |value rounds - terminal| := abs_add _ _
    _ <= (rounds : Rat) * error + tailCost := by
      gcongr
      simpa [abs_sub_comm] using
        abs_value_sub_initial_le_rounds_mul value rounds error hstep

/-- DPTW-shaped scalar specialization.  Supplying a per-round estimate
`S * p^m` and a zero-tail estimate `N * (1-p)^L` gives their advertised sum
without any further probabilistic assumptions. -/
theorem abs_initial_sub_zeroTail_le_dptw_shape
    (value : Nat -> Rat) (zeroTail : Rat)
    (L m : Nat) (S N p : Rat)
    (hstep : forall round, round < L ->
      |value (round + 1) - value round| <= S * p ^ m)
    (htail : |value L - zeroTail| <= N * (1 - p) ^ L) :
    |value 0 - zeroTail| <=
      (L : Rat) * S * p ^ m + N * (1 - p) ^ L := by
  have h := abs_initial_sub_terminal_le_rounds_mul_add
    value zeroTail L (S * p ^ m) (N * (1 - p) ^ L) hstep htail
  simpa [mul_assoc] using h

end FiniteRoundTelescoping

end OneTapeMagnification
end Frontier
end Pnp4
