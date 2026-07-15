import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# A grid obstruction for literal stable-group routing

This is an infrastructure/audit result, not a lower bound for the canonical
validator and not a `P != NP` theorem.

Suppose a relation circuit keeps one vertex for every query event, links
consecutive events in chronological order, and also links consecutive events
after stable grouping by work block.  On a schedule which sweeps all blocks in
each of several rounds (with either orientation in each round), the resulting
two-order routing graph contains the Cartesian grid

`pathGraph roundCount □ pathGraph blockCount`.

The theorem below is deliberately architecture-specific: a different circuit
may avoid these literal event-to-event links.  Its use is to rule out the
generic claim that local witness copies plus the two obvious consistency chains
automatically have small pathwidth.  By the standard monotonicity of pathwidth
under taking subgraphs and the exact pathwidth of rectangular grids, this
literal architecture has pathwidth at least `min roundCount blockCount` (apart
from the degenerate one-vertex convention).  Pathwidth itself is not currently
formalized in Mathlib, so the checked development stops at exact graph
containment and an explicit paired contraction certificate rather than a
pathwidth inequality.

No theorem in this file derives this synthetic full-sweep graph from an actual
canonical one-tape trace.  That connection is a separate, still-open geometry
obligation.

Primary references for the external graph-width facts:

* N. G. Kinnersley, *The vertex separation number of a graph equals its
  path-width*, Information Processing Letters 42(6), 1992.
* J. Ellis, R. Warren, *Lower bounds on the pathwidth of some grid-like
  graphs*, Discrete Applied Mathematics 156(5), 2008, Theorem 4.1.
-/

/-- An event is identified by its sweep round and its work-block label. -/
abbrev StableRoutingVertex (roundCount blockCount : Nat) :=
  Fin roundCount × Fin blockCount

/-- Position of an event in chronological sweep order.  A `true` row is read
right-to-left and a `false` row is read left-to-right. -/
def stableRoutingChronologicalIndex {roundCount blockCount : Nat}
    (reverseRow : Fin roundCount → Bool)
    (vertex : StableRoutingVertex roundCount blockCount) : Nat :=
  vertex.1.val * blockCount +
    if reverseRow vertex.1 then
      blockCount - 1 - vertex.2.val
    else
      vertex.2.val

/-- Position of the same event after stable grouping by block: first the block
label, then the original round order inside that block. -/
def stableRoutingGroupedIndex {roundCount blockCount : Nat}
    (vertex : StableRoutingVertex roundCount blockCount) : Nat :=
  vertex.2.val * roundCount + vertex.1.val

/-- Directed successor relation contributed by either of the two orders. -/
def stableRoutingSuccessor {roundCount blockCount : Nat}
    (reverseRow : Fin roundCount → Bool)
    (left right : StableRoutingVertex roundCount blockCount) : Prop :=
  stableRoutingChronologicalIndex reverseRow left + 1 =
      stableRoutingChronologicalIndex reverseRow right ∨
    stableRoutingGroupedIndex left + 1 = stableRoutingGroupedIndex right

/-- The undirected graph obtained by sharing event vertices between the
chronological validation chain and the stable-grouped validation chain. -/
def stableTwoOrderRoutingGraph {roundCount blockCount : Nat}
    (reverseRow : Fin roundCount → Bool) :
    SimpleGraph (StableRoutingVertex roundCount blockCount) :=
  SimpleGraph.fromRel (stableRoutingSuccessor reverseRow)

/-- Adjacent blocks in one sweep round are adjacent in the chronological part
of the two-order routing graph, independently of that round's orientation. -/
theorem stableTwoOrderRoutingGraph_adj_horizontal
    {roundCount blockCount : Nat}
    (reverseRow : Fin roundCount → Bool) (round : Fin roundCount)
    {left right : Fin blockCount}
    (hadj : (SimpleGraph.pathGraph blockCount).Adj left right) :
    (stableTwoOrderRoutingGraph reverseRow).Adj
      (round, left) (round, right) := by
  rw [stableTwoOrderRoutingGraph, SimpleGraph.fromRel_adj]
  constructor
  · intro heq
    have : left = right := congrArg Prod.snd heq
    exact hadj.ne this
  · unfold stableRoutingSuccessor
    rw [SimpleGraph.pathGraph_adj] at hadj
    rcases hadj with hadj | hadj
    · by_cases hreverse : reverseRow round = true
      · right
        left
        simp [stableRoutingChronologicalIndex, hreverse]
        omega
      · left
        left
        have hfalse : reverseRow round = false := Bool.eq_false_of_not_eq_true hreverse
        simp [stableRoutingChronologicalIndex, hfalse]
        omega
    · by_cases hreverse : reverseRow round = true
      · left
        left
        simp [stableRoutingChronologicalIndex, hreverse]
        omega
      · right
        left
        have hfalse : reverseRow round = false := Bool.eq_false_of_not_eq_true hreverse
        simp [stableRoutingChronologicalIndex, hfalse]
        omega

/-- Consecutive rounds at one fixed block are adjacent in the stable-grouped
part of the two-order routing graph. -/
theorem stableTwoOrderRoutingGraph_adj_vertical
    {roundCount blockCount : Nat}
    (reverseRow : Fin roundCount → Bool) (block : Fin blockCount)
    {upper lower : Fin roundCount}
    (hadj : (SimpleGraph.pathGraph roundCount).Adj upper lower) :
    (stableTwoOrderRoutingGraph reverseRow).Adj
      (upper, block) (lower, block) := by
  rw [stableTwoOrderRoutingGraph, SimpleGraph.fromRel_adj]
  constructor
  · intro heq
    have : upper = lower := congrArg Prod.fst heq
    exact hadj.ne this
  · unfold stableRoutingSuccessor
    rw [SimpleGraph.pathGraph_adj] at hadj
    rcases hadj with hadj | hadj
    · left
      right
      simp [stableRoutingGroupedIndex]
      omega
    · right
      right
      simp [stableRoutingGroupedIndex]
      omega

/-- Main checked obstruction: every rectangular grid edge is present in the
literal chronological-plus-stable-grouped routing graph. -/
theorem stableRoutingGrid_le_twoOrderRoutingGraph
    {roundCount blockCount : Nat}
    (reverseRow : Fin roundCount → Bool) :
    SimpleGraph.pathGraph roundCount □ SimpleGraph.pathGraph blockCount ≤
      stableTwoOrderRoutingGraph reverseRow := by
  rintro ⟨leftRound, leftBlock⟩ ⟨rightRound, rightBlock⟩ hadj
  rw [SimpleGraph.boxProd_adj] at hadj
  rcases hadj with hadj | hadj
  · rcases hadj with ⟨hround, hblock⟩
    change leftBlock = rightBlock at hblock
    subst rightBlock
    exact stableTwoOrderRoutingGraph_adj_vertical
      reverseRow leftBlock hround
  · rcases hadj with ⟨hblock, hround⟩
    change leftRound = rightRound at hround
    subst rightRound
    exact stableTwoOrderRoutingGraph_adj_horizontal
      reverseRow leftRound hblock

/-! ## Local copies do not remove this literal obstruction

One may split every event into a chronological copy and a grouped copy and
join the pair by one equality/consistency edge.  Contracting all such matching
edges recovers the shared-event graph above.  Mathlib does not currently expose
a graph-minor API, so `HasPairedContractionModel` records exactly the two facts
needed for this particular contraction: every pair is joined, and every small
edge has a lift entirely on one side.
-/

/-- Directed edges in the split-copy architecture.  `false` is the
chronological copy and `true` is the stable-grouped copy. -/
def splitStableRoutingSuccessor {roundCount blockCount : Nat}
    (reverseRow : Fin roundCount → Bool)
    (left right : Bool × StableRoutingVertex roundCount blockCount) : Prop :=
  (left.1 = false ∧ right.1 = false ∧
      stableRoutingChronologicalIndex reverseRow left.2 + 1 =
        stableRoutingChronologicalIndex reverseRow right.2) ∨
    (left.1 = true ∧ right.1 = true ∧
      stableRoutingGroupedIndex left.2 + 1 =
        stableRoutingGroupedIndex right.2) ∨
    (left.1 = false ∧ right.1 = true ∧ left.2 = right.2)

/-- Two disjoint order chains, with one local consistency edge joining the two
copies of each event. -/
def splitStableTwoOrderRoutingGraph {roundCount blockCount : Nat}
    (reverseRow : Fin roundCount → Bool) :
    SimpleGraph (Bool × StableRoutingVertex roundCount blockCount) :=
  SimpleGraph.fromRel (splitStableRoutingSuccessor reverseRow)

/-- The two local copies of each event are joined by a consistency edge. -/
theorem splitStableTwoOrderRoutingGraph_adj_pair
    {roundCount blockCount : Nat}
    (reverseRow : Fin roundCount → Bool)
    (vertex : StableRoutingVertex roundCount blockCount) :
    (splitStableTwoOrderRoutingGraph reverseRow).Adj
      (false, vertex) (true, vertex) := by
  rw [splitStableTwoOrderRoutingGraph, SimpleGraph.fromRel_adj]
  simp [splitStableRoutingSuccessor]

/-- A chronological successor edge lifts to the chronological-copy side. -/
theorem splitStableTwoOrderRoutingGraph_adj_chronological
    {roundCount blockCount : Nat}
    (reverseRow : Fin roundCount → Bool)
    {left right : StableRoutingVertex roundCount blockCount}
    (hsucc : stableRoutingChronologicalIndex reverseRow left + 1 =
      stableRoutingChronologicalIndex reverseRow right) :
    (splitStableTwoOrderRoutingGraph reverseRow).Adj
      (false, left) (false, right) := by
  rw [splitStableTwoOrderRoutingGraph, SimpleGraph.fromRel_adj]
  constructor
  · intro heq
    have hvertex : left = right := congrArg (fun value => value.2) heq
    subst right
    omega
  · left
    left
    exact ⟨rfl, rfl, hsucc⟩

/-- A stable-grouped successor edge lifts to the grouped-copy side. -/
theorem splitStableTwoOrderRoutingGraph_adj_grouped
    {roundCount blockCount : Nat}
    (reverseRow : Fin roundCount → Bool)
    {left right : StableRoutingVertex roundCount blockCount}
    (hsucc : stableRoutingGroupedIndex left + 1 =
      stableRoutingGroupedIndex right) :
    (splitStableTwoOrderRoutingGraph reverseRow).Adj
      (true, left) (true, right) := by
  rw [splitStableTwoOrderRoutingGraph, SimpleGraph.fromRel_adj]
  constructor
  · intro heq
    have hvertex : left = right := congrArg (fun value => value.2) heq
    subst right
    omega
  · left
    right
    left
    exact ⟨rfl, rfl, hsucc⟩

/-- A concrete paired-branch-set contraction certificate.  Contracting each
edge `(false,v)--(true,v)` makes every lifted edge an edge on `v`. -/
def StableRoutingHasPairedContractionModel {Vertex : Type*}
    (small : SimpleGraph Vertex) (large : SimpleGraph (Bool × Vertex)) : Prop :=
  (∀ vertex, large.Adj (false, vertex) (true, vertex)) ∧
    ∀ ⦃left right⦄, small.Adj left right →
      ∃ side : Bool, large.Adj (side, left) (side, right)

/-- Every shared-event routing edge lifts to one of the two copy layers. -/
theorem stableTwoOrderRoutingGraph_hasPairedContractionModel
    {roundCount blockCount : Nat}
    (reverseRow : Fin roundCount → Bool) :
    StableRoutingHasPairedContractionModel
      (stableTwoOrderRoutingGraph (blockCount := blockCount) reverseRow)
      (splitStableTwoOrderRoutingGraph (blockCount := blockCount) reverseRow) := by
  constructor
  · exact splitStableTwoOrderRoutingGraph_adj_pair reverseRow
  · intro left right hadj
    rw [stableTwoOrderRoutingGraph, SimpleGraph.fromRel_adj] at hadj
    rcases hadj.2 with hsucc | hsucc
    · rcases hsucc with hchrono | hgrouped
      · exact ⟨false,
          splitStableTwoOrderRoutingGraph_adj_chronological
            reverseRow hchrono⟩
      · exact ⟨true,
          splitStableTwoOrderRoutingGraph_adj_grouped reverseRow hgrouped⟩
    · rcases hsucc with hchrono | hgrouped
      · exact ⟨false,
          (splitStableTwoOrderRoutingGraph_adj_chronological
            reverseRow hchrono).symm⟩
      · exact ⟨true,
          (splitStableTwoOrderRoutingGraph_adj_grouped
            reverseRow hgrouped).symm⟩

/-- The rectangular grid therefore has the same paired contraction model in
the local-copy architecture.  Externally, contracting the pair edges exhibits
the grid as a minor. -/
theorem stableRoutingGrid_hasPairedContractionModel
    {roundCount blockCount : Nat}
    (reverseRow : Fin roundCount → Bool) :
    StableRoutingHasPairedContractionModel
      (SimpleGraph.pathGraph roundCount □ SimpleGraph.pathGraph blockCount)
      (splitStableTwoOrderRoutingGraph (blockCount := blockCount) reverseRow) := by
  refine ⟨splitStableTwoOrderRoutingGraph_adj_pair reverseRow, ?_⟩
  intro left right hadj
  exact
    (stableTwoOrderRoutingGraph_hasPairedContractionModel reverseRow).2
      (stableRoutingGrid_le_twoOrderRoutingGraph reverseRow hadj)

end OneTapeMagnification
end Frontier
end Pnp4
