import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.ActualSerpentineRoutingGridRealization
import Pnp4.Frontier.OneTapeMagnification.CanonicalAlphaFunctionalRelation
import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalUFBDD

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# The serpentine routing grid does not force canonical-validator size

The concrete serpentine machine has arbitrarily large literal two-order event
grids, but its transition function ignores the input and its halting map is
everywhere `none`.  Consequently it has no eligible accepting canonical alpha,
its canonical functional relation is empty, and a two-sink query-free uFBDD
realizes that relation exactly.  The installed mandatory canonical selector is
also query-semantically empty and has exactly three vertices.

Thus the event-grid theorem alone cannot imply a size lower bound for an exact
canonical validator.  A successful geometric route must additionally show
that many routed events are semantically essential for an accepting target and
must survive as distinct features of every exact realizer.  This file records
the concrete counterarchitecture; it is an infrastructure result, not a lower
bound and not P-vs-NP mainline progress.
-/

namespace SerpentineCanonicalCounterarchitecture

local instance serpentineSweepMachineStateDecidableEq
    {K : Nat} (hK : 0 < K) :
    DecidableEq (serpentineSweepMachine K hK).State :=
  inferInstanceAs (DecidableEq (Bool × Fin K))

/-! ## The accepting canonical index is empty -/

@[simp]
theorem cachedSerpentineSweepMachine_halt_eq_none
    {K : Nat} (hK : 0 < K)
    (state : (cachedInputMachine (serpentineSweepMachine K hK)).State) :
    (cachedInputMachine (serpentineSweepMachine K hK)).halt state = none := by
  cases state with
  | none => rfl
  | some value =>
      rcases value with ⟨control, cached⟩
      rfl

/-- No ambient alpha can satisfy the accepting-terminal eligibility condition
for the serpentine machine. -/
theorem noBuiltRejectingGuardedCanonicalAlphaIndex
    {K : Nat} (hK : 0 < K) (T b : Nat)
    (index : BuiltRejectingGuardedCanonicalAlphaIndex
      (serpentineSweepMachine K hK) T b) : False := by
  have hterminal := index.2.2.2
  rw [cachedSerpentineSweepMachine_halt_eq_none hK] at hterminal
  cases hterminal

/-- No cached serpentine run can be accepting, at any time and on any input. -/
theorem cachedSerpentineSweepMachine_run_not_accepting
    {K : Nat} (hK : 0 < K) (input : List Bool) (time : Nat) :
    ¬ IsAccepting (cachedInputMachine (serpentineSweepMachine K hK))
      (run (cachedInputMachine (serpentineSweepMachine K hK)) input time) := by
  unfold IsAccepting outcome
  rw [cachedSerpentineSweepMachine_halt_eq_none hK]
  simp

/-- The finite carrier used by the canonical witness encoder has cardinality
zero for the serpentine machine. -/
theorem card_builtRejectingGuardedCanonicalAlphaIndex_serpentine_eq_zero
    {K : Nat} (hK : 0 < K) (T b : Nat) :
    Fintype.card (BuiltRejectingGuardedCanonicalAlphaIndex
      (serpentineSweepMachine K hK) T b) = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  exact ⟨noBuiltRejectingGuardedCanonicalAlphaIndex hK T b⟩

/-- The optimal encoded right block is consequently empty. -/
theorem canonicalAlphaWitnessBitWidth_serpentine_eq_zero
    {K : Nat} (hK : 0 < K) (T b : Nat) :
    canonicalAlphaWitnessBitWidth (serpentineSweepMachine K hK) T b = 0 := by
  unfold canonicalAlphaWitnessBitWidth
  rw [card_builtRejectingGuardedCanonicalAlphaIndex_serpentine_eq_zero hK]
  norm_num [Nat.clog]

/-- Strongest semantic obstruction: every instance of the concrete canonical
functional relation is false, independently of the input and witness word. -/
theorem finiteRejectingGuardedCanonicalFunctionalRelation_serpentine_false
    {K : Nat} (hK : 0 < K) (n T b : Nat)
    (input : Fin n -> Bool)
    (code : Fin (canonicalAlphaWitnessBitWidth
      (serpentineSweepMachine K hK) T b) -> Bool) :
    ¬ finiteRejectingGuardedCanonicalFunctionalRelation
      (serpentineSweepMachine K hK) n T b input code := by
  unfold finiteRejectingGuardedCanonicalFunctionalRelation
  unfold FiniteLayeredQueryProgramFamily.EncodedAcceptingRelation
  rintro ⟨index, _hcode, _heval⟩
  exact noBuiltRejectingGuardedCanonicalAlphaIndex hK T b index

/-! ## An exact two-vertex joint realizer -/

/-- Two disconnected sinks.  `false` is the start and `true` is the accepting
sink, so there is no accepting walk and no query event. -/
def twoSinkRejectUFBDD (n : Nat) : FiniteUnambiguousFBDD n where
  Vertex := Bool
  vertexFintype := inferInstance
  vertexDecidableEq := inferInstance
  start := false
  accept := true
  node := fun _ => .sink
  accept_sink := rfl
  rank := fun _ => 0
  rank_child := by
    intro source target hchild
    simp [FiniteUFBDDNode.HasChild] at hchild

/-- Every formal walk in the disconnected diagram is stationary. -/
theorem twoSinkRejectUFBDD_walk_eq
    {n : Nat} {source target : (twoSinkRejectUFBDD n).Vertex}
    (walk : (twoSinkRejectUFBDD n).Walk source target) :
    source = target := by
  induction walk with
  | nil => rfl
  | @cons source middle target edge tail ih =>
      simp [FiniteUnambiguousFBDD.Edge, twoSinkRejectUFBDD,
        FiniteUFBDDNode.HasChild] at edge

@[simp]
theorem twoSinkRejectUFBDD_not_accepts
    {n : Nat} (input : Fin n -> Bool) :
    ¬ (twoSinkRejectUFBDD n).Accepts input := by
  intro haccepts
  rcases haccepts with ⟨path⟩
  have heq := twoSinkRejectUFBDD_walk_eq path.walk
  change false = true at heq
  cases heq

theorem twoSinkRejectUFBDD_isSyntacticallyReadOnce (n : Nat) :
    (twoSinkRejectUFBDD n).IsSyntacticallyReadOnce := by
  intro target walk
  cases walk with
  | nil => simp [FiniteUnambiguousFBDD.Walk.queryTrace,
      FiniteUnambiguousFBDD.Walk.queryEvents]
  | @cons source middle target edge tail =>
      simp [FiniteUnambiguousFBDD.Edge, twoSinkRejectUFBDD,
        FiniteUFBDDNode.HasChild] at edge

theorem twoSinkRejectUFBDD_isUnambiguous (n : Nat) :
    (twoSinkRejectUFBDD n).IsUnambiguous := by
  intro input left right hleft hright
  have heq := twoSinkRejectUFBDD_walk_eq left
  change false = true at heq
  cases heq

@[simp]
theorem twoSinkRejectUFBDD_vertex_card (n : Nat) :
    @Fintype.card (twoSinkRejectUFBDD n).Vertex
      (twoSinkRejectUFBDD n).vertexFintype = 2 := by
  rfl

/-- The two disconnected sinks realize the actual encoded canonical relation,
not merely an extensionally related acceptance language. -/
theorem twoSinkRejectUFBDD_realizes_serpentineCanonicalRelation
    {K : Nat} (hK : 0 < K) (n T b : Nat) :
    FiniteUnambiguousFBDD.RealizesFiniteRejectingGuardedCanonicalFunctionalRelation
      (serpentineSweepMachine K hK)
      (twoSinkRejectUFBDD
      (n + canonicalAlphaWitnessBitWidth
        (serpentineSweepMachine K hK) T b)) := by
  intro input code
  constructor
  · intro haccepts
    exact (twoSinkRejectUFBDD_not_accepts
      (Fin.addCases input code) haccepts).elim
  · intro hrelation
    exact (finiteRejectingGuardedCanonicalFunctionalRelation_serpentine_false
      hK n T b input code hrelation).elim

/-! ## The installed mandatory selector is tiny as well -/

/-- The real mandatory canonical selector rejects every Boolean input. -/
theorem mandatoryCanonicalUFBDD_serpentine_not_accepts
    {K : Nat} (hK : 0 < K) (n T b : Nat)
    (input : Fin n -> Bool) :
    ¬ (mandatoryCanonicalUFBDD
      (serpentineSweepMachine K hK) n T b).Accepts input := by
  intro haccepts
  have heval :=
    (FiniteLayeredQueryProgramFamily.selectorFBDD_accepts_iff_eval_eq_true
      (mandatoryFiniteRejectingGuardedCanonicalFamily
        (serpentineSweepMachine K hK) n T b) input).1 haccepts
  obtain ⟨index, _hindex⟩ :=
    (FiniteLayeredQueryProgramFamily.eval_eq_true_iff
      (mandatoryFiniteRejectingGuardedCanonicalFamily
        (serpentineSweepMachine K hK) n T b) input).1 heval
  exact noBuiltRejectingGuardedCanonicalAlphaIndex hK T b index

/-- Exact size of the installed selector: one root and two sinks, with no
component slots because the eligible index carrier is empty. -/
theorem mandatoryCanonicalUFBDD_serpentine_vertex_card
    {K : Nat} (hK : 0 < K) (n T b : Nat) :
    @Fintype.card
        (mandatoryCanonicalUFBDD
          (serpentineSweepMachine K hK) n T b).Vertex
        (mandatoryCanonicalUFBDD
          (serpentineSweepMachine K hK) n T b).vertexFintype = 3 := by
  rw [mandatoryCanonicalUFBDD_vertex_card]
  have hsum :
      (∑ index : BuiltRejectingGuardedCanonicalAlphaIndex
          (serpentineSweepMachine K hK) T b,
        (n + 1) *
          (mandatoryBuiltRejectingGuardedCanonicalComponent
            (serpentineSweepMachine K hK) n index).width) = 0 := by
    classical
    apply Finset.sum_eq_zero
    intro index _hmem
    exact (noBuiltRejectingGuardedCanonicalAlphaIndex hK T b index).elim
  rw [hsum]

/-- For a genuine rectangular grid, its event carrier cannot even inject into
the vertex carrier of the real mandatory selector. -/
theorem no_injective_serpentineGrid_to_mandatoryCanonicalUFBDD
    {R K : Nat} (hR : 2 ≤ R) (hK : 2 ≤ K)
    (n T b : Nat) :
    ¬ ∃ embedding : StableRoutingVertex R K ->
        (mandatoryCanonicalUFBDD
          (serpentineSweepMachine K (by omega)) n T b).Vertex,
      Function.Injective embedding := by
  rintro ⟨embedding, hinjective⟩
  have hcard := Fintype.card_le_of_injective embedding hinjective
  rw [mandatoryCanonicalUFBDD_serpentine_vertex_card
    (by omega : 0 < K) n T b] at hcard
  have hsmall : R * K ≤ 3 := by
    simpa [StableRoutingVertex] using hcard
  have hlarge : 4 ≤ R * K := by
    calc
      4 = 2 * 2 := by omega
      _ ≤ R * K := Nat.mul_le_mul hR hK
  omega

/-- The same parameters simultaneously exhibit the large literal grid and a
two-vertex exact realizer of the encoded canonical functional relation. -/
theorem actualSerpentineGrid_with_twoVertexExactFunctionalRealizer
    {R K : Nat} (hK : 0 < K) (input : List Bool) :
    (SimpleGraph.pathGraph R □ SimpleGraph.pathGraph K ≤
      actualSerpentineTwoOrderRoutingGraph hK input) ∧
    FiniteUnambiguousFBDD.RealizesFiniteRejectingGuardedCanonicalFunctionalRelation
      (serpentineSweepMachine K hK)
      (twoSinkRejectUFBDD
        (input.length + canonicalAlphaWitnessBitWidth
          (serpentineSweepMachine K hK) (R * K) 1)) ∧
    @Fintype.card
        (twoSinkRejectUFBDD
          (input.length + canonicalAlphaWitnessBitWidth
            (serpentineSweepMachine K hK) (R * K) 1)).Vertex
        (twoSinkRejectUFBDD
          (input.length + canonicalAlphaWitnessBitWidth
            (serpentineSweepMachine K hK) (R * K) 1)).vertexFintype = 2 := by
  constructor
  · exact stableRoutingGrid_le_actualSerpentineTwoOrderRoutingGraph hK input
  constructor
  · exact twoSinkRejectUFBDD_realizes_serpentineCanonicalRelation
      hK input.length (R * K) 1
  · exact twoSinkRejectUFBDD_vertex_card _

/-- Concrete capstone: the literal actual-event graph contains the full grid,
while the actual mandatory canonical validator has three vertices and cannot
contain distinct representatives of those events. -/
theorem actualSerpentineGrid_with_tinyMandatoryCanonicalValidator
    {R K : Nat} (hR : 2 ≤ R) (hK : 2 ≤ K)
    (input : List Bool) :
    (SimpleGraph.pathGraph R □ SimpleGraph.pathGraph K ≤
      actualSerpentineTwoOrderRoutingGraph
        (by omega : 0 < K) input) ∧
    (@Fintype.card
        (mandatoryCanonicalUFBDD
          (serpentineSweepMachine K (by omega)) input.length (R * K) 1).Vertex
        (mandatoryCanonicalUFBDD
          (serpentineSweepMachine K (by omega)) input.length (R * K) 1).vertexFintype = 3) ∧
    ¬ ∃ embedding : StableRoutingVertex R K ->
        (mandatoryCanonicalUFBDD
          (serpentineSweepMachine K (by omega))
            input.length (R * K) 1).Vertex,
      Function.Injective embedding := by
  constructor
  · exact stableRoutingGrid_le_actualSerpentineTwoOrderRoutingGraph
      (by omega : 0 < K) input
  constructor
  · exact mandatoryCanonicalUFBDD_serpentine_vertex_card
      (by omega : 0 < K) input.length (R * K) 1
  · exact no_injective_serpentineGrid_to_mandatoryCanonicalUFBDD
      hR hK input.length (R * K) 1

end SerpentineCanonicalCounterarchitecture

end OneTapeMagnification
end Frontier
end Pnp4
