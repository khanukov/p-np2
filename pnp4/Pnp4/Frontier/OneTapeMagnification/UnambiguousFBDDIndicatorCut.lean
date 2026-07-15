import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDPathCut

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

namespace FiniteUnambiguousFBDD

/-!
# Input-compatible indicator cuts for finite unambiguous FBDDs

This file turns the pathwise filtered cut from
`UnambiguousFBDDPathCut` into a path-independent vertex predicate.  A
contributing vertex must be reachable by an input-compatible prefix, have an
input-compatible accepting suffix, query a variable in `alpha`, have exactly
`k` syntactically possible `alpha`-variables before it, and satisfy the support
filter

`alpha ⊆ preVars vertex ∪ postVars vertex`.

Unambiguity identifies the concatenation of any compatible prefix and suffix
with the selected accepting path.  Consequently the path-independent
predicate has exactly one witness whenever the selected accepting path reads
all variables in `alpha`.  This is only the semantic indicator-cut foundation;
no Fourier factorization or lower bound is asserted here.
-/

/-- The input reaches `vertex` along some compatible prefix. -/
def HasCompatiblePrefix {n : Nat} (B : FiniteUnambiguousFBDD n)
    (input : Fin n → Bool) (vertex : B.Vertex) : Prop :=
  ∃ walk : B.Walk B.start vertex, walk.Compatible input

/-- From `vertex`, the input has some compatible continuation to acceptance. -/
def HasCompatibleAcceptingSuffix {n : Nat}
    (B : FiniteUnambiguousFBDD n) (input : Fin n → Bool)
    (vertex : B.Vertex) : Prop :=
  ∃ walk : B.Walk vertex B.accept, walk.Compatible input

/-- A path-independent filtered `alpha`-cut predicate at a vertex.

The query witness says that the vertex itself queries a variable of `alpha`.
The prefix cardinality uses the global syntactic `preVars`, while the final
conjunct is the support filter required for branching programs that may skip
variables. -/
def IsFilteredAlphaCutVertex {n : Nat} (B : FiniteUnambiguousFBDD n)
    (alpha : Finset (Fin n)) (k : Nat) (vertex : B.Vertex) : Prop :=
  (∃ queryIndex : Fin n, ∃ ifFalse ifTrue : B.Vertex,
      B.node vertex = .query queryIndex ifFalse ifTrue ∧
        queryIndex ∈ alpha) ∧
    (alpha ∩ B.preVars vertex).card = k ∧
    alpha ⊆ B.preVars vertex ∪ B.postVars vertex

/-- The full input-dependent indicator predicate at a filtered cut vertex. -/
def HasFilteredAlphaCut {n : Nat} (B : FiniteUnambiguousFBDD n)
    (input : Fin n → Bool) (alpha : Finset (Fin n))
    (k : Nat) (vertex : B.Vertex) : Prop :=
  B.HasCompatiblePrefix input vertex ∧
    B.HasCompatibleAcceptingSuffix input vertex ∧
    B.IsFilteredAlphaCutVertex alpha k vertex

namespace Walk

/-- Every event in a walk really is contributed by the corresponding query
vertex. -/
theorem node_eq_query_of_mem_queryEvents
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {source target vertex : B.Vertex} {queryIndex : Fin n}
    (walk : B.Walk source target)
    (hmem : (vertex, queryIndex) ∈ walk.queryEvents) :
    ∃ ifFalse ifTrue : B.Vertex,
      B.node vertex = .query queryIndex ifFalse ifTrue := by
  induction walk with
  | nil current =>
      simp [queryEvents] at hmem
  | @cons source middle target edge tail ih =>
      cases hnode : B.node source with
      | query currentIndex ifFalse ifTrue =>
          simp only [queryEvents, hnode, FiniteUFBDDNode.queryEvent?,
            Option.toList_some, List.singleton_append,
            List.mem_cons] at hmem
          rcases hmem with hhead | htail
          · cases hhead
            exact ⟨ifFalse, ifTrue, hnode⟩
          · exact ih htail
      | choice children =>
          have htail : (vertex, queryIndex) ∈ tail.queryEvents := by
            simpa [queryEvents, hnode, FiniteUFBDDNode.queryEvent?] using hmem
          exact ih htail
      | sink =>
          simp [Edge, FiniteUFBDDNode.HasChild, hnode] at edge

/-- A walk from a query vertex to the accepting sink starts its event list
with that vertex's query. -/
theorem queryEvents_eq_cons_of_node_eq_query_to_accept
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {vertex : B.Vertex} {queryIndex : Fin n}
    {ifFalse ifTrue : B.Vertex}
    (walk : B.Walk vertex B.accept)
    (hnode : B.node vertex = .query queryIndex ifFalse ifTrue) :
    ∃ events : List (B.Vertex × Fin n),
      walk.queryEvents = (vertex, queryIndex) :: events := by
  cases walk with
  | nil current =>
      have hneq :
          (FiniteUFBDDNode.sink : FiniteUFBDDNode n B.Vertex) ≠
            .query queryIndex ifFalse ifTrue := by simp
      exact (hneq (B.accept_sink.symm.trans hnode)).elim
  | @cons source middle target edge tail =>
      refine ⟨tail.queryEvents, ?_⟩
      simp [queryEvents, hnode, FiniteUFBDDNode.queryEvent?]

end Walk

/-- A pathwise filtered cut yields compatible prefix and suffix witnesses and
the corresponding path-independent vertex predicate. -/
theorem hasFilteredAlphaCut_of_isAlphaCut
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {input : Fin n → Bool} (path : B.AcceptingPath input)
    {alpha : Finset (Fin n)} {k : Nat} {vertex : B.Vertex}
    (hcut : B.IsAlphaCut path.walk alpha k vertex) :
    B.HasFilteredAlphaCut input alpha k vertex := by
  rcases hcut with
    ⟨queryIndex, leftEvents, rightEvents, hevents,
      hqueryAlpha, hcard, hsupport⟩
  rcases Walk.split_of_queryEvents_eq_append_cons path.walk
      leftEvents rightEvents hevents with
    ⟨leftWalk, rightWalk, happend, _hleftEvents, _hrightEvents⟩
  have hcompatible :
      (leftWalk.append rightWalk).Compatible input := by
    rw [happend]
    exact path.compatible
  have hparts :=
    (Walk.compatible_append input leftWalk rightWalk).mp hcompatible
  have hmem : (vertex, queryIndex) ∈ path.walk.queryEvents := by
    rw [hevents]
    simp
  rcases path.walk.node_eq_query_of_mem_queryEvents hmem with
    ⟨ifFalse, ifTrue, hnode⟩
  exact ⟨⟨leftWalk, hparts.1⟩, ⟨rightWalk, hparts.2⟩,
    ⟨⟨queryIndex, ifFalse, ifTrue, hnode, hqueryAlpha⟩,
      hcard, hsupport⟩⟩

/-- Under unambiguity, compatible prefix and accepting-suffix witnesses at a
filtered cut vertex concatenate to the selected accepting path, hence yield
the pathwise `IsAlphaCut` predicate. -/
theorem isAlphaCut_of_hasFilteredAlphaCut
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {input : Fin n → Bool} (path : B.AcceptingPath input)
    (hunambiguous : B.IsUnambiguous)
    {alpha : Finset (Fin n)} {k : Nat} {vertex : B.Vertex}
    (hcut : B.HasFilteredAlphaCut input alpha k vertex) :
    B.IsAlphaCut path.walk alpha k vertex := by
  rcases hcut with
    ⟨⟨leftWalk, hleftCompatible⟩,
      ⟨rightWalk, hrightCompatible⟩,
      ⟨⟨queryIndex, ifFalse, ifTrue, hnode, hqueryAlpha⟩,
        hcard, hsupport⟩⟩
  have happendCompatible :
      (leftWalk.append rightWalk).Compatible input :=
    (Walk.compatible_append input leftWalk rightWalk).mpr
      ⟨hleftCompatible, hrightCompatible⟩
  have happend : leftWalk.append rightWalk = path.walk :=
    hunambiguous input (leftWalk.append rightWalk) path.walk
      happendCompatible path.compatible
  rcases rightWalk.queryEvents_eq_cons_of_node_eq_query_to_accept hnode with
    ⟨rightEvents, hrightEvents⟩
  refine ⟨queryIndex, leftWalk.queryEvents, rightEvents, ?_,
    hqueryAlpha, hcard, hsupport⟩
  rw [← happend, Walk.queryEvents_append, hrightEvents]

/-- Relative to the unique accepting path, the semantic indicator predicate
is exactly the existing pathwise filtered-cut predicate. -/
theorem hasFilteredAlphaCut_iff_isAlphaCut
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {input : Fin n → Bool} (path : B.AcceptingPath input)
    (hunambiguous : B.IsUnambiguous)
    {alpha : Finset (Fin n)} {k : Nat} {vertex : B.Vertex} :
    B.HasFilteredAlphaCut input alpha k vertex ↔
      B.IsAlphaCut path.walk alpha k vertex := by
  constructor
  · exact isAlphaCut_of_hasFilteredAlphaCut path hunambiguous
  · exact hasFilteredAlphaCut_of_isAlphaCut path

/-- If an accepting path reads all variables in `alpha`, then every valid
filtered rank has exactly one input-compatible semantic cut vertex.

Syntactic read-once supplies the pathwise cut theorem.  Unambiguity makes the
result independent of the chosen prefix and suffix witnesses. -/
theorem AcceptingPath.existsUnique_hasFilteredAlphaCut
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {input : Fin n → Bool} (path : B.AcceptingPath input)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hunambiguous : B.IsUnambiguous)
    (alpha : Finset (Fin n)) (k : Nat)
    (hsubset : alpha ⊆ path.walk.queryVars)
    (hk : k < alpha.card) :
    ∃! vertex, B.HasFilteredAlphaCut input alpha k vertex := by
  rcases path.existsUnique_alphaCut hreadOnce alpha k hsubset hk with
    ⟨vertex, hvertex, hunique⟩
  refine ⟨vertex,
    (hasFilteredAlphaCut_iff_isAlphaCut path hunambiguous).mpr hvertex, ?_⟩
  intro other hother
  exact hunique other
    ((hasFilteredAlphaCut_iff_isAlphaCut path hunambiguous).mp hother)

/-- Acceptance-level form: if every accepting path reads `alpha` (equivalently
the unique one does, under `hunambiguous`), then the semantic cut vertex is
unique at every valid rank. -/
theorem existsUnique_hasFilteredAlphaCut_of_accepts
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {input : Fin n → Bool}
    (haccepts : B.Accepts input)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hunambiguous : B.IsUnambiguous)
    (alpha : Finset (Fin n)) (k : Nat)
    (hsubset : ∀ path : B.AcceptingPath input,
      alpha ⊆ path.walk.queryVars)
    (hk : k < alpha.card) :
    ∃! vertex, B.HasFilteredAlphaCut input alpha k vertex := by
  rcases haccepts with ⟨path⟩
  exact path.existsUnique_hasFilteredAlphaCut hreadOnce hunambiguous
    alpha k (hsubset path) hk

/-- The natural-number indicator of the semantic filtered-cut predicate. -/
noncomputable def filteredAlphaCutIndicator
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (input : Fin n → Bool) (alpha : Finset (Fin n))
    (k : Nat) (vertex : B.Vertex) : Nat := by
  classical
  exact if B.HasFilteredAlphaCut input alpha k vertex then 1 else 0

/-- Pointwise partition of unity: on an accepted input whose accepting path
reads `alpha`, the filtered cut indicators sum to one. -/
theorem AcceptingPath.sum_filteredAlphaCutIndicator_eq_one
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {input : Fin n → Bool} (path : B.AcceptingPath input)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hunambiguous : B.IsUnambiguous)
    (alpha : Finset (Fin n)) (k : Nat)
    (hsubset : alpha ⊆ path.walk.queryVars)
    (hk : k < alpha.card) :
    ∑ vertex : B.Vertex,
      B.filteredAlphaCutIndicator input alpha k vertex = 1 := by
  classical
  rcases path.existsUnique_hasFilteredAlphaCut hreadOnce hunambiguous
      alpha k hsubset hk with
    ⟨cutVertex, hcutVertex, hunique⟩
  calc
    ∑ vertex : B.Vertex,
        B.filteredAlphaCutIndicator input alpha k vertex =
        B.filteredAlphaCutIndicator input alpha k cutVertex := by
      apply Fintype.sum_eq_single cutVertex
      intro other hother
      have hnotCut :
          ¬ B.HasFilteredAlphaCut input alpha k other := by
        intro hcut
        exact hother (hunique other hcut)
      simp [filteredAlphaCutIndicator, hnotCut]
    _ = 1 := by
      simp [filteredAlphaCutIndicator, hcutVertex]

end FiniteUnambiguousFBDD
end OneTapeMagnification
end Frontier
end Pnp4
