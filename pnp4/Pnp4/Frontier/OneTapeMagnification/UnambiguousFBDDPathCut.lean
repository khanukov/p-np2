import Pnp4.Frontier.OneTapeMagnification.FiniteUnambiguousFBDD

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

namespace FiniteUnambiguousFBDD

/-!
# Filtered path cuts for finite unambiguous FBDDs

This file proves the first combinatorial step needed to extend the CLTW
Fourier decomposition from programs that read every variable to syntactic
read-once programs that may skip variables.  The support condition

`alpha ⊆ preVars v ∪ postVars v`

is deliberately part of the global cut predicate.  It prevents a cut vertex
from contributing to a Fourier coefficient containing a variable that no
accepting continuation through that vertex reads.
-/

/-! ## Filtered query-event lists -/

/-- Query events whose variables belong to `alpha`, retaining path order. -/
def alphaEvents {n : Nat} {Vertex : Type}
    (events : List (Vertex × Fin n)) (alpha : Finset (Fin n)) :
    List (Vertex × Fin n) :=
  events.filter fun event => decide (event.2 ∈ alpha)

/-- Filtering query events preserves absence of duplicate query variables. -/
theorem alphaEvents_map_snd_nodup {n : Nat} {Vertex : Type}
    (events : List (Vertex × Fin n)) (alpha : Finset (Fin n))
    (hnodup : (events.map Prod.snd).Nodup) :
    ((alphaEvents events alpha).map Prod.snd).Nodup := by
  apply hnodup.sublist
  exact List.Sublist.map Prod.snd List.filter_sublist

/-- The variables of the filtered events are exactly the intersection of
`alpha` with the variables of the original event list. -/
theorem alphaEvents_map_snd_toFinset {n : Nat} {Vertex : Type}
    (events : List (Vertex × Fin n)) (alpha : Finset (Fin n)) :
    ((alphaEvents events alpha).map Prod.snd).toFinset =
      alpha ∩ (events.map Prod.snd).toFinset := by
  classical
  ext queryIndex
  constructor
  · intro hqueryIndex
    have hmap : queryIndex ∈ (alphaEvents events alpha).map Prod.snd :=
      List.mem_toFinset.mp hqueryIndex
    rcases List.mem_map.mp hmap with ⟨event, hevent, heq⟩
    subst queryIndex
    have hfiltered := List.mem_filter.mp hevent
    exact Finset.mem_inter.mpr ⟨by simpa using hfiltered.2,
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨event, hfiltered.1, rfl⟩)⟩
  · intro hqueryIndex
    rcases Finset.mem_inter.mp hqueryIndex with ⟨halpha, hevents⟩
    have hmap : queryIndex ∈ events.map Prod.snd :=
      List.mem_toFinset.mp hevents
    rcases List.mem_map.mp hmap with ⟨event, hevent, heq⟩
    subst queryIndex
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    exact ⟨event, List.mem_filter.mpr ⟨hevent, by simpa using halpha⟩, rfl⟩

/-- The number of selected events is the cardinality of the corresponding
variable-set intersection. -/
theorem alphaEvents_length_eq_inter_card {n : Nat} {Vertex : Type}
    (events : List (Vertex × Fin n)) (alpha : Finset (Fin n))
    (hnodup : (events.map Prod.snd).Nodup) :
    (alphaEvents events alpha).length =
      (alpha ∩ (events.map Prod.snd).toFinset).card := by
  have hfiltered := alphaEvents_map_snd_nodup events alpha hnodup
  calc
    (alphaEvents events alpha).length =
        ((alphaEvents events alpha).map Prod.snd).length := by simp
    _ = ((alphaEvents events alpha).map Prod.snd).toFinset.card :=
      (List.toFinset_card_of_nodup hfiltered).symm
    _ = (alpha ∩ (events.map Prod.snd).toFinset).card := by
      rw [alphaEvents_map_snd_toFinset]

/-- If every variable of `alpha` occurs in the event list, filtering selects
exactly `alpha.card` events. -/
theorem alphaEvents_length_eq_card {n : Nat} {Vertex : Type}
    (events : List (Vertex × Fin n)) (alpha : Finset (Fin n))
    (hnodup : (events.map Prod.snd).Nodup)
    (hsubset : alpha ⊆ (events.map Prod.snd).toFinset) :
    (alphaEvents events alpha).length = alpha.card := by
  rw [alphaEvents_length_eq_inter_card events alpha hnodup]
  rw [Finset.inter_eq_left.mpr hsubset]

/-- The local cut event is the event at filtered rank `k`. -/
def IsLocalAlphaCut {n : Nat} {Vertex : Type}
    (events : List (Vertex × Fin n)) (alpha : Finset (Fin n))
    (k : Nat) (event : Vertex × Fin n) : Prop :=
  (alphaEvents events alpha)[k]? = some event

/-- A valid filtered rank selects exactly one local event. -/
theorem existsUnique_isLocalAlphaCut {n : Nat} {Vertex : Type}
    (events : List (Vertex × Fin n)) (alpha : Finset (Fin n)) (k : Nat)
    (hk : k < (alphaEvents events alpha).length) :
    ∃! event, IsLocalAlphaCut events alpha k event := by
  let event := (alphaEvents events alpha)[k]
  refine ⟨event, ?_, ?_⟩
  · simp [IsLocalAlphaCut, event, List.getElem?_eq_getElem hk]
  · intro other hother
    rw [IsLocalAlphaCut, List.getElem?_eq_getElem hk] at hother
    exact (Option.some.inj hother).symm

/-- The cardinality formulation used by the global path-cut theorem. -/
theorem existsUnique_isLocalAlphaCut_of_subset
    {n : Nat} {Vertex : Type}
    (events : List (Vertex × Fin n)) (alpha : Finset (Fin n)) (k : Nat)
    (hnodup : (events.map Prod.snd).Nodup)
    (hsubset : alpha ⊆ (events.map Prod.snd).toFinset)
    (hk : k < alpha.card) :
    ∃! event, IsLocalAlphaCut events alpha k event := by
  apply existsUnique_isLocalAlphaCut events alpha k
  rwa [alphaEvents_length_eq_card events alpha hnodup hsubset]

/-- A list member determines a decomposition at one of its occurrences. -/
theorem exists_eq_append_cons_of_mem {Element : Type}
    {element : Element} {elements : List Element}
    (hmem : element ∈ elements) :
    ∃ left right, elements = left ++ element :: right := by
  induction elements with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · exact ⟨[], tail, rfl⟩
      · rcases ih htail with ⟨left, right, heq⟩
        exact ⟨head :: left, right, by simp [heq]⟩

/-- Filtering respects a decomposition at a selected event. -/
theorem alphaEvents_eq_append_cons {n : Nat} {Vertex : Type}
    {events leftEvents rightEvents : List (Vertex × Fin n)}
    {event : Vertex × Fin n} {alpha : Finset (Fin n)}
    (heq : events = leftEvents ++ event :: rightEvents)
    (halpha : event.2 ∈ alpha) :
    alphaEvents events alpha =
      alphaEvents leftEvents alpha ++ event :: alphaEvents rightEvents alpha := by
  subst events
  simp [alphaEvents, halpha]

/-- In a read-once event list, the prefix before the event at filtered index
`k` contains exactly `k` selected events. -/
theorem alphaEvents_left_length_eq_of_getElem_eq
    {n : Nat} {Vertex : Type}
    {events leftEvents rightEvents : List (Vertex × Fin n)}
    {event : Vertex × Fin n} {alpha : Finset (Fin n)} {k : Nat}
    (hnodup : (events.map Prod.snd).Nodup)
    (hk : k < (alphaEvents events alpha).length)
    (hget : (alphaEvents events alpha)[k]? = some event)
    (heq : events = leftEvents ++ event :: rightEvents)
    (halpha : event.2 ∈ alpha) :
    (alphaEvents leftEvents alpha).length = k := by
  have heventsNodup : events.Nodup :=
    List.Nodup.of_map Prod.snd hnodup
  have hselectedNodup : (alphaEvents events alpha).Nodup :=
    heventsNodup.filter _
  have hfiltered := alphaEvents_eq_append_cons heq halpha
  have hleftLt : (alphaEvents leftEvents alpha).length <
      (alphaEvents events alpha).length := by
    rw [hfiltered]
    simp
  have hleftGet? :
      (alphaEvents events alpha)[(alphaEvents leftEvents alpha).length]? =
        some event := by
    rw [hfiltered]
    simp
  have hleftGet :
      (alphaEvents events alpha)[(alphaEvents leftEvents alpha).length] =
        event := by
    rw [List.getElem?_eq_getElem hleftLt] at hleftGet?
    exact Option.some.inj hleftGet?
  have hgetValue : (alphaEvents events alpha)[k] = event := by
    rw [List.getElem?_eq_getElem hk] at hget
    exact Option.some.inj hget
  have hsame :
      (alphaEvents events alpha)[(alphaEvents leftEvents alpha).length] =
        (alphaEvents events alpha)[k] :=
    hleftGet.trans hgetValue.symm
  exact (hselectedNodup.getElem_inj_iff).mp hsame

/-- Conversely, a selected event after a prefix of filtered length `k` is
the event at filtered index `k`. -/
theorem alphaEvents_getElem_eq_of_left_length
    {n : Nat} {Vertex : Type}
    {events leftEvents rightEvents : List (Vertex × Fin n)}
    {event : Vertex × Fin n} {alpha : Finset (Fin n)} {k : Nat}
    (heq : events = leftEvents ++ event :: rightEvents)
    (halpha : event.2 ∈ alpha)
    (hlength : (alphaEvents leftEvents alpha).length = k) :
    (alphaEvents events alpha)[k]? = some event := by
  have hfiltered := alphaEvents_eq_append_cons heq halpha
  rw [hfiltered, ← hlength]
  simp

/-! ## Splitting graph walks at query events -/

namespace Walk

/-- An event-list decomposition lifts to a genuine graph-walk decomposition.
The left walk ends at the query vertex and therefore excludes that vertex's
query; the right walk begins there and includes it. -/
theorem split_of_queryEvents_eq_append_cons
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {source target cutVertex : B.Vertex} {cutIndex : Fin n}
    (walk : B.Walk source target)
    (leftEvents rightEvents : List (B.Vertex × Fin n))
    (heq : walk.queryEvents =
      leftEvents ++ (cutVertex, cutIndex) :: rightEvents) :
    ∃ (leftWalk : B.Walk source cutVertex)
      (rightWalk : B.Walk cutVertex target),
      leftWalk.append rightWalk = walk ∧
      leftWalk.queryEvents = leftEvents ∧
      rightWalk.queryEvents = (cutVertex, cutIndex) :: rightEvents := by
  induction walk generalizing leftEvents rightEvents cutVertex cutIndex with
  | nil vertex =>
      simp [queryEvents] at heq
  | @cons source middle target edge tail ih =>
      cases hnode : B.node source with
      | query queryIndex ifFalse ifTrue =>
          cases leftEvents with
          | nil =>
              simp only [queryEvents, hnode, FiniteUFBDDNode.queryEvent?,
                Option.toList_some, List.singleton_append,
                List.nil_append] at heq
              injection heq with hhead htail
              cases hhead
              cases htail
              refine ⟨.nil source, .cons edge tail, rfl, rfl, ?_⟩
              simp [queryEvents, hnode, FiniteUFBDDNode.queryEvent?]
          | cons first rest =>
              simp only [queryEvents, hnode, FiniteUFBDDNode.queryEvent?,
                Option.toList_some, List.cons_append] at heq
              injection heq with hfirst htail
              rcases ih rest rightEvents htail with
                ⟨leftWalk, rightWalk, happend, hleft, hright⟩
              refine ⟨.cons edge leftWalk, rightWalk, ?_, ?_, hright⟩
              · simp [append, happend]
              · simp [queryEvents, hnode, FiniteUFBDDNode.queryEvent?,
                  hleft, hfirst]
      | choice children =>
          have htailEq : tail.queryEvents =
              leftEvents ++ (cutVertex, cutIndex) :: rightEvents := by
            simpa [queryEvents, hnode, FiniteUFBDDNode.queryEvent?] using heq
          rcases ih leftEvents rightEvents htailEq with
            ⟨leftWalk, rightWalk, happend, hleft, hright⟩
          refine ⟨.cons edge leftWalk, rightWalk, ?_, ?_, hright⟩
          · simp [append, happend]
          · simpa [queryEvents, hnode, FiniteUFBDDNode.queryEvent?] using hleft
      | sink =>
          simp [Edge, FiniteUFBDDNode.HasChild, hnode] at edge

/-- Along a full accepting walk, intersecting `alpha` with the global
syntactic `preVars` is the same as intersecting it with the variables on the
chosen left subwalk. -/
theorem alpha_inter_preVars_eq_inter_queryVars
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {cutVertex : B.Vertex} {alpha : Finset (Fin n)}
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (leftWalk : B.Walk B.start cutVertex)
    (rightWalk : B.Walk cutVertex B.accept)
    (wholeWalk : B.Walk B.start B.accept)
    (happend : leftWalk.append rightWalk = wholeWalk)
    (hsubset : alpha ⊆ wholeWalk.queryVars) :
    alpha ∩ B.preVars cutVertex = alpha ∩ leftWalk.queryVars := by
  classical
  ext queryIndex
  constructor
  · intro hqueryIndex
    rcases Finset.mem_inter.mp hqueryIndex with ⟨halpha, hpre⟩
    have hwhole : queryIndex ∈ wholeWalk.queryVars := hsubset halpha
    have hdecomp : queryIndex ∈ (leftWalk.append rightWalk).queryVars := by
      simpa [happend] using hwhole
    rw [queryVars_append] at hdecomp
    rcases Finset.mem_union.mp hdecomp with hleft | hright
    · exact Finset.mem_inter.mpr ⟨halpha, hleft⟩
    · have hpost : queryIndex ∈ B.postVars cutVertex :=
        rightWalk.queryVars_subset_postVars hright
      have hdisjoint := B.preVars_disjoint_postVars hreadOnce cutVertex
      exact (Finset.disjoint_left.mp hdisjoint hpre hpost).elim
  · intro hqueryIndex
    rcases Finset.mem_inter.mp hqueryIndex with ⟨halpha, hleft⟩
    exact Finset.mem_inter.mpr
      ⟨halpha, leftWalk.queryVars_subset_preVars hleft⟩

/-- Every `alpha`-variable on a split accepting walk lies either in the
global syntactic prefix set or in the global syntactic suffix set.  This is
the mandatory support filter in the corrected CLTW cut. -/
theorem alpha_subset_preVars_union_postVars
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {cutVertex : B.Vertex} {alpha : Finset (Fin n)}
    (leftWalk : B.Walk B.start cutVertex)
    (rightWalk : B.Walk cutVertex B.accept)
    (wholeWalk : B.Walk B.start B.accept)
    (happend : leftWalk.append rightWalk = wholeWalk)
    (hsubset : alpha ⊆ wholeWalk.queryVars) :
    alpha ⊆ B.preVars cutVertex ∪ B.postVars cutVertex := by
  intro queryIndex halpha
  have hwhole : queryIndex ∈ wholeWalk.queryVars := hsubset halpha
  have hdecomp : queryIndex ∈ (leftWalk.append rightWalk).queryVars := by
    simpa [happend] using hwhole
  rw [queryVars_append] at hdecomp
  rcases Finset.mem_union.mp hdecomp with hleft | hright
  · exact Finset.mem_union.mpr
      (Or.inl (leftWalk.queryVars_subset_preVars hleft))
  · exact Finset.mem_union.mpr
      (Or.inr (rightWalk.queryVars_subset_postVars hright))

end Walk

/-- Event counting specialized to a graph walk. -/
theorem Walk.alphaEvents_length_eq_inter_queryVars_card
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {source target : B.Vertex} (walk : B.Walk source target)
    (alpha : Finset (Fin n)) (hnodup : walk.queryTrace.Nodup) :
    (alphaEvents walk.queryEvents alpha).length =
      (alpha ∩ walk.queryVars).card := by
  simpa [Walk.queryTrace, Walk.queryVars] using
    alphaEvents_length_eq_inter_card walk.queryEvents alpha hnodup

/-- A global filtered cut.  The query event witnesses that `vertex` occurs on
the chosen accepting walk.  The final conjunct is the support filter required
when accepting paths may skip input variables. -/
def IsAlphaCut {n : Nat} (B : FiniteUnambiguousFBDD n)
    (walk : B.Walk B.start B.accept) (alpha : Finset (Fin n))
    (k : Nat) (vertex : B.Vertex) : Prop :=
  ∃ (queryIndex : Fin n)
    (leftEvents rightEvents : List (B.Vertex × Fin n)),
    walk.queryEvents =
        leftEvents ++ (vertex, queryIndex) :: rightEvents ∧
      queryIndex ∈ alpha ∧
      (alpha ∩ B.preVars vertex).card = k ∧
      alpha ⊆ B.preVars vertex ∪ B.postVars vertex

/-- Every nonempty rank below `alpha.card` determines a unique query vertex
on an accepting path.  Besides the CLTW prefix-cardinality condition, the
vertex satisfies the support filter needed for paths that may skip variables.

Unambiguity is not needed for this pathwise statement; it enters later when
accepting-path indicators are factorized. -/
theorem AcceptingPath.existsUnique_alphaCut
    {n : Nat} {B : FiniteUnambiguousFBDD n}
    {input : Fin n → Bool} (path : B.AcceptingPath input)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (alpha : Finset (Fin n)) (k : Nat)
    (hsubset : alpha ⊆ path.walk.queryVars)
    (hk : k < alpha.card) :
    ∃! vertex, B.IsAlphaCut path.walk alpha k vertex := by
  classical
  have htraceNodup :
      (path.walk.queryEvents.map Prod.snd).Nodup := by
    simpa [Walk.queryTrace] using hreadOnce B.accept path.walk
  have heventSubset :
      alpha ⊆ (path.walk.queryEvents.map Prod.snd).toFinset := by
    simpa [Walk.queryVars, Walk.queryTrace] using hsubset
  have hselectedLength :
      (alphaEvents path.walk.queryEvents alpha).length = alpha.card :=
    alphaEvents_length_eq_card path.walk.queryEvents alpha
      htraceNodup heventSubset
  have hkSelected :
      k < (alphaEvents path.walk.queryEvents alpha).length := by
    rw [hselectedLength]
    exact hk
  rcases existsUnique_isLocalAlphaCut
      path.walk.queryEvents alpha k hkSelected with
    ⟨chosenEvent, hchosen, _hchosenUnique⟩
  rcases chosenEvent with ⟨cutVertex, cutIndex⟩
  have hchosenGet :
      (alphaEvents path.walk.queryEvents alpha)[k]? =
        some (cutVertex, cutIndex) :=
    hchosen
  have hchosenValue :
      (alphaEvents path.walk.queryEvents alpha)[k] =
        (cutVertex, cutIndex) := by
    have hchosenCopy := hchosenGet
    rw [List.getElem?_eq_getElem hkSelected] at hchosenCopy
    exact Option.some.inj hchosenCopy
  have hchosenMem :
      (cutVertex, cutIndex) ∈
        alphaEvents path.walk.queryEvents alpha := by
    have hmem := List.getElem_mem hkSelected
    rw [hchosenValue] at hmem
    exact hmem
  have hcutIndexAlpha : cutIndex ∈ alpha := by
    have hselected := List.of_mem_filter hchosenMem
    simpa [alphaEvents] using hselected
  have hchosenMemEvents :
      (cutVertex, cutIndex) ∈ path.walk.queryEvents := by
    exact List.mem_of_mem_filter hchosenMem
  rcases exists_eq_append_cons_of_mem hchosenMemEvents with
    ⟨leftEvents, rightEvents, hevents⟩
  have hleftLength :
      (alphaEvents leftEvents alpha).length = k :=
    alphaEvents_left_length_eq_of_getElem_eq htraceNodup hkSelected
      hchosenGet hevents hcutIndexAlpha
  rcases Walk.split_of_queryEvents_eq_append_cons path.walk
      leftEvents rightEvents hevents with
    ⟨leftWalk, rightWalk, happend, hleftEvents, _hrightEvents⟩
  have hleftCount : (alpha ∩ leftWalk.queryVars).card = k := by
    calc
      (alpha ∩ leftWalk.queryVars).card =
          (alphaEvents leftWalk.queryEvents alpha).length :=
        (leftWalk.alphaEvents_length_eq_inter_queryVars_card alpha
          (hreadOnce cutVertex leftWalk)).symm
      _ = (alphaEvents leftEvents alpha).length := by rw [hleftEvents]
      _ = k := hleftLength
  have hpreEq :
      alpha ∩ B.preVars cutVertex = alpha ∩ leftWalk.queryVars :=
    Walk.alpha_inter_preVars_eq_inter_queryVars hreadOnce leftWalk
      rightWalk path.walk happend hsubset
  have hpreCard : (alpha ∩ B.preVars cutVertex).card = k := by
    rw [hpreEq]
    exact hleftCount
  have hsupport :
      alpha ⊆ B.preVars cutVertex ∪ B.postVars cutVertex :=
    Walk.alpha_subset_preVars_union_postVars leftWalk rightWalk
      path.walk happend hsubset
  refine ⟨cutVertex, ?_, ?_⟩
  · exact ⟨cutIndex, leftEvents, rightEvents, hevents,
      hcutIndexAlpha, hpreCard, hsupport⟩
  · intro otherVertex hother
    rcases hother with
      ⟨otherIndex, otherLeftEvents, otherRightEvents,
        hotherEvents, hotherIndexAlpha, hotherPreCard, _hotherSupport⟩
    rcases Walk.split_of_queryEvents_eq_append_cons path.walk
        otherLeftEvents otherRightEvents hotherEvents with
      ⟨otherLeftWalk, otherRightWalk, hotherAppend,
        hotherLeftEvents, _hotherRightEvents⟩
    have hotherPreEq :
        alpha ∩ B.preVars otherVertex =
          alpha ∩ otherLeftWalk.queryVars :=
      Walk.alpha_inter_preVars_eq_inter_queryVars hreadOnce
        otherLeftWalk otherRightWalk path.walk hotherAppend hsubset
    have hotherLocalCard :
        (alpha ∩ otherLeftWalk.queryVars).card = k := by
      rw [← hotherPreEq]
      exact hotherPreCard
    have hotherLeftLength :
        (alphaEvents otherLeftEvents alpha).length = k := by
      calc
        (alphaEvents otherLeftEvents alpha).length =
            (alphaEvents otherLeftWalk.queryEvents alpha).length := by
          rw [hotherLeftEvents]
        _ = (alpha ∩ otherLeftWalk.queryVars).card :=
          otherLeftWalk.alphaEvents_length_eq_inter_queryVars_card alpha
            (hreadOnce otherVertex otherLeftWalk)
        _ = k := hotherLocalCard
    have hotherGet :
        (alphaEvents path.walk.queryEvents alpha)[k]? =
          some (otherVertex, otherIndex) :=
      alphaEvents_getElem_eq_of_left_length hotherEvents
        hotherIndexAlpha hotherLeftLength
    have hpairs :
        (cutVertex, cutIndex) = (otherVertex, otherIndex) := by
      apply Option.some.inj
      exact hchosenGet.symm.trans hotherGet
    exact (congrArg Prod.fst hpairs).symm

end FiniteUnambiguousFBDD
end OneTapeMagnification
end Frontier
end Pnp4
