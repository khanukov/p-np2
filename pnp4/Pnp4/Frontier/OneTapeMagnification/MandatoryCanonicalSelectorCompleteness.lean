import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalUFBDD

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Completeness of mandatory selector query traces

A selector component whose query at every physical layer is fixed and
mandatory cannot reach the accepting sink early.  Consequently every formal
accepting walk through that component reads its entire fixed order.  For the
mandatory canonical family this order is a permutation of all input
coordinates, so every accepting path queries every variable.  This statement
is purely graph-theoretic and does not require positive block size or input
compatibility.
-/

namespace FiniteLayeredQueryProgramFamily

/-- A selector sink has no outgoing edges, so every walk starting at a sink
has an empty query trace.  The endpoint is deliberately generalized to keep
dependent elimination on `Walk` robust. -/
theorem selectorSinkWalk_queryTrace_eq_nil_aux {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) (value : Bool)
    {source target : (family.selectorFBDD).Vertex}
    (hsource : source = selectorSink value)
    (walk : (family.selectorFBDD).Walk source target) :
    walk.queryTrace = [] := by
  refine (FiniteUnambiguousFBDD.Walk.recOn
    (motive := fun source target walk =>
      source = selectorSink value -> walk.queryTrace = [])
    walk ?_ ?_) hsource
  · intro vertex _hvertex
    rfl
  · intro source middle target edge tail _ih hsource'
    subst source
    simp [FiniteUnambiguousFBDD.Edge, selectorFBDD, selectorNode,
      selectorSink, FiniteUFBDDNode.HasChild] at edge

/-- Exact remaining trace of a formal accepting walk which starts at an
arbitrary component boundary. -/
theorem selectorComponentWalk_to_accept_queryTrace_eq_drop_of_fixedMandatoryOrder
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (order : (index : family.Index) -> Fin (family.layers index) -> Fin n)
    (hfixed : forall index,
      (family.program index).HasFixedQueryOrder
        (fun layer => some (order index layer)))
    (index : family.Index) (fuel physical : Nat)
    (hphysical : physical + fuel = family.layers index)
    (state : (family.program index).State)
    {source target : (family.selectorFBDD).Vertex}
    (hsource : source =
      selectorComponent index ⟨physical, by omega⟩ state)
    (htarget : target = (family.selectorFBDD).accept)
    (walk : (family.selectorFBDD).Walk source target) :
    walk.queryTrace = (List.ofFn (order index)).drop physical := by
  induction fuel generalizing physical state source target with
  | zero =>
      have hnot : ¬ physical < family.layers index := by omega
      cases walk with
      | nil vertex =>
          have heq :
              selectorComponent index ⟨physical, by omega⟩ state =
                (family.selectorFBDD).accept := hsource.symm.trans htarget
          simp [selectorComponent, selectorFBDD, selectorSink] at heq
      | @cons _ middle _ edge tail =>
          subst source
          have hmiddle : middle =
              selectorSink ((family.program index).output state) := by
            simpa [FiniteUnambiguousFBDD.Edge, selectorFBDD, selectorNode,
              selectorComponent, selectorSink, hnot,
              FiniteUFBDDNode.HasChild] using edge
          have htail : tail.queryTrace = [] :=
            selectorSinkWalk_queryTrace_eq_nil_aux family
              ((family.program index).output state) hmiddle tail
          have htrace :
              (FiniteUnambiguousFBDD.Walk.cons edge tail).queryTrace =
                tail.queryTrace := by
            simp [FiniteUnambiguousFBDD.Walk.queryTrace,
              FiniteUnambiguousFBDD.Walk.queryEvents, selectorFBDD,
              selectorNode, selectorComponent, selectorSink, hnot,
              FiniteUFBDDNode.queryEvent?]
          rw [htrace, htail]
          have heq : physical = family.layers index := by omega
          simp [heq]
  | succ fuel ih =>
      have hlt : physical < family.layers index := by omega
      let layer : Fin (family.layers index) := ⟨physical, hlt⟩
      have hquery : (family.program index).query? layer state =
          some (order index layer) := hfixed index layer state
      cases walk with
      | nil vertex =>
          have heq :
              selectorComponent index ⟨physical, by omega⟩ state =
                (family.selectorFBDD).accept := hsource.symm.trans htarget
          simp [selectorComponent, selectorFBDD, selectorSink] at heq
      | @cons _ middle _ edge tail =>
          subst source
          have hmiddle :
              middle = selectorComponent index ⟨physical + 1, by omega⟩
                  ((family.program index).next layer state (some false)) ∨
                middle = selectorComponent index ⟨physical + 1, by omega⟩
                  ((family.program index).next layer state (some true)) := by
            simpa [FiniteUnambiguousFBDD.Edge, selectorFBDD, selectorNode,
              selectorComponent, selectorSink, hlt, layer, hquery,
              selectorNextBoundary, FiniteUFBDDNode.HasChild] using edge
          rcases hmiddle with hmiddle | hmiddle
          · have htail := ih (physical := physical + 1)
              (hphysical := by omega)
              (state := (family.program index).next layer state (some false))
              (source := middle) (target := target) hmiddle htarget tail
            have htrace :
                (FiniteUnambiguousFBDD.Walk.cons edge tail).queryTrace =
                  order index layer :: tail.queryTrace := by
              simp [FiniteUnambiguousFBDD.Walk.queryTrace,
                FiniteUnambiguousFBDD.Walk.queryEvents, selectorFBDD,
                selectorNode, selectorComponent, hlt, layer, hquery,
                FiniteUFBDDNode.queryEvent?]
            rw [htrace, htail]
            have hlength :
                physical < (List.ofFn (order index)).length := by
              simpa using hlt
            rw [List.drop_eq_getElem_cons hlength]
            simp [layer]
          · have htail := ih (physical := physical + 1)
              (hphysical := by omega)
              (state := (family.program index).next layer state (some true))
              (source := middle) (target := target) hmiddle htarget tail
            have htrace :
                (FiniteUnambiguousFBDD.Walk.cons edge tail).queryTrace =
                  order index layer :: tail.queryTrace := by
              simp [FiniteUnambiguousFBDD.Walk.queryTrace,
                FiniteUnambiguousFBDD.Walk.queryEvents, selectorFBDD,
                selectorNode, selectorComponent, hlt, layer, hquery,
                FiniteUFBDDNode.queryEvent?]
            rw [htrace, htail]
            have hlength :
                physical < (List.ofFn (order index)).length := by
              simpa using hlt
            rw [List.drop_eq_getElem_cons hlength]
            simp [layer]

/-- A component-start-to-accept walk has exactly the component's full fixed
mandatory query order. -/
theorem selectorComponentStartWalk_to_accept_queryTrace_eq_of_fixedMandatoryOrder
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (order : (index : family.Index) -> Fin (family.layers index) -> Fin n)
    (hfixed : forall index,
      (family.program index).HasFixedQueryOrder
        (fun layer => some (order index layer)))
    (index : family.Index)
    (walk : (family.selectorFBDD).Walk
      (selectorComponent index ⟨0, Nat.zero_lt_succ _⟩
        (family.program index).start)
      (family.selectorFBDD).accept) :
    walk.queryTrace = List.ofFn (order index) := by
  simpa using
    selectorComponentWalk_to_accept_queryTrace_eq_drop_of_fixedMandatoryOrder
      family order hfixed index (family.layers index) 0 (by omega)
        (family.program index).start rfl rfl walk

/-- Every formal accepting root walk selects one component and has exactly
that component's full fixed query trace. -/
theorem selectorRootWalk_to_accept_exists_queryTrace_eq_of_fixedMandatoryOrder_aux
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (order : (index : family.Index) -> Fin (family.layers index) -> Fin n)
    (hfixed : forall index,
      (family.program index).HasFixedQueryOrder
        (fun layer => some (order index layer)))
    {source target : (family.selectorFBDD).Vertex}
    (hsource : source = selectorRoot)
    (htarget : target = (family.selectorFBDD).accept)
    (walk : (family.selectorFBDD).Walk source target) :
    exists index, walk.queryTrace = List.ofFn (order index) := by
  classical
  letI : Fintype family.Index := family.indexFintype
  cases walk with
  | nil vertex =>
      have heq : (selectorRoot : family.SelectorVertex) =
          (family.selectorFBDD).accept := hsource.symm.trans htarget
      simp [selectorRoot, selectorFBDD, selectorSink] at heq
  | @cons _ middle _ edge tail =>
      subst source
      have hfirst : (family.selectorFBDD).Edge selectorRoot middle := by
        exact edge
      have hmem : middle ∈ family.selectorStartChildren := by
        simpa [FiniteUnambiguousFBDD.Edge, selectorFBDD, selectorNode,
          selectorRoot, FiniteUFBDDNode.HasChild] using hfirst
      simp only [selectorStartChildren, List.mem_map] at hmem
      obtain ⟨index, _hindex, hmiddle⟩ := hmem
      have htail :=
        selectorComponentWalk_to_accept_queryTrace_eq_drop_of_fixedMandatoryOrder
          family order hfixed index (family.layers index) 0 (by omega)
            (family.program index).start hmiddle.symm htarget tail
      refine ⟨index, ?_⟩
      have htrace :
          (FiniteUnambiguousFBDD.Walk.cons edge tail).queryTrace =
            tail.queryTrace := by
        simp [FiniteUnambiguousFBDD.Walk.queryTrace,
          FiniteUnambiguousFBDD.Walk.queryEvents, selectorFBDD,
          selectorNode, selectorRoot, FiniteUFBDDNode.queryEvent?]
      rw [htrace, htail]
      simp

/-- Root-specialized form of the exact selector trace decoder. -/
theorem selectorRootWalk_to_accept_exists_queryTrace_eq_of_fixedMandatoryOrder
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (order : (index : family.Index) -> Fin (family.layers index) -> Fin n)
    (hfixed : forall index,
      (family.program index).HasFixedQueryOrder
        (fun layer => some (order index layer)))
    (walk : (family.selectorFBDD).Walk
      (family.selectorFBDD).start (family.selectorFBDD).accept) :
    exists index, walk.queryTrace = List.ofFn (order index) := by
  exact selectorRootWalk_to_accept_exists_queryTrace_eq_of_fixedMandatoryOrder_aux
    family order hfixed rfl rfl walk

/-- If every component has `n` mandatory duplicate-free layers, every formal
accepting selector path queries all `n` variables. -/
theorem selectorAcceptingPath_queryVars_eq_univ_of_fixedMandatoryOrder
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (order : (index : family.Index) -> Fin (family.layers index) -> Fin n)
    (hfixed : forall index,
      (family.program index).HasFixedQueryOrder
        (fun layer => some (order index layer)))
    (hlayers : forall index, family.layers index = n)
    (hnodup : forall index, (List.ofFn (order index)).Nodup)
    (input : Fin n -> Bool)
    (path : (family.selectorFBDD).AcceptingPath input) :
    path.walk.queryVars = Finset.univ := by
  obtain ⟨index, htrace⟩ :=
    selectorRootWalk_to_accept_exists_queryTrace_eq_of_fixedMandatoryOrder
      family order hfixed path.walk
  unfold FiniteUnambiguousFBDD.Walk.queryVars
  rw [htrace]
  apply Finset.eq_univ_of_card
  rw [List.toFinset_card_of_nodup (hnodup index)]
  simp [hlayers index]

end FiniteLayeredQueryProgramFamily

/-! ## Mandatory canonical specialization -/

/-- Every accepting path of the mandatory canonical selector queries every
input coordinate.  No positivity assumption on `b` is needed. -/
theorem mandatoryCanonicalUFBDD_acceptingPath_queryVars_eq_univ
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (input : Fin n -> Bool)
    (path : (mandatoryCanonicalUFBDD machine n T b).AcceptingPath input) :
    path.walk.queryVars = Finset.univ := by
  let family := mandatoryFiniteRejectingGuardedCanonicalFamily machine n T b
  let order : (index : family.Index) ->
      Fin (family.layers index) -> Fin n := fun index =>
    mandatoryBuiltRejectingGuardedCanonicalQueryOrder machine n index
  apply FiniteLayeredQueryProgramFamily.selectorAcceptingPath_queryVars_eq_univ_of_fixedMandatoryOrder
      family order
  · intro index
    exact mandatoryBuiltRejectingGuardedCanonicalComponent_hasFixedQueryOrder
      machine n index
  · intro index
    rfl
  · intro index
    exact mandatoryBuiltRejectingGuardedCanonicalQueryOrder_nodup
      machine n index

/-- In particular, every chosen variable set is contained in the variables
read by every accepting mandatory canonical path. -/
theorem mandatoryCanonicalUFBDD_alpha_subset_acceptingPath_queryVars
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) (input : Fin n -> Bool)
    (alpha : Finset (Fin n))
    (path : (mandatoryCanonicalUFBDD machine n T b).AcceptingPath input) :
    alpha ⊆ path.walk.queryVars := by
  rw [mandatoryCanonicalUFBDD_acceptingPath_queryVars_eq_univ
    machine n T b input path]
  exact Finset.subset_univ alpha

end OneTapeMagnification
end Frontier
end Pnp4
