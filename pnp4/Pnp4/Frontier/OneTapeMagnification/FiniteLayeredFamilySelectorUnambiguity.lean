import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FiniteLayeredFamilySelector

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Unambiguity of the finite layered-family selector

The selector has a single nondeterministic step: its silent root chooses a
family component.  Once that choice is fixed, input compatibility determines
every query transition, while query-free and terminal component transitions
have singleton child lists.  Thus component unambiguity lifts to graph-path
unambiguity of the selector.
-/

namespace FiniteLayeredQueryProgramFamily

/-- No walk can leave a selector sink, so any two walks with the same sink
source and endpoint coincide.  The source is generalized to keep dependent
elimination on `Walk` robust. -/
theorem selectorSinkWalk_unique_aux {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) (value : Bool)
    {source target : (family.selectorFBDD).Vertex}
    (hsource : source = selectorSink value)
    (left right : (family.selectorFBDD).Walk source target) :
    left = right := by
  cases left with
  | nil vertex =>
      cases right with
      | nil => rfl
      | @cons _ middle _ edge tail =>
          rw [hsource] at edge
          simp [FiniteUnambiguousFBDD.Edge, selectorFBDD, selectorNode,
            selectorSink, FiniteUFBDDNode.HasChild] at edge
  | @cons _ middle _ edge tail =>
      rw [hsource] at edge
      simp [FiniteUnambiguousFBDD.Edge, selectorFBDD, selectorNode,
        selectorSink, FiniteUFBDDNode.HasChild] at edge

/-- Starting at a fixed component slot, an input-compatible walk to the
accepting sink is unique.  Induction is on the exact number of remaining
physical layers; at the terminal boundary the only possible transition is
the singleton edge to the component's Boolean sink. -/
theorem selectorComponentWalk_unique_aux {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) (input : Fin n -> Bool)
    (index : family.Index)
    (fuel physical : Nat) (hphysical : physical + fuel = family.layers index)
    (state : (family.program index).State)
    {source target : (family.selectorFBDD).Vertex}
    (hsource : source = selectorComponent index
      ⟨physical, by omega⟩ state)
    (htarget : target = (family.selectorFBDD).accept)
    (left right : (family.selectorFBDD).Walk source target)
    (hleft : left.Compatible input) (hright : right.Compatible input) :
    left = right := by
  induction fuel generalizing physical state source target with
  | zero =>
      have hnot : ¬physical < family.layers index := by omega
      cases left with
      | nil vertex =>
          have heq : selectorComponent index ⟨physical, by omega⟩ state =
              (family.selectorFBDD).accept := hsource.symm.trans htarget
          simp [selectorComponent, selectorFBDD, selectorSink] at heq
      | @cons _ leftMiddle _ leftEdge leftTail =>
          have hleftFirst : (family.selectorFBDD).CompatibleEdge input
              (selectorComponent index ⟨physical, by omega⟩ state)
                leftMiddle := by
            simpa [hsource] using hleft.1
          have hleftMiddle : leftMiddle =
              selectorSink ((family.program index).output state) := by
            simpa [FiniteUnambiguousFBDD.CompatibleEdge, selectorFBDD,
              selectorNode, selectorComponent, selectorSink, hnot] using
                hleftFirst
          cases right with
          | nil vertex =>
              have heq : selectorComponent index
                    ⟨physical, by omega⟩ state =
                  (family.selectorFBDD).accept := hsource.symm.trans htarget
              simp [selectorComponent, selectorFBDD, selectorSink] at heq
          | @cons _ rightMiddle _ rightEdge rightTail =>
              have hrightFirst : (family.selectorFBDD).CompatibleEdge input
                  (selectorComponent index ⟨physical, by omega⟩ state)
                    rightMiddle := by
                simpa [hsource] using hright.1
              have hrightMiddle : rightMiddle =
                  selectorSink ((family.program index).output state) := by
                simpa [FiniteUnambiguousFBDD.CompatibleEdge, selectorFBDD,
                  selectorNode, selectorComponent, selectorSink, hnot] using
                    hrightFirst
              subst leftMiddle
              subst rightMiddle
              have htail : leftTail = rightTail :=
                selectorSinkWalk_unique_aux family
                  ((family.program index).output state) rfl leftTail rightTail
              cases htail
              rfl
  | succ fuel ih =>
      have hlt : physical < family.layers index := by omega
      let layer : Fin (family.layers index) := ⟨physical, hlt⟩
      cases hquery : (family.program index).query? layer state with
      | none =>
          cases left with
          | nil vertex =>
              have heq :
                  selectorComponent index ⟨physical, by omega⟩ state =
                    (family.selectorFBDD).accept :=
                hsource.symm.trans htarget
              simp [selectorComponent, selectorFBDD, selectorSink] at heq
          | @cons _ leftMiddle _ leftEdge leftTail =>
              have hleftFirst : (family.selectorFBDD).CompatibleEdge input
                  (selectorComponent index ⟨physical, by omega⟩ state)
                    leftMiddle := by
                simpa [hsource] using hleft.1
              have hleftMiddle : leftMiddle = selectorComponent index
                  ⟨physical + 1, by omega⟩
                  ((family.program index).next layer state none) := by
                simpa [FiniteUnambiguousFBDD.CompatibleEdge, selectorFBDD,
                  selectorNode, selectorComponent, selectorSink, hlt, layer,
                  hquery, selectorNextBoundary] using hleftFirst
              cases right with
              | nil vertex =>
                  have heq : selectorComponent index
                        ⟨physical, by omega⟩ state =
                      (family.selectorFBDD).accept :=
                    hsource.symm.trans htarget
                  simp [selectorComponent, selectorFBDD, selectorSink] at heq
              | @cons _ rightMiddle _ rightEdge rightTail =>
                  have hrightFirst :
                      (family.selectorFBDD).CompatibleEdge input
                        (selectorComponent index
                          ⟨physical, by omega⟩ state) rightMiddle := by
                    simpa [hsource] using hright.1
                  have hrightMiddle : rightMiddle = selectorComponent index
                      ⟨physical + 1, by omega⟩
                      ((family.program index).next layer state none) := by
                    simpa [FiniteUnambiguousFBDD.CompatibleEdge, selectorFBDD,
                      selectorNode, selectorComponent, selectorSink, hlt,
                      layer, hquery, selectorNextBoundary] using hrightFirst
                  subst leftMiddle
                  subst rightMiddle
                  have htail := ih (physical := physical + 1)
                    (hphysical := by omega)
                    (state := (family.program index).next layer state none)
                    (source := selectorComponent index
                      ⟨physical + 1, by omega⟩
                      ((family.program index).next layer state none))
                    (target := target) (left := leftTail)
                    (right := rightTail) rfl htarget hleft.2 hright.2
                  cases htail
                  rfl
      | some queryIndex =>
          cases hbit : input queryIndex with
          | false =>
              cases left with
              | nil vertex =>
                  have heq : selectorComponent index
                        ⟨physical, by omega⟩ state =
                      (family.selectorFBDD).accept :=
                    hsource.symm.trans htarget
                  simp [selectorComponent, selectorFBDD, selectorSink] at heq
              | @cons _ leftMiddle _ leftEdge leftTail =>
                  have hleftFirst :
                      (family.selectorFBDD).CompatibleEdge input
                        (selectorComponent index
                          ⟨physical, by omega⟩ state) leftMiddle := by
                    simpa [hsource] using hleft.1
                  have hleftMiddle : leftMiddle = selectorComponent index
                      ⟨physical + 1, by omega⟩
                      ((family.program index).next layer state
                        (some false)) := by
                    simpa [FiniteUnambiguousFBDD.CompatibleEdge, selectorFBDD,
                      selectorNode, selectorComponent, selectorSink, hlt,
                      layer, hquery, hbit, selectorNextBoundary] using
                        hleftFirst
                  cases right with
                  | nil vertex =>
                      have heq : selectorComponent index
                            ⟨physical, by omega⟩ state =
                          (family.selectorFBDD).accept :=
                        hsource.symm.trans htarget
                      simp [selectorComponent, selectorFBDD, selectorSink]
                        at heq
                  | @cons _ rightMiddle _ rightEdge rightTail =>
                      have hrightFirst :
                          (family.selectorFBDD).CompatibleEdge input
                            (selectorComponent index
                              ⟨physical, by omega⟩ state)
                                rightMiddle := by
                        simpa [hsource] using hright.1
                      have hrightMiddle : rightMiddle =
                          selectorComponent index ⟨physical + 1, by omega⟩
                            ((family.program index).next layer state
                              (some false)) := by
                        simpa [FiniteUnambiguousFBDD.CompatibleEdge,
                          selectorFBDD, selectorNode, selectorComponent,
                          selectorSink, hlt, layer, hquery, hbit,
                          selectorNextBoundary] using hrightFirst
                      subst leftMiddle
                      subst rightMiddle
                      have htail := ih (physical := physical + 1)
                        (hphysical := by omega)
                        (state := (family.program index).next layer state
                          (some false))
                        (source := selectorComponent index
                          ⟨physical + 1, by omega⟩
                          ((family.program index).next layer state
                            (some false)))
                        (target := target) (left := leftTail)
                        (right := rightTail) rfl htarget hleft.2 hright.2
                      cases htail
                      rfl
          | true =>
              cases left with
              | nil vertex =>
                  have heq : selectorComponent index
                        ⟨physical, by omega⟩ state =
                      (family.selectorFBDD).accept :=
                    hsource.symm.trans htarget
                  simp [selectorComponent, selectorFBDD, selectorSink] at heq
              | @cons _ leftMiddle _ leftEdge leftTail =>
                  have hleftFirst :
                      (family.selectorFBDD).CompatibleEdge input
                        (selectorComponent index
                          ⟨physical, by omega⟩ state) leftMiddle := by
                    simpa [hsource] using hleft.1
                  have hleftMiddle : leftMiddle = selectorComponent index
                      ⟨physical + 1, by omega⟩
                      ((family.program index).next layer state
                        (some true)) := by
                    simpa [FiniteUnambiguousFBDD.CompatibleEdge, selectorFBDD,
                      selectorNode, selectorComponent, selectorSink, hlt,
                      layer, hquery, hbit, selectorNextBoundary] using
                        hleftFirst
                  cases right with
                  | nil vertex =>
                      have heq : selectorComponent index
                            ⟨physical, by omega⟩ state =
                          (family.selectorFBDD).accept :=
                        hsource.symm.trans htarget
                      simp [selectorComponent, selectorFBDD, selectorSink]
                        at heq
                  | @cons _ rightMiddle _ rightEdge rightTail =>
                      have hrightFirst :
                          (family.selectorFBDD).CompatibleEdge input
                            (selectorComponent index
                              ⟨physical, by omega⟩ state)
                                rightMiddle := by
                        simpa [hsource] using hright.1
                      have hrightMiddle : rightMiddle =
                          selectorComponent index ⟨physical + 1, by omega⟩
                            ((family.program index).next layer state
                              (some true)) := by
                        simpa [FiniteUnambiguousFBDD.CompatibleEdge,
                          selectorFBDD, selectorNode, selectorComponent,
                          selectorSink, hlt, layer, hquery, hbit,
                          selectorNextBoundary] using hrightFirst
                      subst leftMiddle
                      subst rightMiddle
                      have htail := ih (physical := physical + 1)
                        (hphysical := by omega)
                        (state := (family.program index).next layer state
                          (some true))
                        (source := selectorComponent index
                          ⟨physical + 1, by omega⟩
                          ((family.program index).next layer state
                            (some true)))
                        (target := target) (left := leftTail)
                        (right := rightTail) rfl htarget hleft.2 hright.2
                      cases htail
                      rfl

/-- Two compatible accepting walks which selected the same component are
equal. -/
theorem selectorComponentWalk_unique {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n) (input : Fin n -> Bool)
    (index : family.Index)
    (left right : (family.selectorFBDD).Walk
      (selectorComponent index ⟨0, Nat.zero_lt_succ _⟩
        (family.program index).start)
      (family.selectorFBDD).accept)
    (hleft : left.Compatible input) (hright : right.Compatible input) :
    left = right :=
  selectorComponentWalk_unique_aux family input index
    (family.layers index) 0 (by omega) (family.program index).start
      rfl rfl left right hleft hright

/-- Component unambiguity lifts to path unambiguity of the finite selector. -/
theorem selectorFBDD_isUnambiguous_of_family {n : Nat}
    (family : FiniteLayeredQueryProgramFamily n)
    (hunambiguous : family.IsUnambiguous) :
    (family.selectorFBDD).IsUnambiguous := by
  classical
  letI : Fintype family.Index := family.indexFintype
  intro input left right hleft hright
  cases left with
  | @cons _ leftMiddle _ leftEdge leftTail =>
      have hleftFirst : (family.selectorFBDD).CompatibleEdge input
          selectorRoot leftMiddle := hleft.1
      have hleftMem : leftMiddle ∈ family.selectorStartChildren := by
        simpa [FiniteUnambiguousFBDD.CompatibleEdge, selectorFBDD,
          selectorNode, selectorRoot] using hleftFirst
      simp only [selectorStartChildren, List.mem_map] at hleftMem
      obtain ⟨leftIndex, _hleftIndex, hleftMiddle⟩ := hleftMem
      subst leftMiddle
      cases right with
      | @cons _ rightMiddle _ rightEdge rightTail =>
          have hrightFirst : (family.selectorFBDD).CompatibleEdge input
              selectorRoot rightMiddle := hright.1
          have hrightMem : rightMiddle ∈ family.selectorStartChildren := by
            simpa [FiniteUnambiguousFBDD.CompatibleEdge, selectorFBDD,
              selectorNode, selectorRoot] using hrightFirst
          simp only [selectorStartChildren, List.mem_map] at hrightMem
          obtain ⟨rightIndex, _hrightIndex, hrightMiddle⟩ := hrightMem
          subst rightMiddle
          have hleftEval :
              (family.program leftIndex).eval input = true := by
            exact selectorComponentWalk_to_accept_implies_eval_true
              family input leftIndex leftTail hleft.2
          have hrightEval :
              (family.program rightIndex).eval input = true := by
            exact selectorComponentWalk_to_accept_implies_eval_true
              family input rightIndex rightTail hright.2
          have hindex : leftIndex = rightIndex :=
            hunambiguous input leftIndex rightIndex hleftEval hrightEval
          subst rightIndex
          have htail : leftTail = rightTail :=
            selectorComponentWalk_unique family input leftIndex
              leftTail rightTail hleft.2 hright.2
          cases htail
          rfl

end FiniteLayeredQueryProgramFamily
end OneTapeMagnification
end Frontier
end Pnp4
