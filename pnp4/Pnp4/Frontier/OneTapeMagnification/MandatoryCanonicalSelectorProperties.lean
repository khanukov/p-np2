import Mathlib.Tactic
import Pnp4.Frontier.OneTapeMagnification.FiniteLayeredFamilySelector

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

local instance cachedInputMachineStateDecidableEqForMandatorySelector
    (machine : DeterministicMachine) [DecidableEq machine.State] :
    DecidableEq (cachedInputMachine machine).State :=
  cachedInputStateDecidableEq machine

/-!
# Mandatory canonical selector properties

The generic finite-family selector cannot inherit syntactic read-once behavior
from the source family's semantic `IsReadOnce` field: a formal graph path may
take mutually inconsistent Boolean branches.  This file states the stronger
and sufficient hypothesis explicitly.  Every component must query a fixed,
duplicate-free mandatory order, independently of its live state.

The mandatory canonical family satisfies that hypothesis because each
component is the output of `collapseToMandatoryFixedOrder`.
-/

namespace FiniteLayeredQueryProgramFamily

/-- Query-trace information for a formal selector walk which starts at a
component boundary.  Besides duplicate-freedom, every query in the walk is
identified with a layer at or after the starting boundary. -/
theorem selectorComponentWalk_queryTrace_spec_of_fixedMandatoryOrder
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (order : (index : family.Index) → Fin (family.layers index) → Fin n)
    (hfixed : ∀ index,
      (family.program index).HasFixedQueryOrder
        (fun layer => some (order index layer)))
    (hnodup : ∀ index, (List.ofFn (order index)).Nodup)
    (index : family.Index) (fuel physical : Nat)
    (hphysical : physical + fuel = family.layers index)
    (state : (family.program index).State)
    (source target : family.SelectorVertex)
    (walk : (family.selectorFBDD).Walk source target)
    (hsource : source =
      selectorComponent index ⟨physical, by omega⟩ state) :
    walk.queryTrace.Nodup ∧
      ∀ queryIndex ∈ walk.queryTrace,
        ∃ layer : Fin (family.layers index),
          physical ≤ layer.val ∧ queryIndex = order index layer := by
  induction fuel generalizing physical state source target with
  | zero =>
      have hnot : ¬physical < family.layers index := by omega
      refine (FiniteUnambiguousFBDD.Walk.recOn
        (motive := fun source target walk =>
          source = selectorComponent index ⟨physical, by omega⟩ state →
            walk.queryTrace.Nodup ∧
              ∀ queryIndex ∈ walk.queryTrace,
                ∃ layer : Fin (family.layers index),
                  physical ≤ layer.val ∧ queryIndex = order index layer)
        walk ?_ ?_) hsource
      · intro vertex _hvertex
        simp [FiniteUnambiguousFBDD.Walk.queryTrace,
          FiniteUnambiguousFBDD.Walk.queryEvents]
      · intro source middle target edge tail _htail hsource'
        subst source
        have hmiddle : middle =
            selectorSink ((family.program index).output state) := by
          simpa [FiniteUnambiguousFBDD.Edge, selectorFBDD, selectorNode,
            selectorComponent, selectorSink, hnot,
            FiniteUFBDDNode.HasChild] using edge
        subst middle
        have htailEmpty : tail.queryTrace = [] := by
          refine FiniteUnambiguousFBDD.Walk.recOn
            (motive := fun source target walk =>
              source = selectorSink ((family.program index).output state) →
                walk.queryTrace = []) tail ?_ ?_ rfl
          · intro vertex _hvertex
            rfl
          · intro source middle target edge' tail' _ih hsource''
            subst source
            simp [FiniteUnambiguousFBDD.Edge, selectorFBDD, selectorNode,
              selectorSink, FiniteUFBDDNode.HasChild] at edge'
        have htrace :
            (FiniteUnambiguousFBDD.Walk.cons edge tail).queryTrace =
              tail.queryTrace := by
          simp [FiniteUnambiguousFBDD.Walk.queryTrace,
            FiniteUnambiguousFBDD.Walk.queryEvents, selectorFBDD,
            selectorNode, selectorComponent, selectorSink, hnot,
            FiniteUFBDDNode.queryEvent?]
        rw [htrace, htailEmpty]
        simp
  | succ fuel ih =>
      have hlt : physical < family.layers index := by omega
      let layer : Fin (family.layers index) := ⟨physical, hlt⟩
      have hquery : (family.program index).query? layer state =
          some (order index layer) := hfixed index layer state
      refine (FiniteUnambiguousFBDD.Walk.recOn
        (motive := fun source target walk =>
          source = selectorComponent index ⟨physical, by omega⟩ state →
            walk.queryTrace.Nodup ∧
              ∀ queryIndex ∈ walk.queryTrace,
                ∃ later : Fin (family.layers index),
                  physical ≤ later.val ∧ queryIndex = order index later)
        walk ?_ ?_) hsource
      · intro vertex _hvertex
        simp [FiniteUnambiguousFBDD.Walk.queryTrace,
          FiniteUnambiguousFBDD.Walk.queryEvents]
      · intro source middle target edge tail _htail hsource'
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
        · have htail := ih (physical + 1) (by omega)
            ((family.program index).next layer state (some false))
            middle target tail hmiddle
          have hnotmem : order index layer ∉ tail.queryTrace := by
            intro hmem
            obtain ⟨later, hlater, heq⟩ := htail.2 _ hmem
            have hlayer : layer = later :=
              (List.nodup_ofFn.mp (hnodup index)) heq
            have hval := congrArg Fin.val hlayer
            change physical = later.val at hval
            omega
          have htrace :
              (FiniteUnambiguousFBDD.Walk.cons edge tail).queryTrace =
                order index layer :: tail.queryTrace := by
            simp [FiniteUnambiguousFBDD.Walk.queryTrace,
              FiniteUnambiguousFBDD.Walk.queryEvents, selectorFBDD,
              selectorNode, selectorComponent, hlt, layer, hquery,
              FiniteUFBDDNode.queryEvent?]
          rw [htrace]
          constructor
          · exact List.nodup_cons.mpr ⟨hnotmem, htail.1⟩
          · intro queryIndex hmem
            simp only [List.mem_cons] at hmem
            rcases hmem with rfl | hmem
            · exact ⟨layer, by simp [layer], rfl⟩
            · obtain ⟨later, hlater, heq⟩ := htail.2 _ hmem
              exact ⟨later, le_trans (by omega) hlater, heq⟩
        · have htail := ih (physical + 1) (by omega)
            ((family.program index).next layer state (some true))
            middle target tail hmiddle
          have hnotmem : order index layer ∉ tail.queryTrace := by
            intro hmem
            obtain ⟨later, hlater, heq⟩ := htail.2 _ hmem
            have hlayer : layer = later :=
              (List.nodup_ofFn.mp (hnodup index)) heq
            have hval := congrArg Fin.val hlayer
            change physical = later.val at hval
            omega
          have htrace :
              (FiniteUnambiguousFBDD.Walk.cons edge tail).queryTrace =
                order index layer :: tail.queryTrace := by
            simp [FiniteUnambiguousFBDD.Walk.queryTrace,
              FiniteUnambiguousFBDD.Walk.queryEvents, selectorFBDD,
              selectorNode, selectorComponent, hlt, layer, hquery,
              FiniteUFBDDNode.queryEvent?]
          rw [htrace]
          constructor
          · exact List.nodup_cons.mpr ⟨hnotmem, htail.1⟩
          · intro queryIndex hmem
            simp only [List.mem_cons] at hmem
            rcases hmem with rfl | hmem
            · exact ⟨layer, by simp [layer], rfl⟩
            · obtain ⟨later, hlater, heq⟩ := htail.2 _ hmem
              exact ⟨later, le_trans (by omega) hlater, heq⟩

/-- Root-level helper with a variable source.  Keeping the source as an
explicit variable avoids dependent elimination on a definitionally fixed
endpoint of `Walk`. -/
theorem selectorRootWalk_queryTrace_nodup_of_fixedMandatoryOrder
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (order : (index : family.Index) → Fin (family.layers index) → Fin n)
    (hfixed : ∀ index,
      (family.program index).HasFixedQueryOrder
        (fun layer => some (order index layer)))
    (hnodup : ∀ index, (List.ofFn (order index)).Nodup)
    (source target : family.SelectorVertex)
    (walk : (family.selectorFBDD).Walk source target)
    (hsource : source = selectorRoot) :
    walk.queryTrace.Nodup := by
  refine (FiniteUnambiguousFBDD.Walk.recOn
    (motive := fun source target walk =>
      source = selectorRoot → walk.queryTrace.Nodup)
    walk ?_ ?_) hsource
  · intro vertex _hvertex
    simp [FiniteUnambiguousFBDD.Walk.queryTrace,
      FiniteUnambiguousFBDD.Walk.queryEvents]
  · intro source middle target edge tail _htail hsource'
    subst source
    have hmiddle : ∃ index : family.Index,
        middle = selectorComponent index ⟨0, Nat.zero_lt_succ _⟩
          (family.program index).start := by
      classical
      letI : Fintype family.Index := family.indexFintype
      change middle ∈ family.selectorStartChildren at edge
      have hexists : ∃ index : family.Index,
          selectorComponent index ⟨0, Nat.zero_lt_succ _⟩
            (family.program index).start = middle := by
        simpa [selectorStartChildren] using edge
      obtain ⟨index, hindex⟩ := hexists
      exact ⟨index, hindex.symm⟩
    obtain ⟨index, rfl⟩ := hmiddle
    have htail :=
      selectorComponentWalk_queryTrace_spec_of_fixedMandatoryOrder
        family order hfixed hnodup index (family.layers index) 0
        (by omega) (family.program index).start _ target tail rfl
    have htrace :
        (FiniteUnambiguousFBDD.Walk.cons edge tail).queryTrace =
          tail.queryTrace := by
      simp [FiniteUnambiguousFBDD.Walk.queryTrace,
        FiniteUnambiguousFBDD.Walk.queryEvents, selectorFBDD, selectorNode,
        selectorRoot, FiniteUFBDDNode.queryEvent?]
    rw [htrace]
    exact htail.1

/-- A silent selector over mandatory fixed-order components is syntactically
read-once on every formal root path, not merely on compatible executions. -/
theorem selectorFBDD_isSyntacticallyReadOnce_of_fixedMandatoryOrder
    {n : Nat} (family : FiniteLayeredQueryProgramFamily n)
    (order : (index : family.Index) → Fin (family.layers index) → Fin n)
    (hfixed : ∀ index,
      (family.program index).HasFixedQueryOrder
        (fun layer => some (order index layer)))
    (hnodup : ∀ index, (List.ofFn (order index)).Nodup) :
    (family.selectorFBDD).IsSyntacticallyReadOnce := by
  intro target walk
  exact selectorRootWalk_queryTrace_nodup_of_fixedMandatoryOrder
    family order hfixed hnodup _ target walk rfl

end FiniteLayeredQueryProgramFamily

/-! ## Canonical mandatory-family specialization -/

/-- The completed static query order installed in one mandatory canonical
component. -/
def mandatoryBuiltRejectingGuardedCanonicalQueryOrder
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b) :
    Fin n → Fin n :=
  let scheduled := builtTimedAlphaVisitSchedule
    (cachedInputMachine machine) index.1
  let hmonotone := builtRejectingGuardedCanonicalIndexMonotone machine index
  let master := finiteCachedTimedAlphaScheduleMasterQueryOrder
    (n := n) scheduled hmonotone
  LayeredQueryProgram.completeMasterQuery master
    (builtRejectingGuardedCanonicalIndex_master_nodup machine n index)

/-- The mandatory canonical component exposes its fixed completed order, not
just semantic read-once behavior. -/
theorem mandatoryBuiltRejectingGuardedCanonicalComponent_hasFixedQueryOrder
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b) :
    (mandatoryBuiltRejectingGuardedCanonicalComponent machine n index)
      |>.HasFixedQueryOrder
        (fun layer => some
          (mandatoryBuiltRejectingGuardedCanonicalQueryOrder
            machine n index layer)) := by
  unfold mandatoryBuiltRejectingGuardedCanonicalComponent
    mandatoryBuiltRejectingGuardedCanonicalQueryOrder
  exact LayeredQueryProgram.collapseToMandatoryFixedOrder_hasFixedQueryOrder
    _ _ _

/-- The completed order of every canonical component is duplicate-free. -/
theorem mandatoryBuiltRejectingGuardedCanonicalQueryOrder_nodup
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n : Nat) {T b : Nat}
    (index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b) :
    (List.ofFn
      (mandatoryBuiltRejectingGuardedCanonicalQueryOrder
        machine n index)).Nodup := by
  let scheduled := builtTimedAlphaVisitSchedule
    (cachedInputMachine machine) index.1
  let hmonotone := builtRejectingGuardedCanonicalIndexMonotone machine index
  let master := finiteCachedTimedAlphaScheduleMasterQueryOrder
    (n := n) scheduled hmonotone
  let hmaster : master.Nodup := by
    dsimp [master, scheduled, hmonotone]
    exact builtRejectingGuardedCanonicalIndex_master_nodup machine n index
  change (List.ofFn
    (LayeredQueryProgram.completeMasterQuery master hmaster)).Nodup
  rw [LayeredQueryProgram.listOfFn_completeMasterQuery master hmaster]
  exact LayeredQueryProgram.completeMasterOrder_nodup master hmaster

/-- The finite mandatory canonical selector is a syntactic read-once FBDD.
This closes the gap between semantic read-once component executions and the
all-formal-path property required by the CLTW-style FBDD layer. -/
theorem mandatoryFiniteRejectingGuardedCanonicalSelector_isSyntacticallyReadOnce
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) :
    ((mandatoryFiniteRejectingGuardedCanonicalFamily machine n T b)
      |>.selectorFBDD).IsSyntacticallyReadOnce := by
  apply FiniteLayeredQueryProgramFamily.selectorFBDD_isSyntacticallyReadOnce_of_fixedMandatoryOrder
      (order := fun index =>
        mandatoryBuiltRejectingGuardedCanonicalQueryOrder machine n index)
  · intro index
    exact mandatoryBuiltRejectingGuardedCanonicalComponent_hasFixedQueryOrder
      machine n index
  · intro index
    exact mandatoryBuiltRejectingGuardedCanonicalQueryOrder_nodup
      machine n index

/-- Exact vertex count of the disjoint mandatory canonical selector.  The sum
is intentional: no sharing or polynomial compression is hidden here. -/
theorem mandatoryFiniteRejectingGuardedCanonicalSelector_vertex_card
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b : Nat) :
    @Fintype.card
        ((mandatoryFiniteRejectingGuardedCanonicalFamily machine n T b)
          |>.selectorFBDD).Vertex
        ((mandatoryFiniteRejectingGuardedCanonicalFamily machine n T b)
          |>.selectorFBDD).vertexFintype =
      (∑ index : BuiltRejectingGuardedCanonicalAlphaIndex machine T b,
        (n + 1) *
          (mandatoryBuiltRejectingGuardedCanonicalComponent
            machine n index).width) + 3 := by
  rw [FiniteLayeredQueryProgramFamily.selectorFBDD_vertex_card]
  unfold FiniteLayeredQueryProgramFamily.layeredStateSlotCount
  simp [mandatoryFiniteRejectingGuardedCanonicalFamily]

end OneTapeMagnification
end Frontier
end Pnp4
