import UniformClassBridgeClosure.TM0OrdinaryTrace

/-! Unconditional same-language inclusion for the literal Ordinary finite-TM0 model.
The complete finite enumeration is fixed with the machine, before all lengths/inputs.
Decider correctness proves circuit correctness and is never circuit construction data.
The differently typed legacy ContentVerifierBridge is not filled by this route. -/
namespace UniformClassBridgeClosure.Ordinary
open Turing Pnp3.ComplexityInterfaces

theorem uniformP_ppolyDAG (L : Language) (h : UniformP L) :
    Pnp3.ComplexityInterfaces.PpolyDAG L := by
  classical
  obtain ⟨Λ, finiteLabels, initialLabel, T, accept, reject, c, decides⟩ := h
  letI : Fintype Λ := finiteLabels
  letI : Inhabited Λ := initialLabel
  have different : accept ≠ reject := (decides 0 Fin.elim0).1
  apply TM0DAG.Window.literal_decider_ppolyDAG L (Finset.univ.toList)
    (by intro q; simp) T accept reject different c
  intro N y
  obtain ⟨_, t, last, bound, reached, verdict, halted, _⟩ := decides N y
  refine ⟨t, last, bound, ?_, verdict, halted⟩
  rw [← trace_eq_rawTrace, inputConfig_eq_init]
  exact reached

theorem check_uniformP_ppolyDAG (L : Language) :
    UniformClassBridgeClosure.Ordinary.UniformP L →
      Pnp3.ComplexityInterfaces.PpolyDAG L :=
  uniformP_ppolyDAG L

#check (UniformP : Language → Prop)
#check (Pnp3.ComplexityInterfaces.PpolyDAG : Language → Prop)
#check (uniformP_ppolyDAG : ∀ L : Language,
  UniformClassBridgeClosure.Ordinary.UniformP L → Pnp3.ComplexityInterfaces.PpolyDAG L)
#check (check_uniformP_ppolyDAG : ∀ L : Language,
  UniformClassBridgeClosure.Ordinary.UniformP L → Pnp3.ComplexityInterfaces.PpolyDAG L)
#print axioms uniformP_ppolyDAG
#print axioms check_uniformP_ppolyDAG
end UniformClassBridgeClosure.Ordinary
