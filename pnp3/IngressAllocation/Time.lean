import IngressAllocation.Target
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1
private theorem first_unique (M : UniformTM) {N B s t : Nat} (c : Config M.stateCount N B)
    (P : Fin M.stateCount → Prop) (atS : P (M.run s c).state) (atT : P (M.run t c).state)
    (firstS : ∀ u,u < s → ¬P (M.run u c).state)
    (firstT : ∀ u,u < t → ¬P (M.run u c).state) : s=t := by
  rcases lt_trichotomy s t with early | same | late
  · exact False.elim (firstT s early atS)
  · exact same
  · exact False.elim (firstS t late atT)
private theorem append_heads (M : UniformTM) {N B t d P : Nat} (c : Config M.stateCount N B)
    (left : ∀ u,u ≤ t → (M.run u c).head.val ≤ P)
    (right : ∀ u,u ≤ d → (M.run u (M.run t c)).head.val ≤ P) :
    ∀ u,u ≤ t+d → (M.run u c).head.val ≤ P := by
  intro u hu
  by_cases early : u ≤ t
  · exact left u early
  · rw [show u=t+(u-t) by omega,UniformTM.run_add]
    exact right (u-t) (by omega)
end IngressAllocation
