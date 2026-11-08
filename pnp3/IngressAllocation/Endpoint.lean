import IngressAllocation.Prepared
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
run_cmd do
  let env ← getEnv
  for (mod,key,aliasName) in [("Geometry","old_le_new","budgetMono"),("Geometry","envelope_room","envelopeRoom"),
      ("Extension","trace_of_qualified_room","traceRoom"),("Extension","extend_unique","extendUnique")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private.IngressAllocation."++mod++".") && n.toString.endsWith (".IngressAllocation."++key)
    match found with
    | [(n,.thmInfo ci)] =>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique extension theorem {mod}/{key}: {found.map Prod.fst}"
/-- Uses the concrete footprint, independently of the elapsed clock. Includes literal left clamp. -/
private theorem reallocate_prefix (k R t : Nat) (y : Bitstring R)
    (heads : Footprint (BodyIngress.machine k) (C:=FixedRawLengthFence.allocation R) y t (12*(R+1)^2)) :
    let h:=budgetMono k R
    MoveRoom (BodyIngress.machine k) (C:=FixedRawLengthFence.allocation R) y t ∧
    Trace (BodyIngress.machine k) h y t ∧
    (BodyIngress.machine k).run t (initialConfig (BodyIngress.machine k) (allocation k R) y)=
      extendConfig h ((BodyIngress.machine k).run t
        (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation R) y)) := by
  have room : MoveRoom (BodyIngress.machine k) (C:=FixedRawLengthFence.allocation R) y t := by
    intro u hu
    dsimp only
    intro _
    have bound:=heads u (Nat.le_of_lt hu)
    have strict:=envelopeRoom R
    omega
  have trace:=traceRoom (BodyIngress.machine k) (budgetMono k R) y t room
  exact ⟨room,trace,extendUnique (budgetMono k R) (trace t le_rfl)⟩
private theorem transport_first_set (M : UniformTM) {N C B t : Nat} (h : C ≤ B)
    (y : Bitstring N) (states : Fin M.stateCount → Prop)
    (trace : Trace M h y t)
    (first : ∀ u,u < t → ¬states (M.run u (initialConfig M C y)).state) :
    ∀ u,u < t → ¬states (M.run u (initialConfig M B y)).state := by
  intro u hu
  rw [← (trace u (Nat.le_of_lt hu)).1]
  exact first u hu
private theorem transport_verdicts (M : UniformTM) {N C B t : Nat} (h : C ≤ B)
    (y : Bitstring N) (trace : Trace M h y t)
    (safe : ∀ u,u ≤ t → (M.run u (initialConfig M C y)).state ≠ M.accept ∧
      (M.run u (initialConfig M C y)).state ≠ M.reject) :
    ∀ u,u ≤ t → (M.run u (initialConfig M B y)).state ≠ M.accept ∧
      (M.run u (initialConfig M B y)).state ≠ M.reject := by
  intro u hu
  rw [← (trace u hu).1]
  exact safe u hu
end IngressAllocation
