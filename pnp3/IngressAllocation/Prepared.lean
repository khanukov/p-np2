import IngressAllocation.Extension
import IngressAllocation.Geometry
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
run_cmd do
  let env ← getEnv
  for (mod,key,aliasName) in [("Extension","extend_unique","extendUnique"),("Geometry","old_le_new","budgetMono"),
      ("Geometry","envelope_room","envelopeRoom"),("Geometry","twelve_fields_bound","fieldsBound")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private.IngressAllocation."++mod++".") && n.toString.endsWith (".IngressAllocation."++key)
    match found with
    | [(n,.thmInfo ci)] =>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique theorem interface {mod}/{key}: {found.map Prod.fst}"
private theorem extension_self {states N C B : Nat} (h : C ≤ B) (c : Config states N C) :
    FixedPairParser.ConfigExtension h c (extendConfig h c) := by
  refine ⟨rfl,rfl,?_,?_⟩
  · intro i
    change (if hi : i.val < tapeLength N C then c.tape ⟨i.val,hi⟩ else none)=c.tape i
    rw [dif_pos i.isLt]
  · intro j hj
    change (if hi : j.val < tapeLength N C then c.tape ⟨_,hi⟩ else none)=none
    rw [dif_neg (by omega)]
private theorem prepared_interval (k R S n p t : Nat) (positive : 1 ≤ R) (small : S ≤ R)
    (width : n ≤ R) (phys : p < S)
    (c : Config (BodyIngress.machine k).stateCount R (FixedRawLengthFence.allocation R))
    (heads : ∀ u,u ≤ t → ((BodyIngress.machine k).run u c).head.val ≤
      SerializedBody.delimiter (FixedRawLengthFence.fencePos R) (S-p) n 12) :
    ∀ u,u ≤ t → FixedPairParser.ConfigExtension (budgetMono k R)
      ((BodyIngress.machine k).run u c)
      ((BodyIngress.machine k).run u (extendConfig (budgetMono k R) c)) := by
  intro u hu
  apply FixedPairParser.run_extension (BodyIngress.machine k) (budgetMono k R) (extension_self _ c) u
  intro v hv
  have bound:=heads v (by omega)
  have geometry:=fieldsBound R (S-p) n (by omega) width positive
  have strict:=envelopeRoom R
  omega
end IngressAllocation
