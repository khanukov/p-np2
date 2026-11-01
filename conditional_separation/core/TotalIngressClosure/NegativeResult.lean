import TotalIngressClosure.CanonicalSpec
import TotalIngressClosure.FrontPartition
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,key,aliasName) in [("CanonicalSpec","Outcome","Outcome"),("CanonicalSpec","CanonicalResult","CanonicalResult"),
      ("FirstEvents","reject_first","rejectFirst"),("EventSafety","leaf_val","leafVal")] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private.TotalIngressClosure."++mod++".") && n.toString.endsWith (".TotalIngressClosure."++key)
    match found with
    | [(n,ci)]=>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique literal-negative assembly {mod}/{key}: {found.map Prod.fst}"
set_option maxRecDepth 4000 in
private theorem negative_result (k:Nat){a m:Nat}(x:Bitstring a)(w:Bitstring m)(T:Nat)
    (price:T ≤ 4096*(pairLength a m+1)^2)
    (hit:((BodyIngress.machine k).run T (initialConfig (BodyIngress.machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=(BodyIngress.machine k).reject)
    (heads:∀ u,u ≤ T → ((BodyIngress.machine k).run u (initialConfig (BodyIngress.machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).head.val ≤ 12*(pairLength a m+1)^2)
    (low:∀ u,u ≤ T → ((BodyIngress.machine k).run u (initialConfig (BodyIngress.machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state.val < 352) :
    CanonicalResult k x w:=by
  let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
  let c:=initialConfig (BodyIngress.machine k) B (encodePair x w)
  have absent(u:Nat)(hu:u < T):
      (∀ b,((BodyIngress.machine k).run u c).state≠BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b))) ∧
      (∀ mode:Fin 3,((BodyIngress.machine k).run u c).state≠BodyIngress.body k (SerializedBody.entry mode)):=by
    have bound:((BodyIngress.machine k).run u c).state.val < 352:=low u hu.le
    constructor
    · intro b bad
      have eq:=congrArg Fin.val bad
      change ((BodyIngress.machine k).run u c).state.val=288+Cursor.stateCount k+(if b then 7 else 6) at eq
      unfold Cursor.stateCount at eq
      split_ifs at eq <;> omega
    · intro mode bad
      let q:Fin (CarryWindow.machine k).stateCount:=⟨((BodyIngress.machine k).run u c).state.val,by
        have size:(352:Nat) ≤ (CarryWindow.machine k).stateCount:=by
          change 352 ≤ 288+Cursor.stateCount k+8+25
          unfold Cursor.stateCount;omega
        omega⟩
      have equal:((BodyIngress.machine k).run u c).state=BodyIngress.old k q:=Fin.ext rfl
      exact (BodyIngress.embeddings k).2.2.2.2.2.2 q mode (equal.symm.trans bad)
  obtain ⟨s,st,reject,_whole,first,safe,negative⟩:=rejectFirst k x w T hit absent
  have p3:(R+1)^2 ≤ (R+1)^3:=Nat.pow_le_pow_right (by omega) (by decide)
  have coeff:4096 ≤ 4294967296*(k+1):=by omega
  refine ⟨s,st.trans (price.trans (Nat.mul_le_mul coeff p3)),?_,first,safe,?_⟩
  · intro u hu;exact heads u (hu.trans st)
  · exact Or.inl ⟨reject,negative⟩
end TotalIngressClosure
