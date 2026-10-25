import VirtualFinalClosure.RejectedPrefix
namespace VirtualFinalClosure.RejectedRaw
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("VirtualFinalClosure.RejectedPrefix","VirtualFinalClosure.RejectedPrefix","rejected","rejected"),
      ("VirtualFinalClosure.Resources","VirtualFinalClosure.Resources","old_le_new","oldNew"),
      ("VirtualFinalClosure.Resources","VirtualFinalClosure.Resources","prefix_price","prefixPrice"),
      ("VirtualFinalClosure.Resources","VirtualFinalClosure.Resources","prefix_space","prefixSpace")] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,.thmInfo ci)]=>
      logInfo m!"private-term|{name}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique raw exact rejection handoff {mod}/{key}"
private theorem raw_reject (k N t : Nat) (y : Bitstring N)
    (price:t ≤ CertificateGuardClosure.deadline k N)
    (heads:∀ u,u ≤ t → ((CertificateGuardClosure.machine k).run u
      (initialConfig (CertificateGuardClosure.machine k) (CertificateGuardClosure.allocation k N) y)).head.val ≤ 12*(N+1)^2)
    (low:∀ u,u ≤ t → ((CertificateGuardClosure.machine k).run u
      (initialConfig (CertificateGuardClosure.machine k) (CertificateGuardClosure.allocation k N) y)).state.val < 625)
    (hit:((CertificateGuardClosure.machine k).run t
      (initialConfig (CertificateGuardClosure.machine k) (CertificateGuardClosure.allocation k N) y)).state=(CertificateGuardClosure.machine k).reject)
    (sound:encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y=false) :
    let O:=CertificateGuardClosure.machine k;let C0:=CertificateGuardClosure.allocation k N;let B:=allocation k N
    let c:=initialConfig (machine k) B y;let old:=initialConfig O C0 y
    ∃ T,T ≤ deadline k N ∧
      (∀ u,u ≤ T → ((machine k).run u c).head.val ≤ spaceBound k N) ∧
      (∀ u,u < T → ((machine k).run u c).state≠(machine k).accept ∧ ((machine k).run u c).state≠(machine k).reject ∧
        ∀ (mode:Fin 3) (flag:Fin 144),((machine k).run u c).state≠control k
          (CertificateGuardClosure.old k (TotalIngressClosure.old k (BodyIngress.body k (SerializedBody.entry mode)))) flag) ∧
      ∃ (h:C0 ≤ B) (s:Nat),s=T ∧ s ≤ CertificateGuardClosure.deadline k N ∧ (O.run s old).state=O.reject ∧
        (machine k).run T c=config k ⟨8,by decide⟩ (IngressAllocation.extendConfig h (O.run s old)) ∧
        encodedRelationLanguage (PartAEndpoint.thresholdContentWitnessRelation k) N y=false:=by
  intro O C0 B c old
  obtain ⟨s,st,hit,done,first,bounds⟩:=rejected k N t y heads low hit
  exact ⟨s,(st.trans price).trans (prefixPrice k N),fun u hu=>(bounds u hu).trans (prefixSpace k N),first,
    oldNew k N,s,rfl,st.trans price,hit,done,sound⟩
#print axioms raw_reject
end VirtualFinalClosure.RejectedRaw
