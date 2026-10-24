import RawCallerClosure.Target
import RawCallerClosure.Work
namespace RawCallerClosure
open Pnp3.Complexity.Uniform.V1 PairEncoding Lean Elab Command
run_cmd do
  let e←getEnv
  for (owner,leaf) in [(`RawCallerClosure.Transport,"transport_prefix"),
    (`RawCallerClosure.Rows,"old_accept"),(`RawCallerClosure.Rows,"old_reject"),
    (`RawCallerClosure.Rows,"old_injective"),(`RawCallerClosure.Work,"old_not_done")] do
    let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "RawCallerClosure") leaf
    let some (.thmInfo ci):=e.find? n | throwError "Missing prefix support"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong prefix owner"
    logInfo m!"ordinary-raw-prefix|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private theorem prefix_facts (k N : Nat) (y : Bitstring N) (pre : Nat)
    (front:Target.Prelude k N y pre) :
    let B:=allocation k N;let C:=initialConfig (machine k) B y
    let G:=CertificateGuardClosure.machine k;let oldC:=initialConfig G B y
    let work (b : Bool):=CertificateGuardClosure.old k (TotalIngressClosure.old k
      (BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b))))
    (∀ u,u≤pre → (machine k).run u C=oldConfig k (G.run u oldC)) ∧
    (∀ u,u≤pre → ((machine k).run u C).state≠(machine k).accept) ∧
    (∀ u,u<pre → ((machine k).run u C).state≠(machine k).reject ∧
      ((machine k).run u C).state≠callerState k (PhysicalCallerClosure.rowsDone k) ∧
      (∀ b,((machine k).run u C).state≠old k (work b))) := by
  intro B C G oldC work
  rcases front with ⟨_price,_heads,safe,first,_outcome⟩
  have same:=transport_prefix k N B pre y (fun u hu=> (first u hu).2.2)
  refine ⟨same,?_,?_⟩
  · intro u hu
    rw [same u hu]
    intro bad
    change old k _=(machine k).accept at bad
    exact safe u hu (old_injective k (bad.trans (old_accept k).symm))
  · intro u hu
    rw [same u hu.le]
    refine ⟨?_,old_not_done k _,?_⟩
    · intro bad
      change old k _=(machine k).reject at bad
      exact (first u hu).1 (old_injective k (bad.trans (old_reject k).symm))
    · intro b bad
      change old k _=old k _ at bad
      exact (first u hu).2.1 b (old_injective k bad)
end RawCallerClosure
