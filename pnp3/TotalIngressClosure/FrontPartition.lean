import TotalIngressClosure.CapacityEqual
import TotalIngressClosure.WideReject
import TotalIngressClosure.ProducerRejectLift
import TotalIngressClosure.SyntacticTrace
import TotalIngressClosure.FrontGeometry
import TotalIngressClosure.MissingFirst
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
run_cmd do
  let env ← getEnv
  for (mod,key,aliasName) in [("Header","header_data","headerData"),
      ("SyntacticTrace","tag_reject","tagReject"),("SyntacticTrace","gamma_reject","gammaReject"),
      ("FrontGeometry","capacity_wide","capacityWide"),("FrontGeometry","missing_first_shape","missingShape"),
      ("ProducerRejectLift","producer_reject_lift","producerLift"),("WideReject","wide_reject","wideReject"),
      ("CapacityEqual","capacity_equal","capacityEqual"),("MissingFirst","missing_first","missingFirst"),
      ("TableReject","table_reject","tableReject")] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private.TotalIngressClosure."++mod++".") &&
      n.toString.endsWith (".TotalIngressClosure."++key)
    match found with
    | [(n,.thmInfo ci)]=>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique exhaustive physical front interface {mod}/{key}: {found.map Prod.fst}"
private theorem front_partition (k:Nat){a m:Nat}(x:Bitstring a)(w:Bitstring m) :
    let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
    let c:=initialConfig (BodyIngress.machine k) B (encodePair x w)
    (∃ t,t ≤ 4096*(R+1)^2 ∧ ((BodyIngress.machine k).run t c).state=(BodyIngress.machine k).reject ∧
      (∀ u,u ≤ t → ((BodyIngress.machine k).run u c).head.val ≤ 12*(R+1)^2) ∧
      (∀ u,u ≤ t → ((BodyIngress.machine k).run u c).state.val < 352)) ∨
    (∃ n z,FixedContentTagGate.tagMatches (Fin.append x w)=true ∧
      FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
      contentHeader? (Fin.append x w)=some (n,2*z+1) ∧ (z=0 ∨ 9+z < a+m) ∧
      n < FixedRawLengthFence.capacity a m z ∧
      2^n ≤ FixedRawLengthFence.fencePos R-(a+m+z+n+3)-1):=by
  intro R B c
  have grow(C:Nat)(h:C ≤ 4096)(t:Nat)(price:t ≤ C*(R+1)^2):t ≤ 4096*(R+1)^2:=
    price.trans (Nat.mul_le_mul_right _ h)
  cases tag:FixedContentTagGate.tagMatches (Fin.append x w) with
  | false=>
    obtain ⟨t,price,hit,_tape,_head,heads⟩:=tagReject x w tag
    obtain ⟨reject,foot,low⟩:=producerLift k x w t (12*(R+1)^2) hit heads
    exact Or.inl ⟨t,grow 128 (by decide) t price,reject,foot,low⟩
  | true=>
    cases gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w) with
    | none=>
      obtain ⟨t,price,hit,_tape,_head,heads⟩:=gammaReject x w tag gamma
      obtain ⟨reject,foot,low⟩:=producerLift k x w t (12*(R+1)^2) hit heads
      exact Or.inl ⟨t,grow 128 (by decide) t price,reject,foot,low⟩
    | some z=>
      obtain ⟨n,header,_lower,_upper,_borrow,_digits,_high⟩:=headerData x w gamma
      by_cases first:z=0 ∨ 9+z < a+m
      · by_cases cap:n < FixedRawLengthFence.capacity a m z
        · by_cases paid:2^n ≤ FixedRawLengthFence.fencePos R-(a+m+z+n+3)-1
          · exact Or.inr ⟨n,z,rfl,rfl,header,first,cap,paid⟩
          · exact Or.inl (tableReject k x w header tag gamma first cap paid)
        · have wide:=capacityWide x w header gamma (Nat.le_of_not_gt cap)
          by_cases equal:n=FixedRawLengthFence.capacity a m z
          · obtain ⟨t,price,reject,foot,low⟩:=capacityEqual k x w header tag gamma first wide equal
            exact Or.inl ⟨t,grow 144 (by decide) t price,reject,foot,low⟩
          · obtain ⟨t,price,hit,heads⟩:=wideReject x w header tag gamma wide (by omega)
            obtain ⟨reject,foot,low⟩:=producerLift k x w t (12*(R+1)^2) hit heads
            exact Or.inl ⟨t,grow 128 (by decide) t price,reject,foot,low⟩
      · obtain ⟨pos,shape⟩:=missingShape x w gamma first
        obtain ⟨t,price,reject,foot,low⟩:=missingFirst k x w tag gamma pos shape
        exact Or.inl ⟨t,grow 12 (by decide) t price,reject,foot,low⟩
end TotalIngressClosure
