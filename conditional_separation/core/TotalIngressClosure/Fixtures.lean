import TotalIngressClosure.Raw
import CanonicalLeaf.Fixtures
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
run_cmd do
  let found:=(←getEnv).constants.toList.filter fun (n,_)=>n.toString.startsWith "_private.TotalIngressClosure.CanonicalTransport." &&
    n.toString.endsWith ".TotalIngressClosure.canonical_raw"
  match found with
  | [(n,.thmInfo ci)]=>
    logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit `canonicalRaw n::st.openDecls}
  | _=>throwError "Nonunique same-word actual raw theorem {found.map Prod.fst}"
set_option maxRecDepth 4000 in
private theorem tiny_connected :
    let x:Bitstring 7:=fun i=>i.val==0 || i.val==2 || i.val==3 || i.val==6
    let w:Bitstring 8:=fun i=>i.val==2 || i.val==5
    PartAEndpoint.thresholdContentWitnessRelation 0 7 8 x w=true ∧
      ∃ t,t ≤ deadline 0 (pairLength 7 8) ∧
        ((machine 0).run t (initialConfig (machine 0) (allocation 0 (pairLength 7 8)) (encodePair x w))).state=
          old 0 (BodyIngress.old 0 (CarryWindow.embed 0 (CanonicalLeaf.result 0 false))):=by
  intro x w
  have accepted:PartAEndpoint.thresholdContentWitnessRelation 0 7 8 x w=true:=CanonicalLeaf.tiny_accepted
  refine ⟨accepted,?_⟩
  obtain ⟨t,price,_heads,_safe,_first,d,_clock,_suffix,_hBudget,_initial,_foot,_room,_trace,finish,outcome⟩:=canonicalRaw 0 x w
  have oldResult:((BodyIngress.machine 0).run d (initialConfig (BodyIngress.machine 0)
      (FixedRawLengthFence.allocation (pairLength 7 8)) (encodePair x w))).state=
      BodyIngress.old 0 (CarryWindow.embed 0 (CanonicalLeaf.result 0 false)):=by
    rcases outcome with ⟨_reject,negative⟩|⟨n,z,_hH,_tag,gamma,header,_cap,_arena,result⟩
    · rw [accepted] at negative;contradiction
    · have actualGamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some 1:=by decide
      have equalZ:z=1:=Option.some.inj (gamma.symm.trans actualGamma)
      have actualHeader:contentHeader? (Fin.append x w)=some (1,3):=by decide
      have equalN:n=1:=congrArg Prod.fst (Option.some.inj (header.symm.trans actualHeader))
      rcases result with ⟨_phys,_ell,fits,_rest⟩|⟨_positive,_logical,_zeros,_decoded,leaf⟩
      · have bad:¬ Cursor.Target.W 0 1 ≤ 15-min (9+2*1+2^1) 15:=by decide
        exact False.elim (bad (by simpa only [equalZ,equalN] using fits))
      · rcases leaf with ⟨_eof,run⟩|⟨_phys,_reason,run⟩ <;> exact congrArg Config.state run
  refine ⟨t,price,?_⟩
  rw [finish]
  change old 0 _=old 0 _
  exact congrArg (old 0) oldResult
#print axioms tiny_connected
end TotalIngressClosure
