import TotalIngressClosure.CanonicalTotal
import TotalIngressClosure.SeqTrace
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("TotalIngressClosure.CanonicalTotal","TotalIngressClosure","canonical_total","canonicalTotal"),
      ("TotalIngressClosure.CanonicalSpec","TotalIngressClosure","Outcome","Outcome"),
      ("TotalIngressClosure.CanonicalSpec","TotalIngressClosure","CanonicalResult","CanonicalResult"),
      ("TotalIngressClosure.FirstEvents","TotalIngressClosure","Before","Before"),
      ("TotalIngressClosure.Gate","TotalIngressClosure","budget_mono","budgetMono"),
      ("TotalIngressClosure.Gate","TotalIngressClosure","parser_room","parserRoom"),
      ("TotalIngressClosure.Gate","TotalIngressClosure","prefix_heads","parserHeads"),
      ("TotalIngressClosure.Gate","TotalIngressClosure","prefix_states","parserStates"),
      ("TotalIngressClosure.Gate","TotalIngressClosure","suffix","suffixRun"),
      ("TotalIngressClosure.SeqTrace","TotalIngressClosure","seq_span","seqSpan"),
      ("IngressAllocation.Endpoint","IngressAllocation","reallocate_prefix","reallocatePrefix")] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique concrete allocation-and-parser interface {mod}/{key}: {found.map Prod.fst}"
private theorem local_clock(k R d:Nat)(price:d ≤ 4294967296*(k+1)*(R+1)^3):
    FixedPairParser.clock R+d ≤ deadline k R:=by
  have small:2*R+1 ≤ (R+1)^3:=by nlinarith only [Nat.zero_le R,Nat.zero_le (R^2),Nat.zero_le (R^3)]
  have coeff:4294967296*(k+1)+1 ≤ 68719476736*(k+1):=by omega
  have half:FixedPairParser.clock R+d ≤ (4294967296*(k+1)+1)*(R+1)^3:=by
    change 2*R+1+d ≤ _
    nlinarith only [price,small]
  exact half.trans (Nat.mul_le_mul coeff (Nat.pow_le_pow_right (by omega) (by decide)))
private theorem input_head (N:Nat) : N ≤ 12*(N+1)^2:=by
  nlinarith only [Nat.zero_le N,Nat.zero_le (N^2)]
set_option maxRecDepth 4000 in
private theorem canonical_raw(k:Nat){a m:Nat}(x:Bitstring a)(w:Bitstring m):
    let N:=pairLength a m;let y:=encodePair x w
    let B:=allocation k N;let B0:=FixedRawLengthFence.allocation N
    let M:=machine k;let O:=BodyIngress.machine k
    let c:=initialConfig M B y;let c0:=initialConfig O B0 y;let large:=initialConfig O B y
    ∃ t,t ≤ deadline k N ∧
      (∀ u,u ≤ t → (M.run u c).head.val ≤ 12*(N+1)^2) ∧
      (∀ u,u ≤ t → (M.run u c).state≠M.accept) ∧
      (∀ u,u < t → (M.run u c).state≠M.reject ∧
        (∀ b,(M.run u c).state≠old k (BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b)))) ∧
        (∀ mode:Fin 3,(M.run u c).state≠old k (BodyIngress.body k (SerializedBody.entry mode)))) ∧
      ∃ d,t=FixedPairParser.clock N+d ∧
        (∀ u,M.run (FixedPairParser.clock N+u) c=config k (O.run u large)) ∧
        ∃ hBudget:B0 ≤ B,FixedPairParser.ConfigExtension hBudget c0 large ∧
          IngressAllocation.Footprint O (C:=B0) y d (12*(N+1)^2) ∧
          IngressAllocation.MoveRoom O (C:=B0) y d ∧ IngressAllocation.Trace O hBudget y d ∧
          M.run t c=config k (IngressAllocation.extendConfig hBudget (O.run d c0)) ∧ Outcome k x w d:=by
  intro N y B B0 M O c c0 large
  obtain ⟨d,price,heads,first,safe,outcome⟩:=canonicalTotal k x w
  have hBudget:B0 ≤ B:=budgetMono k N
  obtain ⟨room,trace,endRun⟩:=reallocatePrefix k N d y heads
  have suffixRun(u:Nat):M.run (FixedPairParser.clock N+u) c=config k (O.run u large):=
    suffixRun k y (parserRoom k N) _ (decodePair_roundtrip x w) u
  have initial:FixedPairParser.ConfigExtension hBudget c0 large:=FixedPairParser.initialConfig_extension O hBudget y
  let targets : Unit ⊕ (Bool ⊕ Fin 3) → Fin O.stateCount:=fun j=>match j with
    | .inl _=>O.reject
    | .inr (.inl b)=>BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b))
    | .inr (.inr mode)=>BodyIngress.body k (SerializedBody.entry mode)
  have before(u:Nat)(hu:u < d)(j:Unit ⊕ (Bool ⊕ Fin 3)):(O.run u c0).state≠targets j:=by
    rcases j with ⟨⟩|b|mode
    · exact (first u hu).1
    · exact (first u hu).2.1 b
    · exact (first u hu).2.2 mode
  obtain ⟨allHeads,allSafe,allFirst⟩:=seqSpan O hBudget y (parserRoom k N) _ (decodePair_roundtrip x w)
    trace heads (input_head N) safe targets before
  refine ⟨FixedPairParser.clock N+d,local_clock k N d price,allHeads,allSafe,?_,d,rfl,suffixRun,hBudget,initial,heads,room,trace,?_,outcome⟩
  · intro u hu
    exact ⟨allFirst u hu (.inl ()),fun b=>allFirst u hu (.inr (.inl b)),fun mode=>allFirst u hu (.inr (.inr mode))⟩
  · exact (suffixRun d).trans (congrArg (config k) (show O.run d large=IngressAllocation.extendConfig hBudget (O.run d c0) from endRun))
end TotalIngressClosure
