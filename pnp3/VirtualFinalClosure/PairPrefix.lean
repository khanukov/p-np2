import VirtualFinalClosure.Resources
import VirtualFinalClosure.ConfigFields
import CertificateGuardClosure.Sequence
import TotalIngressClosure.SeqTrace
namespace VirtualFinalClosure.PairPrefix
open Pnp3.Complexity.Uniform.V1 PairEncoding Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("CertificateGuardClosure.GuardRun","CertificateGuardClosure","guard_run","guardRun"),
      ("CertificateGuardClosure.Sequence","CertificateGuardClosure","gate_entry","gateEntry"),
      ("CertificateGuardClosure.Sequence","CertificateGuardClosure","gate_low","gateLow"),
      ("CertificateGuardClosure.Sequence","CertificateGuardClosure","gate_heads","gateHeads"),
      ("CertificateGuardClosure.Sequence","CertificateGuardClosure","parser_heads","parserHeads"),
      ("CertificateGuardClosure.Sequence","CertificateGuardClosure","include_suffix","includeSuffix"),
      ("CertificateGuardClosure.Sequence","CertificateGuardClosure","parser_low","parserLow"),
      ("TotalIngressClosure.SeqTrace","TotalIngressClosure","seq_suffix","parserSuffix"),
      ("VirtualFinalClosure.ConfigFields","VirtualFinalClosure.ConfigFields","guarded","guardedState")] do
    let found:=env.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,.thmInfo ci)]=>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique exact double-parser physical prefix {mod}/{key}"
private theorem raw_entry (k B : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (canonical : m=a+1) (room : 2*pairLength a m+3<tapeLength (pairLength a m) B)
    (parserRoom : FixedPairParser.clock (pairLength a m)≤B) :
    let R:=pairLength a m;let y:=encodePair x w;let M:=CertificateGuardClosure.machine k
    let c:=initialConfig M B y;let b:=initialConfig (BodyIngress.machine k) B y
    ∃ g,g≤128*(R+1)^2 ∧
      (∀ u,u<g → (M.run u c).state.val<87) ∧
      (∀ u,u≤g → (M.run u c).head.val≤12*(R+1)^2) ∧
      (∀ u,M.run (g+u) c=CertificateGuardClosure.config k
        (TotalIngressClosure.config k ((BodyIngress.machine k).run u b))) := by
  intro R y M c b
  have parsed:decodePair y=some ((⟨a,x⟩,⟨m,w⟩):DecodedPair):=decodePair_roundtrip x w
  obtain ⟨h,price,guardHeads,first,done⟩:=guardRun (B:=B) x w room
  rw [if_pos canonical] at done
  let p:=FixedPairParser.clock R
  let g:=p+h
  have entry : M.run g c=CertificateGuardClosure.config k
      (initialConfig (TotalIngressClosure.machine k) B y) :=
    gateEntry (TotalIngressClosure.machine k) y parserRoom _ parsed (fun u hu=>(first u hu).1) done
  have runTotal (u : Nat) : M.run (g+u) c=CertificateGuardClosure.config k
      ((TotalIngressClosure.machine k).run u (initialConfig (TotalIngressClosure.machine k) B y)) := by
    rw [UniformTM.run_add,entry]
    exact includeSuffix (TotalIngressClosure.machine k) _ u
  have suffix (u : Nat) : M.run ((g+p)+u) c=CertificateGuardClosure.config k
      (TotalIngressClosure.config k ((BodyIngress.machine k).run u b)) := by
    rw [show g+p+u=g+(p+u) by omega,runTotal]
    exact congrArg (CertificateGuardClosure.config k)
      (parserSuffix (BodyIngress.machine k) y parserRoom _ parsed u)
  have bound : g+p≤128*(R+1)^2 := by
    have small:p=2*R+1:=rfl
    have hp:h≤64*(R+1)^2:=price
    dsimp only [g]
    nlinarith only [hp,small,Nat.zero_le R,Nat.zero_le (R^2)]
  have envelope : 2*R+3≤12*(R+1)^2 := by
    nlinarith only [Nat.zero_le R,Nat.zero_le (R^2)]
  refine ⟨g+p,bound,?_,?_,suffix⟩
  · intro u hu
    by_cases early : u<g
    · exact (gateLow (TotalIngressClosure.machine k) y parserRoom _ parsed first u early).trans (by decide)
    · rw [show u=g+(u-g) by omega,runTotal]
      have small:=parserLow (BodyIngress.machine k) y parserRoom (u-g) (by change u-g<FixedPairParser.clock R;omega)
      rw [guardedState]
      change ((TotalIngressClosure.machine k).run (u-g) (initialConfig (TotalIngressClosure.machine k) B y)).state.val<10 at small
      omega
  · intro u hu
    by_cases early : u≤g
    · exact (gateHeads (TotalIngressClosure.machine k) y parserRoom _ parsed (fun v hv=>(first v hv).1)
        guardHeads (by omega) u early).trans envelope
    · rw [show u=g+(u-g) by omega,runTotal]
      have small:=parserHeads (BodyIngress.machine k) y parserRoom (u-g) (by change u-g≤FixedPairParser.clock R;omega)
      exact small.trans (by nlinarith only [Nat.zero_le R,Nat.zero_le (R^2)])
#print axioms raw_entry
end VirtualFinalClosure.PairPrefix
