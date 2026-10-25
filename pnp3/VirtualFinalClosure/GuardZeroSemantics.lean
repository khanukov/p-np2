import VirtualFinalClosure.GuardDecision
namespace VirtualFinalClosure.GuardZeroSemantics
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion Pnp4.AlgorithmsToLowerBounds Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("VirtualFinalClosure.GuardMeaning","VirtualFinalClosure.GuardMeaning","readNatBE_zero","readZero"),
      ("VirtualFinalClosure.GuardDecision","VirtualFinalClosure.GuardDecision","virtual_test","virtualTest")] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,.thmInfo ci)]=>
      logInfo m!"private-term|{name}|kind=theorem|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique original zero-source semantic term {mod}/{key}"
private theorem padded_zero {S : Nat} (word : Bitstring S) (p : Nat)
    (zero : ∀ i,p ≤ i → i < S → padRead word i=false) :
    ∀ i,p ≤ i → padRead word i=false:=by
  intro i hi
  by_cases inside : i < S
  · exact zero i hi inside
  · exact padRead_ge word (by omega)
/-- The ACTUAL all-zero physical suffix fast path really validates the BE
index and BOTH prefix/padding windows, even when W is far beyond the source.
This proves a semantic optimization, not permission to reject other W>r paths. -/
private theorem zero_suffix {a m n consumed : Nat} (k : Nat) (x : Bitstring a) (w : Bitstring m)
    (canonical : m=a+1) (header : contentHeader? (Fin.append x w)=some (n,consumed))
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (virtual : a+m ≤ treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n)
    (zero : ∀ i,tagLen+consumed+Pnp3.Models.Partial.tableLen n ≤ i → i < a+m →
      padRead (Fin.append x w) i=false) :
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true ↔
      0<n ∧ ∀ j : Fin (2^n),padRead (Fin.append x w) (tagLen+consumed+j.val)=Nat.testBit j.val 0:=by
  let codec:=treeCircuitWitnessCodec (thresholdPoly k)
  let word:=Fin.append x w
  let p:=tagLen+consumed+Pnp3.Models.Partial.tableLen n
  let ell:=idxWidth codec.witnessBits n
  let W:=codec.witnessBits n
  let M:=treeMCSPPrefixM codec n
  have every:=padded_zero word p zero
  have layout : p+ell+W=M:=by
    dsimp only [p,ell,W,M,treeMCSPPrefixM]
    rw [contentHeader?_consumed_eq_gammaLen word header]
  have readI : readNatBE (padWord word M) p ell=some 0:=by
    apply readZero _ _ _ (by omega)
    intro j
    change padRead word (p+j.val)=false
    exact every _ (by omega)
  have payload : ∀ j : Fin W,padRead word (p+ell+j.val)=false:=by
    intro j
    exact every _ (by omega)
  have exactTest:=virtualTest k x w canonical header tag readI virtual
  constructor
  · intro accepted
    obtain ⟨positive,_fit,_zero,table⟩:=exactTest.mp accepted
    exact ⟨positive,table⟩
  · rintro ⟨positive,table⟩
    exact exactTest.mpr ⟨positive,Nat.zero_le _,payload,table⟩
private theorem last_odd (n : Nat) (positive : 0<n) : Nat.testBit (2^n-1) 0=true:=by
  cases n with
  | zero=>omega
  | succ n=>
    have pos:=Nat.two_pow_pos n
    have mod : (2^(n+1)-1)%2=1:=by rw [Nat.pow_succ];omega
    simp only [Nat.testBit_zero,mod,decide_true]
/-- Original input0 truth-table acceptance forces its LAST (odd) true row to
be physically present. This fact is scoped to that virtual circuit; it is not
an unrelated W-cap rejection rule. -/
private theorem table_physical {S n : Nat} (word : Bitstring S) (A : Nat) (positive : 0<n)
    (table : ∀ j : Fin (2^n),padRead word (A+j.val)=Nat.testBit j.val 0) : A+2^n ≤ S:=by
  have pos:=Nat.two_pow_pos n
  have last:=table ⟨2^n-1,by omega⟩
  rw [last_odd n positive] at last
  by_contra outside
  have blank : padRead word (A+(2^n-1))=false:=padRead_ge word (by omega)
  rw [blank] at last
  cases last
#print axioms padded_zero
#print axioms zero_suffix
#print axioms last_odd
#print axioms table_physical
end VirtualFinalClosure.GuardZeroSemantics
