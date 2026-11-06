import VirtualFinalClosure.LengthGrowthDriver
import VirtualFinalClosure.CompleteWeight
import VirtualFinalClosure.ComputedPostWeight
namespace VirtualFinalClosure.TightGrowth
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.LengthGrowthDriver","VirtualFinalClosure.LengthGrowthDriver","driver","lengthDriver",(1:Nat)),
      ("VirtualFinalClosure.CompleteWeight","VirtualFinalClosure.CompleteWeight","from_length","completeWeight",1),
      ("VirtualFinalClosure.ComputedPostWeight","VirtualFinalClosure.ComputedPostWeight","prepared","postLength",1),
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",2),
      ("VirtualFinalClosure.CapMeaning","VirtualFinalClosure.CapMeaning","weight_lower","weightLower",1),
      ("VirtualFinalClosure.WeightCapFrame","VirtualFinalClosure.WeightCapFrame","residual","residual",0),
      ("VirtualFinalClosure.CapacityImage","VirtualFinalClosure.CapacityImage","image","capacityImage",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong literal tight-capacity driver interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique literal tight-capacity driver interface {mod}/{key}"

/-- Same actual native bitLength/power/W/bitLengthW rows, with W as the proof
horizon. No W is installed at entry; its physical computation is inherited from
those literal drivers. The final occupied capacity is at most 2W, including n0. -/
private theorem prepared (k N B S L n Q F C : Nat) (T : Nat → Option Bool) (m : Fin 144)
    (ph : phase m.val=1) (positive : 0 < C) (limit : C ≤ 2*Cursor.Target.W k n)
    (fr : Frame T S L (L+n+1) Q F)
    (reg : ∀ i,S < i → i < L → T i=some false)
    (assn : ∀ i,L < i → i < L+n+1 → T i=some false)
    (fit : F+10*Cursor.Target.W k n+n+7 < tapeLength N B) :
    let W:=Cursor.Target.W k n
    let start : Config (machine k).stateCount N B:=
      ⟨control k (tableControl k 98) m,⟨S,by obtain ⟨sl,_lh,qp,room,_,_,_,_,_,_,_,_,_⟩:=fr;omega⟩,
        fun j=>capacityImage T F C j.val⟩
    ∃ (a b u j0 C0 j1 C1 : Nat) (h0 : F+1 < tapeLength N B),
      C0=C*2^j0 ∧ bitLength n ≤ C0 ∧ C0 ≤ 2*W ∧
      C1=C0*2^j1 ∧ W ≤ C1 ∧ C1 ≤ 2*W ∧
      a ≤ (bitLength n-C+1)*(8192*(F+10*W+n+9)^2) ∧
      b ≤ (W-C0+1)*(4194304*(k+1)*(F+10*W+n+9)^3) ∧
      u ≤ 4096*(W+1)*(F+5*C1+n+8)^2 ∧
      (machine k).run (a+b+u) start=
        ⟨control k (tableControl k (613+93*k)) m,⟨F+1,h0⟩,
          fun j=>residual T L n F C1 (bitLength W) 0 0 W 0 j.val⟩ ∧
      (∀ v,v ≤ a+b+u → ((machine k).run v start).head.val ≤ L+16*(F+10*W+n+8)):=by
  intro W start
  have ell : bitLength n ≤ W:=by have h:=(weightLower k n).1;omega
  have frCopy:=fr
  obtain ⟨sl,lh,qp,room,_,_,_,_,_,_,_,_,_⟩:=frCopy
  obtain ⟨a,j0,C0,hl,ap,form0,ellFits,limit0,at308,heads0⟩:=
    lengthDriver k N B S L n Q F W C T m ph positive limit ell fr reg assn fit
  have positive0 : 0 < C0:=by rw [form0];exact Nat.mul_pos positive (Nat.two_pow_pos j0)
  obtain ⟨b,j1,C1,hd,bp,form1,wFits,limit1,at430,heads1⟩:=
    completeWeight k N B S L n Q F W C0 T m ph positive0 limit0 ellFits le_rfl fr reg assn fit
  have positive1 : 0 < C1:=by rw [form1];exact Nat.mul_pos positive0 (Nat.two_pow_pos j1)
  have fit1 : F+5*C1+n+7 < tapeLength N B:=lt_of_le_of_lt (by omega) fit
  obtain ⟨u,up,at613,heads2,_first⟩:=postLength k N B S L n Q F C1 T m ph fr positive1 wFits fit1
  refine ⟨a,b,u,j0,C0,j1,C1,by omega,form0,ellFits,limit0,form1,wFits,limit1,ap,bp,up,?_,?_⟩
  · rw [UniformTM.run_add,UniformTM.run_add,at308,at430]
    exact at613
  · intro v hv
    by_cases early : v ≤ a
    · exact (heads0 v early).trans (by omega)
    · by_cases middle : v ≤ a+b
      · rw [show v=a+(v-a) by omega,UniformTM.run_add,at308]
        exact heads1 (v-a) (by omega)
      · rw [show v=(a+b)+(v-(a+b)) by omega,UniformTM.run_add,UniformTM.run_add,at308,at430]
        exact (heads2 (v-(a+b)) (by omega)).2.trans (by omega)
#print axioms prepared
end VirtualFinalClosure.TightGrowth
