import VirtualFinalClosure.WeightGrowthDriver
import VirtualFinalClosure.ComputeWeight
import VirtualFinalClosure.WeightRound
import VirtualFinalClosure.CapMeaning
import VirtualFinalClosure.Recompute
namespace VirtualFinalClosure.CompleteWeight
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",(2:Nat)),
      ("VirtualFinalClosure.CapacityImage","VirtualFinalClosure.CapacityImage","image","image",0),
      ("VirtualFinalClosure.CapacityImage","VirtualFinalClosure.CapacityImage","frame","imageFrame",1),
      ("VirtualFinalClosure.CapacityImage","VirtualFinalClosure.CapacityImage","low","imageLow",1),
      ("VirtualFinalClosure.CapacityImage","VirtualFinalClosure.CapacityImage","digits","imageDigits",1),
      ("VirtualFinalClosure.CapacityImage","VirtualFinalClosure.CapacityImage","tail","imageTail",1),
      ("VirtualFinalClosure.ComputeWeight","VirtualFinalClosure.ComputeWeight","prepared","computeWeight",1),
      ("VirtualFinalClosure.WeightGrowthDriver","VirtualFinalClosure.WeightGrowthDriver","phase_price","phasePrice",1),
      ("VirtualFinalClosure.WeightGrowthDriver","VirtualFinalClosure.WeightGrowthDriver","driver","driver",1),
      ("VirtualFinalClosure.WeightCapFrame","VirtualFinalClosure.WeightCapFrame","residual","residual",0),
      ("VirtualFinalClosure.CapMeaning","VirtualFinalClosure.CapMeaning","cap_shortage","capShortage",1),
      ("VirtualFinalClosure.WeightCapCycle","VirtualFinalClosure.WeightCapCycle","cycle","cycle",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong actual length-growth driver interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual length-growth driver interface {mod}/{key}"
/-- Actual computed bitLength endpoint -> ALL further literal W-growth
iterations -> successful q430. No fits/success assumption is imported: every
native cap supplies the strict measure decrease through its exact semantics. -/
private theorem from_length (k N B S L n Q F K C : Nat) (T : Nat → Option Bool) (m : Fin 144)
    (ph : phase m.val=1) (positive : 0 < C) (ck : C ≤ 2*K)
    (ellFits : bitLength n ≤ C) (wk : Cursor.Target.W k n ≤ K)
    (fr : Frame T S L (L+n+1) Q F)
    (reg : ∀ i,S < i → i < L → T i=some false)
    (assn : ∀ i,L < i → i < L+n+1 → T i=some false)
    (fit : F+10*K+n+7 < tapeLength N B) :
    let Y:=RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (image T F C) L n F C) L n F C
    let start : Config (machine k).stateCount N B:=
      ⟨control k (tableControl k 308) m,⟨L,by obtain ⟨_sl,_lh,_qp,room,_,_,_,_,_,_,_,_,_⟩:=fr;omega⟩,fun i=>Y i.val⟩
    ∃ (t j finalC : Nat) (hd : F+finalC+n+3 < tapeLength N B),
      t ≤ (Cursor.Target.W k n-C+1)*(4194304*(k+1)*(F+10*K+n+9)^3) ∧
      finalC=C*2^j ∧ Cursor.Target.W k n ≤ finalC ∧ finalC ≤ 2*K ∧
      (machine k).run t start=
        ⟨control k (tableControl k (430+93*k)) m,⟨F+finalC+n+3,hd⟩,
          fun i=>residual T L n F finalC 0 (n^k+k) (Cursor.Target.W k n) 0 0 i.val⟩ ∧
      (∀ u,u ≤ t → ((machine k).run u start).head.val ≤ L+16*(F+10*K+n+8)) := by
  intro Y start
  have currentFit : F+5*C+n+7 < tapeLength N B:=lt_of_le_of_lt (by omega) fit
  obtain ⟨a0,b0,ap,bp,_seedTrace,_weightTrace,aheads,_first,outcome⟩:=
    computeWeight k N B S L n Q F C T m ph fr positive ellFits currentFit
  have price : a0+b0 ≤ 4096*(n+C+1)*(F+5*C+n+9)+16*(F+5*C+n+8)+2097152*(k+1)*(n+C+1)^2*(F+5*C+n+9):=by omega
  rcases outcome with ⟨fitsW,atW⟩|⟨v2,v3,v4,v5,d0,cap,atCap⟩
  · have cost : a0+b0 ≤ 4194304*(k+1)*(F+10*K+n+9)^3:=by
      simpa only [Nat.add_zero] using phasePrice k n F K C S (a0+b0) 0 ck price (by omega)
    refine ⟨a0+b0,0,C,by omega,?_,by simp,fitsW,ck,atW,?_⟩
    · have q : Cursor.Target.W k n-C=0:=by omega
      simpa only [q,Nat.zero_add,Nat.one_mul] using cost
    · intro u hu;exact (aheads u hu).trans (by omega)
  · change (machine k).run (a0+b0) start=
        ⟨control k (tableControl k (798+93*k)) m,⟨F+1,by omega⟩,
          fun i=>residual T L n F C v2 v3 v4 v5 d0 i.val⟩ at atCap
    have shortage:=capShortage k n C v2 v3 v4 v5 d0 cap
    have nextCapacity : 2*C ≤ 2*K:=by omega
    obtain ⟨d,hs,dp,grown,dheads⟩:=cycle k N B S L n Q F C v2 v3 v4 v5 d0 T m ph positive fr assn currentFit
    obtain ⟨v,j,finalC,hf,vp,formula,large,limit,done,vheads⟩:=
      driver k N B S L n Q F K (2*C) T m ph (by omega) nextCapacity (by omega) wk fr reg assn fit
    have combined:=phasePrice k n F K C S (a0+b0) d ck price dp
    refine ⟨a0+b0+d+v,j+1,finalC,hf,?_,?_,large,limit,?_,?_⟩
    · have measures : Cursor.Target.W k n-2*C+2 ≤ Cursor.Target.W k n-C+1:=by omega
      calc
        a0+b0+d+v ≤ 4194304*(k+1)*(F+10*K+n+9)^3+
            (Cursor.Target.W k n-2*C+1)*(4194304*(k+1)*(F+10*K+n+9)^3):=Nat.add_le_add combined vp
        _ = (Cursor.Target.W k n-2*C+2)*(4194304*(k+1)*(F+10*K+n+9)^3):=by ring
        _ ≤ (Cursor.Target.W k n-C+1)*(4194304*(k+1)*(F+10*K+n+9)^3):=Nat.mul_le_mul_right _ measures
    · rw [formula,Nat.pow_succ];ring
    · rw [UniformTM.run_add,UniformTM.run_add,atCap,grown]
      exact done
    · intro u hu
      by_cases early : u ≤ a0+b0
      · exact (aheads u early).trans (by omega)
      · by_cases middle : u ≤ a0+b0+d
        · rw [show u=(a0+b0)+(u-(a0+b0)) by omega,UniformTM.run_add,atCap]
          exact (dheads (u-(a0+b0)) (by omega)).trans (by omega)
        · rw [show u=(a0+b0+d)+(u-(a0+b0+d)) by omega,UniformTM.run_add,UniformTM.run_add,atCap,grown]
          exact vheads (u-(a0+b0+d)) (by omega)
#print axioms from_length
end VirtualFinalClosure.CompleteWeight
