import VirtualFinalClosure.WeightCapCycle
import VirtualFinalClosure.WeightRound
import VirtualFinalClosure.CapMeaning
import VirtualFinalClosure.Recompute
namespace VirtualFinalClosure.WeightGrowthDriver
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
      ("VirtualFinalClosure.WeightRound","VirtualFinalClosure.WeightRound","round","roundWeight",1),
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
private theorem phase_price (k n F K C S a d : Nat) (ck : C ≤ 2*K)
    (ap : a ≤ 4096*(n+C+1)*(F+5*C+n+9)+16*(F+5*C+n+8)+2097152*(k+1)*(n+C+1)^2*(F+5*C+n+9))
    (dp : d ≤ 2+(C*(4*C+7)+2*n+14*C+27)+(F-S+3)+1) :
    a+d ≤ 4194304*(k+1)*(F+10*K+n+9)^3 := by
  let D:=F+10*K+n+9
  have ce : C ≤ D:=by dsimp only [D];omega
  have ne : n ≤ D:=by dsimp only [D];omega
  have fe : F-S ≤ D:=by dsimp only [D];omega
  have aa : n+C+1 ≤ D:=by dsimp only [D];omega
  have ee : F+5*C+n+9 ≤ D:=by dsimp only [D];omega
  have b1:=Nat.mul_le_mul (Nat.mul_le_mul_left 4096 aa) ee
  have b2:=Nat.mul_le_mul_left 16 (show F+5*C+n+8 ≤ D by omega)
  have b3:=Nat.mul_le_mul (Nat.mul_le_mul_left (2097152*(k+1)) (Nat.pow_le_pow_left aa 2)) ee
  have ab : a ≤ 4096*D^2+16*D+2097152*(k+1)*D^3 := by
    calc
      a ≤ 4096*(n+C+1)*(F+5*C+n+9)+16*(F+5*C+n+8)+2097152*(k+1)*(n+C+1)^2*(F+5*C+n+9):=ap
      _ ≤ 4096*D*D+16*D+2097152*(k+1)*D^2*D:=Nat.add_le_add (Nat.add_le_add b1 b2) b3
      _ = _:=by ring
  have cp:=Nat.mul_le_mul ce (show 4*C+7 ≤ 4*D+7 by omega)
  have pos : 9 ≤ D:=by dsimp only [D];omega
  have square : D ≤ D^2:=by simpa only [pow_two] using Nat.le_mul_self D
  have cube : D^2 ≤ D^3:=by
    simpa only [pow_succ,Nat.mul_one] using Nat.mul_le_mul_left (D^2) (show 1 ≤ D by omega)
  have scale : D^2 ≤ (k+1)*D^3:=cube.trans (by nlinarith only [Nat.zero_le k,Nat.zero_le (D^3)])
  have db : d ≤ 64*D^2:=by nlinarith only [dp,cp,ce,ne,fe,pos,square]
  change a+d ≤ 4194304*(k+1)*D^3
  nlinarith only [ab,db,scale,square,Nat.zero_le ((k+1)*D^3)]
/-- ENTIRE capacity-growth driver for W. Every cap is followed by actual
reset/doubling, q98 workspace/bitLength replay, seed and all-k arithmetic.
T is fixed BEFORE the run, including the physically retained source hole. -/
private theorem driver (k N B S L n Q F K C : Nat) (T : Nat → Option Bool) (m : Fin 144)
    (ph : phase m.val=1) (positive : 0 < C) (ck : C ≤ 2*K)
    (ellFits : bitLength n ≤ C) (wk : Cursor.Target.W k n ≤ K)
    (fr : Frame T S L (L+n+1) Q F)
    (reg : ∀ i,S < i → i < L → T i=some false)
    (assn : ∀ i,L < i → i < L+n+1 → T i=some false)
    (fit : F+10*K+n+7 < tapeLength N B) :
    let start : Config (machine k).stateCount N B:=
      ⟨control k (tableControl k 98) m,⟨S,by obtain ⟨sl,_lh,_qp,room,_,_,_,_,_,_,_,_,_⟩:=fr;omega⟩,fun i=>image T F C i.val⟩
    ∃ (t j finalC : Nat) (hd : F+finalC+n+3 < tapeLength N B),
      t ≤ (Cursor.Target.W k n-C+1)*(4194304*(k+1)*(F+10*K+n+9)^3) ∧
      finalC=C*2^j ∧ Cursor.Target.W k n ≤ finalC ∧ finalC ≤ 2*K ∧
      (machine k).run t start=
        ⟨control k (tableControl k (430+93*k)) m,⟨F+finalC+n+3,hd⟩,
          fun i=>residual T L n F finalC 0 (n^k+k) (Cursor.Target.W k n) 0 0 i.val⟩ ∧
      (∀ u,u ≤ t → ((machine k).run u start).head.val ≤ L+16*(F+10*K+n+8)) := by
  intro start
  have copyFr:=fr
  obtain ⟨_sl,_lh,_paid,room,_,_,_,_,_,_,_,_,_⟩:=copyFr
  generalize eq : Cursor.Target.W k n-C=q
  induction q using Nat.strong_induction_on generalizing C with
  | h q ih=>
    have currentFit : F+5*C+n+7 < tapeLength N B:=lt_of_le_of_lt (by omega) fit
    obtain ⟨a,ap,aheads,outcome⟩:=roundWeight k N B S L n Q F C T m ph positive ellFits fr reg assn currentFit
    rcases outcome with ⟨fitsW,hd,done⟩|⟨v2,v3,v4,v5,d0,cap,hd,atCap⟩
    · have cost : a ≤ 4194304*(k+1)*(F+10*K+n+9)^3:=by
        simpa only [Nat.add_zero] using phase_price k n F K C S a 0 ck ap (by omega)
      refine ⟨a,0,C,hd,?_,by simp,fitsW,ck,done,?_⟩
      · have qe : q=0:=by omega
        simpa only [qe,Nat.zero_add,Nat.one_mul] using cost
      · intro u hu
        exact (aheads u hu).trans (by omega)
    · have shortage:=capShortage k n C v2 v3 v4 v5 d0 cap
      have smaller : Cursor.Target.W k n-2*C < q:=by omega
      have nextCapacity : 2*C ≤ 2*K:=by omega
      obtain ⟨d,hs,dp,grown,dheads⟩:=cycle k N B S L n Q F C v2 v3 v4 v5 d0 T m ph positive fr assn currentFit
      obtain ⟨v,j,finalC,hf,vp,formula,large,limit,done,vheads⟩:=
        ih (Cursor.Target.W k n-2*C) smaller (2*C) (by omega) nextCapacity (by omega) rfl
      have combined:=phase_price k n F K C S a d ck ap dp
      refine ⟨a+d+v,j+1,finalC,hf,?_,?_,large,limit,?_,?_⟩
      · have measures : Cursor.Target.W k n-2*C+2 ≤ q+1:=by omega
        calc
          a+d+v ≤ 4194304*(k+1)*(F+10*K+n+9)^3+
              (Cursor.Target.W k n-2*C+1)*(4194304*(k+1)*(F+10*K+n+9)^3):=Nat.add_le_add combined vp
          _ = (Cursor.Target.W k n-2*C+2)*(4194304*(k+1)*(F+10*K+n+9)^3):=by ring
          _ ≤ (q+1)*(4194304*(k+1)*(F+10*K+n+9)^3):=Nat.mul_le_mul_right _ measures
      · rw [formula,Nat.pow_succ];ring
      · rw [UniformTM.run_add,UniformTM.run_add,atCap,grown]
        exact done
      · intro u hu
        by_cases early : u ≤ a
        · exact (aheads u early).trans (by omega)
        · by_cases middle : u ≤ a+d
          · rw [show u=a+(u-a) by omega,UniformTM.run_add,atCap]
            exact (dheads (u-a) (by omega)).trans (by omega)
          · rw [show u=(a+d)+(u-(a+d)) by omega,UniformTM.run_add,UniformTM.run_add,atCap,grown]
            exact vheads (u-(a+d)) (by omega)
#print axioms phase_price
#print axioms driver
end VirtualFinalClosure.WeightGrowthDriver
