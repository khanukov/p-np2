import VirtualFinalClosure.CapacityCycle
import VirtualFinalClosure.Recompute
namespace VirtualFinalClosure.LengthGrowthDriver
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
      ("VirtualFinalClosure.Recompute","VirtualFinalClosure.Recompute","prepared","recompute",1),
      ("VirtualFinalClosure.CapacityCycle","VirtualFinalClosure.CapacityCycle","cycle","cycle",1),
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
private theorem phase_price (n F K C S a d : Nat) (ck : C ≤ 2*K)
    (ap : a ≤ 4096*(n+C+1)*(F+5*C+n+9))
    (dp : d ≤ n+C+6+(C*(4*C+7)+2*n+14*C+27)+(F-S+3)+1) :
    a+d ≤ 8192*(F+10*K+n+9)^2 := by
  let D:=F+10*K+n+9
  have ce : C ≤ D:=by dsimp only [D];omega
  have ne : n ≤ D:=by dsimp only [D];omega
  have fe : F-S ≤ D:=by dsimp only [D];omega
  have aa : n+C+1 ≤ D:=by dsimp only [D];omega
  have ee : F+5*C+n+9 ≤ D:=by dsimp only [D];omega
  have prod:=Nat.mul_le_mul (Nat.mul_le_mul_left 4096 aa) ee
  have cp:=Nat.mul_le_mul ce (show 4*C+7 ≤ 4*D+7 by omega)
  have pos : 9 ≤ D:=by dsimp only [D];omega
  have ab : a ≤ 4096*D^2 := calc
    a ≤ 4096*(n+C+1)*(F+5*C+n+9):=ap
    _ ≤ 4096*D*D:=prod
    _ = _:=by ring
  have square : D ≤ D^2:=by simpa only [pow_two] using Nat.le_mul_self D
  have db : d ≤ 64*D^2 := by nlinarith only [dp,cp,ce,ne,fe,pos,square]
  change a+d ≤ 8192*D^2
  nlinarith only [ab,db,Nat.zero_le (D^2)]
/-- ALL physical doubling iterations required for bitLength n, on the SAME
fixed candidate; n0 is included. The original base tape T is fixed before the
run, and the final tape is an explicit function of T and the executed capacity.
This is a body reused by the raw connector, not the full virtual FINAL theorem. -/
private theorem driver (k N B S L n Q F K C : Nat) (T : Nat → Option Bool) (m : Fin 144)
    (ph : phase m.val=1) (positive : 0 < C) (ck : C ≤ 2*K) (lk : bitLength n ≤ K)
    (fr : Frame T S L (L+n+1) Q F)
    (reg : ∀ i,S < i → i < L → T i=some false)
    (assn : ∀ i,L < i → i < L+n+1 → T i=some false)
    (fit : F+10*K+n+7 < tapeLength N B) :
    let start : Config (machine k).stateCount N B:=
      ⟨control k (tableControl k 98) m,⟨S,by obtain ⟨sl,_lh,_qp,room,_,_,_,_,_,_,_,_,_⟩:=fr;omega⟩,fun j=>image T F C j.val⟩
    ∃ (t j finalC : Nat) (hl : L < tapeLength N B),
      t ≤ (bitLength n-C+1)*(8192*(F+10*K+n+9)^2) ∧
      finalC=C*2^j ∧ bitLength n ≤ finalC ∧ finalC ≤ 2*K ∧
      (machine k).run t start=
        ⟨control k (tableControl k 308) m,⟨L,hl⟩,
          fun i=>RuntimeBitLength.Target.fullImage
            (CappedWorkspace.Target.image (image T F finalC) L n F finalC) L n F finalC i.val⟩ ∧
      (∀ u,u ≤ t → ((machine k).run u start).head.val ≤ F+10*K+n+7) := by
  intro start
  have frCopy:=fr
  obtain ⟨sl,_lh,qp,room,_s0,_l0,_h0,_d0,_ff,_rg,_as,_paid,_gap⟩:=frCopy
  have below : L+n+1 < F:=by omega
  generalize eq : bitLength n-C=q
  induction q using Nat.strong_induction_on generalizing C with
  | h q ih=>
    let G:=image T F C
    let c : Config (machine k).stateCount N B:=
      ⟨control k (tableControl k 98) m,⟨S,by omega⟩,fun j=>G j.val⟩
    have sameStart : start=c:=rfl
    have currentFit : F+5*C+n+7 < tapeLength N B:=lt_of_le_of_lt (by omega) fit
    have fg:=imageFrame T S L n Q F C fr
    have rg : ∀ i,S < i → i < L → G i=some false := by
      intro i lo hi
      exact (imageLow T F C i (by omega)).trans (reg i lo hi)
    have ag : ∀ i,L < i → i < L+n+1 → G i=some false := by
      intro i lo hi
      exact (imageLow T F C i (by omega)).trans (assn i lo hi)
    obtain ⟨a,hf,ap,arrived,aheads,_first,_configs⟩:=recompute k N B S L n Q F C G m positive fg rg ag
      (imageDigits T F C) (by intro i lo _hi;exact imageTail T F C i lo) currentFit
    by_cases fits : bitLength n ≤ C
    · have cost : a ≤ 8192*(F+10*K+n+9)^2:=by
        have total:=phase_price n F K C S a 0 ck ap (by omega)
        simpa only [Nat.add_zero] using total
      have actual : (machine k).run a c=
          ⟨control k (tableControl k 308) m,⟨L,by simpa only [if_pos fits] using hf⟩,
            fun i=>RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (image T F C) L n F C) L n F C i.val⟩:=by
        simpa only [if_pos fits] using arrived
      refine ⟨a,0,C,by omega,?_,by simp,fits,ck,?_,?_⟩
      · have qe : q=0:=by omega
        simpa only [qe,Nat.zero_add,Nat.one_mul] using cost
      · rw [sameStart]
        exact actual
      · intro u hu
        rw [sameStart]
        exact (aheads u hu).trans (by omega)
    · have smaller : bitLength n-2*C < q:=by omega
      have nextCapacity : 2*C ≤ 2*K:=by omega
      let Y:=RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image G L n F C) L n F C
      let ci:=if (C+1)%2=1 then 250 else 304
      have which : ci=250 ∨ ci=304:=by dsimp only [ci];split_ifs <;> simp
      have atCap : (machine k).run a c=
          ⟨control k (tableControl k ci) m,⟨F+C+n+3,by simpa only [if_neg fits] using hf⟩,fun i=>Y i.val⟩:=by
        simpa only [if_neg fits] using arrived
      obtain ⟨d,hs,dp,grown,dheads⟩:=cycle k N B S L n Q F C ci T m ph which positive fr assn currentFit
      obtain ⟨v,j,finalC,hl,vp,formula,large,limit,done,vheads⟩:=
        ih (bitLength n-2*C) smaller (2*C) (by omega) nextCapacity rfl
      have combined := phase_price n F K C S a d ck ap dp
      refine ⟨a+d+v,j+1,finalC,hl,?_,?_,large,limit,?_,?_⟩
      · have measures : bitLength n-2*C+2 ≤ q+1:=by omega
        calc
          a+d+v ≤ 8192*(F+10*K+n+9)^2+(bitLength n-2*C+1)*(8192*(F+10*K+n+9)^2):=Nat.add_le_add combined vp
          _ = (bitLength n-2*C+2)*(8192*(F+10*K+n+9)^2):=by ring
          _ ≤ (q+1)*(8192*(F+10*K+n+9)^2):=Nat.mul_le_mul_right _ measures
      · rw [formula,Nat.pow_succ]
        ring
      · rw [sameStart,UniformTM.run_add,UniformTM.run_add,atCap,grown]
        exact done
      · intro u hu
        rw [sameStart]
        by_cases early : u ≤ a
        · exact (aheads u early).trans (by omega)
        · by_cases middle : u ≤ a+d
          · rw [show u=a+(u-a) by omega,UniformTM.run_add,atCap]
            exact (dheads (u-a) (by omega)).trans (by omega)
          · rw [show u=(a+d)+(u-(a+d)) by omega,UniformTM.run_add,UniformTM.run_add,atCap,grown]
            exact vheads (u-(a+d)) (by omega)
#print axioms phase_price
#print axioms driver
end VirtualFinalClosure.LengthGrowthDriver
