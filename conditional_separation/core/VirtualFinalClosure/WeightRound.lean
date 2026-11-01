import VirtualFinalClosure.ComputeWeight
import VirtualFinalClosure.WeightCapFrame
import VirtualFinalClosure.Recompute
namespace VirtualFinalClosure.WeightRound
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
      ("VirtualFinalClosure.ComputeWeight","VirtualFinalClosure.ComputeWeight","prepared","computeWeight",1),
      ("VirtualFinalClosure.WeightCapFrame","VirtualFinalClosure.WeightCapFrame","residual","residual",0),
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
/-- A complete literal workspace/bitLength/seed/all-k-W round. The actual
completed n-length proof discharges ellFits; no arithmetic success is assumed. -/
private theorem round (k N B S L n Q F C : Nat) (T : Nat → Option Bool) (m : Fin 144)
    (ph : phase m.val=1) (positive : 0 < C) (fits : bitLength n ≤ C)
    (fr : Frame T S L (L+n+1) Q F)
    (reg : ∀ i,S < i → i < L → T i=some false)
    (assn : ∀ i,L < i → i < L+n+1 → T i=some false)
    (fit : F+5*C+n+7 < tapeLength N B) :
    let start : Config (machine k).stateCount N B:=
      ⟨control k (tableControl k 98) m,⟨S,by obtain ⟨sl,_lh,_qp,room,_,_,_,_,_,_,_,_,_⟩:=fr;omega⟩,fun i=>image T F C i.val⟩
    ∃ t,t ≤ 4096*(n+C+1)*(F+5*C+n+9)+16*(F+5*C+n+8)+2097152*(k+1)*(n+C+1)^2*(F+5*C+n+9) ∧
      (∀ u,u ≤ t → ((machine k).run u start).head.val ≤ L+16*(F+5*C+n+8)) ∧
      ((Cursor.Target.W k n ≤ C ∧ ∃ hd : F+C+n+3 < tapeLength N B,
        (machine k).run t start=⟨control k (tableControl k (430+93*k)) m,⟨F+C+n+3,hd⟩,
          fun i=>residual T L n F C 0 (n^k+k) (Cursor.Target.W k n) 0 0 i.val⟩) ∨
       ∃ v2 v3 v4 v5 d,CappedWeight.Target.Cap k n C v2 v3 v4 v5 d ∧
        ∃ hd : F+1 < tapeLength N B,
        (machine k).run t start=⟨control k (tableControl k (798+93*k)) m,⟨F+1,hd⟩,
          fun i=>residual T L n F C v2 v3 v4 v5 d i.val⟩) := by
  intro start
  have copyFr:=fr
  obtain ⟨_sl,_lh,_paid,room,_,_,_,_,_,_,_,_,_⟩:=copyFr
  let G:=image T F C
  have fg:=imageFrame T S L n Q F C fr
  have rg : ∀ i,S < i → i < L → G i=some false:=by
    intro i lo hi;exact (imageLow T F C i (by omega)).trans (reg i lo hi)
  have ag : ∀ i,L < i → i < L+n+1 → G i=some false:=by
    intro i lo hi;exact (imageLow T F C i (by omega)).trans (assn i lo hi)
  obtain ⟨a,hf,ap,arrived,aheads,_first,_configs⟩:=recompute k N B S L n Q F C G m positive fg rg ag
    (imageDigits T F C) (by intro i lo _hi;exact imageTail T F C i lo) fit
  have atLength : (machine k).run a start=
      ⟨control k (tableControl k 308) m,⟨L,by simpa only [if_pos fits] using hf⟩,
        fun i=>RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image G L n F C) L n F C i.val⟩:=by
    simpa only [if_pos fits] using arrived
  obtain ⟨a0,b0,ap0,bp0,_seedTrace,_weightTrace,heads,_firstW,outcome⟩:=
    computeWeight k N B S L n Q F C T m ph fr positive fits fit
  refine ⟨a+a0+b0,by omega,?_,?_⟩
  · intro u hu
    by_cases early : u ≤ a
    · exact (aheads u early).trans (by omega)
    · rw [show u=a+(u-a) by omega,UniformTM.run_add,atLength]
      exact heads (u-a) (by omega)
  · have done : (machine k).run (a+a0+b0) start=(machine k).run (a0+b0) ((machine k).run a start):=by
      rw [←UniformTM.run_add];congr 1;omega
    rw [done,atLength]
    rcases outcome with ⟨fitsW,run⟩|⟨v2,v3,v4,v5,d,cap,run⟩
    · exact Or.inl ⟨fitsW,by omega,run⟩
    · exact Or.inr ⟨v2,v3,v4,v5,d,cap,by omega,run⟩
#print axioms round
end VirtualFinalClosure.WeightRound
