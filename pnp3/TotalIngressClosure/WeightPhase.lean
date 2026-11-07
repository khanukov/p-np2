import IngressAllocation.ArithmeticPaths
import IngressAllocation.Time
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("PowerDriver.Kernel","PowerDriver","Frame","PowerFrame"),
      ("PowerDriver.Kernel","PowerDriver","driver","powerDriver"),
      ("PowerDriver.Kernel","PowerDriver","Path.execute","powerRun"),
      ("PowerDriver.Kernel","PowerDriver","Path.first","powerFirst"),
      ("FullWeight.Loops","FullWeight","tail","weightTail"),
      ("FullWeight.Kernel","FullWeight","Path.execute","tailRun"),
      ("FullWeight.Kernel","FullWeight","Path.first","tailFirst"),
      ("IngressAllocation.ArithmeticPaths","IngressAllocation.PowerStage","every_head","powerHeads"),
      ("IngressAllocation.ArithmeticPaths","IngressAllocation.WeightStage","every_head","tailHeads"),
      ("IngressAllocation.Time","IngressAllocation","append_heads","appendHeads")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique all-power/all-weight path {mod}/{key}: {found.map Prod.fst}"
private theorem phasePrice (k n r P d v : Nat)
    (hd:d ≤ 1024*(k+1)*(n+r+1)^2*(P+2))
    (hv:v ≤ 1048576*(k+1)*(r+1)^2*(P+2)) :
    d+v ≤ 2097152*(k+1)*(n+r+1)^2*(P+2):=by
  have sq:(r+1)^2 ≤ (n+r+1)^2:=Nat.pow_le_pow_left (by omega) 2
  have vv:v ≤ 1048576*(k+1)*(n+r+1)^2*(P+2):=
    hv.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ sq))
  have dd:d ≤ 1024*((k+1)*(n+r+1)^2*(P+2)):=by simpa only [Nat.mul_assoc] using hd
  have vv':v ≤ 1048576*((k+1)*(n+r+1)^2*(P+2)):=by simpa only [Nat.mul_assoc] using vv
  calc
    d+v ≤ 2097152*((k+1)*(n+r+1)^2*(P+2)):=by omega
    _ = _ := by ring
set_option maxRecDepth 4000 in
private theorem weight_phase (k N B L n Q F r : Nat) (Z : Nat → Option Bool)
    (fr : PowerFrame Z L n Q F r) (rp : 0 < r) (ellFits : bitLength n ≤ r)
    (fit : F+5*r+n+7 < tapeLength N B) :
    let c : Config (Cursor.machine k).stateCount N B:=⟨Cursor.q k 329,⟨F+2*r+n+4,by omega⟩,fun i=>Z i.val⟩
    ∃ t,t ≤ 2097152*(k+1)*(n+r+1)^2*(F+5*r+n+9) ∧
      (∀ u,u ≤ t → ((Cursor.machine k).run u c).head.val ≤ F+5*r+n+7) ∧
      (∀ u,u < t → ((Cursor.machine k).run u c).state.val < 430+93*k) ∧
      ((Cursor.Target.W k n ≤ r ∧ (Cursor.machine k).run t c=
        ⟨Cursor.q k (430+93*k),⟨F+r+n+3,by omega⟩,
          fun i=>CappedWeight.Target.image Z L n F r 0 (n^k+k) (Cursor.Target.W k n) 0 0 i.val⟩) ∨
       ∃ v2 v3 v4 v5 d,CappedWeight.Target.Cap k n r v2 v3 v4 v5 d ∧
        (Cursor.machine k).run t c=⟨Cursor.q k (798+93*k),⟨F+1,by omega⟩,
          fun i=>CappedWeight.Target.image Z L n F r v2 v3 v4 v5 d i.val⟩) := by
  let c : Config (Cursor.machine k).stateCount N B:=⟨Cursor.q k 329,⟨F+2*r+n+4,by omega⟩,fun i=>Z i.val⟩
  obtain ⟨d,powerPrice,branch⟩:=powerDriver (k:=k) Z fr rp
  rcases branch with ⟨powerFits,path⟩|⟨j,a,e,hj,ha,he,eq,path⟩
  all_goals
    have run:=powerRun (N:=N) (B:=B) path fit
    have before:=powerFirst (N:=N) (B:=B) path fit
    have heads:=powerHeads path fit (by change F+2*r+n+4 < tapeLength N B;omega)
  · change (Cursor.machine k).run d c=
      ⟨Cursor.q k (329+82*k),⟨F+2*r+n+4,by omega⟩,
        fun i=>CappedWeight.Target.image Z L n F r (bitLength n) (n^k) 0 0 0 i.val⟩ at run
    obtain ⟨v,tailPrice,tailBranch⟩:=weightTail (k:=k) Z fr (bitLength n) (n^k) ellFits powerFits
    rcases tailBranch with ⟨final,tailPath⟩|⟨v2,v3,v4,v5,cap,tailPath⟩
    all_goals
      have finished:=tailRun (N:=N) (B:=B) tailPath fit
      have lastHeads:=tailHeads tailPath fit (by change F+2*r+n+4 < tapeLength N B;omega)
      have lastBefore:=tailFirst (N:=N) (B:=B) tailPath fit
      have bounded : ∀ u,u ≤ d+v → ((Cursor.machine k).run u c).head.val ≤ F+5*r+n+7:=by
        apply appendHeads (Cursor.machine k) c heads
        intro u hu
        rw [run]
        exact lastHeads u hu
      have guarded : ∀ u,u < d+v → ((Cursor.machine k).run u c).state.val < 430+93*k:=by
        intro u hu
        by_cases early : u < d
        · exact (before u early).trans_le (by omega)
        · rw [show u=d+(u-d) by omega,UniformTM.run_add,run]
          exact lastBefore (u-d) (by omega)
    · refine ⟨d+v,phasePrice k n r (F+5*r+n+7) d v powerPrice tailPrice,bounded,guarded,Or.inl ⟨final,?_⟩⟩
      rw [UniformTM.run_add,run]
      exact finished
    · have fullCap : CappedWeight.Target.Cap k n r v2 v3 v4 v5 0:=by
        refine Or.inr ?_
        rcases cap with ⟨j,hj,eq,h2,h3,h4,h5⟩|⟨j,hj,eq,h2,h3,h4,h5⟩|⟨a,e,ha,he,eq,h2,h3,h4,h5⟩
        · exact Or.inl ⟨j,hj,eq,h2,h3,h4,h5,rfl⟩
        · exact Or.inr (Or.inl ⟨j,hj,eq,h2,h3,h4,h5,rfl⟩)
        · exact Or.inr (Or.inr ⟨a,e,ha,he,eq,h2,h3,h4,h5,rfl⟩)
      refine ⟨d+v,phasePrice k n r (F+5*r+n+7) d v powerPrice tailPrice,bounded,guarded,Or.inr ⟨v2,v3,v4,v5,0,fullCap,?_⟩⟩
      rw [UniformTM.run_add,run]
      exact finished
  · refine ⟨d,powerPrice.trans (by nlinarith only [Nat.zero_le ((k+1)*(n+r+1)^2*(F+5*r+n+9))]),heads,(fun u hu=>(before u hu).trans_le (by omega)),Or.inr
      ⟨bitLength n,n^j-a-1,r,0,e+1,Or.inl ⟨j,a,e,hj,ha,he,eq,rfl,rfl,rfl,rfl,rfl⟩,?_⟩⟩
    exact run
end TotalIngressClosure
