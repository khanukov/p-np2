import VirtualFinalClosure.WeightReplay
import VirtualFinalClosure.FullEarly
import VirtualFinalClosure.FullReplay
import VirtualFinalClosure.WorkspaceReplay
import TotalIngressClosure.WeightPhase
namespace VirtualFinalClosure.WeightFirstReplay
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.WeightReplay","VirtualFinalClosure.WeightReplay","range","range",(1:Nat)),
      ("PowerDriver.Kernel","PowerDriver","Frame","PowerFrame",(2:Nat)),
      ("TotalIngressClosure.WeightPhase","TotalIngressClosure","weight_phase","weightPhase",1),
      ("VirtualFinalClosure.WeightRowFloor","VirtualFinalClosure.WeightRowFloor","row_floor","rowFloor",1),
      ("VirtualFinalClosure.ReplayBounds","VirtualFinalClosure.ReplayBounds","reject_stays","rejectStays",1),
      ("VirtualFinalClosure.FullEarly","VirtualFinalClosure.FullEarly","run_lift","runLift",1),
      ("VirtualFinalClosure.ArithmeticReplay","VirtualFinalClosure.ArithmeticReplay","lift","lift",0),
      ("VirtualFinalClosure.WorkspaceReplay","VirtualFinalClosure.WorkspaceReplay","slot_value","slotValue",1),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong actual full-weight replay interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual full-weight replay interface {mod}/{key}"
private theorem q_value (k i : Nat) (hi : i ≤ 798+93*k) : (Cursor.q k i).val=i:=
  Nat.mod_eq_of_lt (by unfold Cursor.stateCount;omega)
/-- ALL k power blocks, +k, +4 and W multiplication on the FROZEN candidate.
The whole original dirty cap residual is kept. This is an executable prepared
body consumed by raw/growth connectors, not an assumed arithmetic-success field. -/
private theorem prepared (k N B L n Q F C : Nat) (Z : Nat → Option Bool) (m : Fin 144)
    (fr : PowerFrame Z L n Q F C) (positive : 0 < C)
    (ellFits : bitLength n ≤ C) (fit : F+5*C+n+7 < tapeLength N B) :
    let old : Config (Cursor.machine k).stateCount N B:=⟨Cursor.q k 329,⟨F+2*C+n+4,by omega⟩,fun j=>Z j.val⟩
    let start : Config (machine k).stateCount N B:=⟨control k (tableControl k 329) m,⟨F+2*C+n+4,by omega⟩,fun j=>Z j.val⟩
    ∃ t,t ≤ 2097152*(k+1)*(n+C+1)^2*(F+5*C+n+9) ∧
      (∀ u,u ≤ t → ((machine k).run u start).head.val ≤ F+5*C+n+7) ∧
      (∀ u,u ≤ t → (machine k).run u start=lift k m ((Cursor.machine k).run u old)) ∧
      (∀ u,u < t → ∀ j,j=430+93*k ∨ j=798+93*k → ∀ flag : Fin 144,
        ((machine k).run u start).state≠control k (tableControl k j) flag) ∧
      ((Cursor.Target.W k n ≤ C ∧ (machine k).run t start=
          ⟨control k (tableControl k (430+93*k)) m,⟨F+C+n+3,by omega⟩,
            fun j=>CappedWeight.Target.image Z L n F C 0 (n^k+k) (Cursor.Target.W k n) 0 0 j.val⟩) ∨
       ∃ v2 v3 v4 v5 d,CappedWeight.Target.Cap k n C v2 v3 v4 v5 d ∧
        (machine k).run t start=
          ⟨control k (tableControl k (798+93*k)) m,⟨F+1,by omega⟩,
            fun j=>CappedWeight.Target.image Z L n F C v2 v3 v4 v5 d j.val⟩) := by
  intro old start
  obtain ⟨t,price,heads,before,outcome⟩:=weightPhase k N B L n Q F C Z fr positive ellFits fit
  have finished : ((Cursor.machine k).run t old).state≠(Cursor.machine k).reject := by
    intro equal
    have bad:=congrArg Fin.val equal
    have rv : (Cursor.machine k).reject.val=40:=q_value k 40 (by omega)
    rw [rv] at bad
    rcases outcome with ⟨_fits,run⟩|⟨v2,v3,v4,v5,d,_cap,run⟩
    · rw [run] at bad
      have val:=q_value k (430+93*k) (by omega)
      change (Cursor.q k (430+93*k)).val=40 at bad
      omega
    · rw [run] at bad
      have val:=q_value k (798+93*k) le_rfl
      change (Cursor.q k (798+93*k)).val=40 at bad
      omega
  have band:=range k N B t old (q_value k 329 (by omega)) finished before
  have simulation:=runLift k m old t
    (by intro u hu;have h:=band u hu;exact ⟨(by decide : 98 ≤ 329).trans h.1,h.2⟩)
    (by
      intro u hu
      have lower:=(band u hu.le).1
      have upper:=before u hu
      change ((Cursor.machine k).run u old).state.val < 430+93*k at upper
      exact ⟨by omega,by omega,by omega,by omega,by omega⟩)
  have initial : start=lift k m old:=by
    apply Config.ext_parts
    · exact (congrArg (fun q=>control k (tableControl k q) m) (q_value k 329 (by omega))).symm
    · rfl
    · rfl
  refine ⟨t,price,?_,?_,?_,?_⟩
  · intro u hu
    rw [initial,simulation u hu]
    exact heads u hu
  · intro u hu
    rw [initial]
    exact simulation u hu
  · intro u hu j which flag equal
    have equality:=simulation u hu.le
    rw [←initial] at equality
    have val : ((machine k).run u start).state.val=144*(375+((Cursor.machine k).run u old).state.val)+m.val := by
      rw [equality];exact slotValue k ((Cursor.machine k).run u old).state m
    have target:=slotValue k (Cursor.q k j) flag
    rw [q_value k j (by rcases which with h|h <;> omega)] at target
    have same:=congrArg Fin.val equal
    rw [val,target] at same
    have fm:=m.isLt
    have ff:=flag.isLt
    have upper:=before u hu
    change ((Cursor.machine k).run u old).state.val < 430+93*k at upper
    rcases which with h|h <;> omega
  · have done:=simulation t le_rfl
    rw [←initial] at done
    rcases outcome with ⟨fits,run⟩|⟨v2,v3,v4,v5,d,cap,run⟩
    · left
      refine ⟨fits,?_⟩
      rw [run] at done
      simpa only [lift,q_value k (430+93*k) (by omega)] using done
    · right
      refine ⟨v2,v3,v4,v5,d,cap,?_⟩
      rw [run] at done
      simpa only [lift,q_value k (798+93*k) le_rfl] using done
#print axioms q_value
#print axioms prepared
end VirtualFinalClosure.WeightFirstReplay
