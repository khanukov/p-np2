import VirtualFinalClosure.PostRange
import VirtualFinalClosure.WorkspaceReplay
namespace VirtualFinalClosure.PostReplay
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("PostWeight.Kernel","PostWeight","Banks","Banks",(2:Nat)),
      ("PostWeight.Kernel","PostWeight","Banks.mk","banksMk",(3:Nat)),
      ("PostWeight.Length","PostWeight","postLength","postLength",(1:Nat)),
      ("PostWeight.Length","PostWeight","seekStart","seekStart",(1:Nat)),
      ("PostWeight.Kernel","PostWeight","Path.append","joinPath",(1:Nat)),
      ("PostWeight.Kernel","PostWeight","Path.execute","execute",(1:Nat)),
      ("PostWeight.Kernel","PostWeight","atD","atD",(1:Nat)),
      ("PostWeight.Kernel","PostWeight","atBank","atBank",(1:Nat)),
      ("VirtualReady.Kernel","VirtualReady","Node","Node",(2:Nat)),
      ("VirtualReady.Kernel","VirtualReady","Node.mk","node",(3:Nat)),
      ("VirtualReady.Kernel","VirtualReady","Node.state","state",(0:Nat)),
      ("VirtualReady.Kernel","VirtualReady","Node.head","head",(0:Nat)),
      ("VirtualReady.Kernel","VirtualReady","Node.tape","tape",(0:Nat)),
      ("VirtualReady.Kernel","VirtualReady","embed","embed",(0:Nat)),
      ("CarryReadyCompletion.Surface","CarryReadyCompletion","D","D",(0:Nat)),
      ("CarryReadyCompletion.Surface","CarryReadyCompletion","Good","Good",(0:Nat)),
      ("CarryReadyCompletion.Surface","CarryReadyCompletion","Shape","Shape",(0:Nat)),
      ("CarryReadyCompletion.Surface","CarryReadyCompletion","Loc","Loc",(0:Nat)),
      ("CarryReadyCompletion.Native","CarryReadyCompletion","shape_of_banks","shapeOfBanks",(1:Nat)),
      ("VirtualFinalClosure.PostRange","VirtualFinalClosure.PostRange","path_trace","pathTrace",(1:Nat)),
      ("VirtualFinalClosure.PostRange","VirtualFinalClosure.PostRange","good_bounds","goodBounds",(1:Nat)),
      ("VirtualFinalClosure.FullReplay","VirtualFinalClosure.FullReplay","run_lift","runLift",(1:Nat)),
      ("VirtualFinalClosure.ArithmeticReplay","VirtualFinalClosure.ArithmeticReplay","lift","lift",(0:Nat)),
      ("VirtualFinalClosure.WorkspaceReplay","VirtualFinalClosure.WorkspaceReplay","slot_value","slotValue",(1:Nat)),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",(0:Nat)),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",(0:Nat)),
      ("VirtualFinalClosure.Resources","VirtualFinalClosure.Resources","bitLength_le","ellLe",(1:Nat)) ] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | .ctorInfo _=>3 | _=>9
      unless actual=kind do throwError "Wrong literal post-W replay interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique literal post-W replay interface {mod}/{key}"
private theorem q_value (k i : Nat) (hi : i ≤ 798+93*k) : (Cursor.q k i).val=i:=Nat.mod_eq_of_lt (by unfold Cursor.stateCount;omega)
private theorem price (P C n W t : Nat) (tp : t ≤ 2048*(W+1)*(P+1)^2)
    (fit : 5*C+n+7 ≤ P) : t+(3*C+n+8) ≤ 4096*(W+1)*(P+1)^2 := by
  have h : 3*C+n+8 ≤ P+1:=by omega
  have square : P+1 ≤ (P+1)^2:=by simpa only [pow_two] using Nat.le_mul_self (P+1)
  have scale : (P+1)^2 ≤ (W+1)*(P+1)^2:=by nlinarith only [Nat.zero_le W,Nat.zero_le ((P+1)^2)]
  nlinarith only [tp,h,square,scale,Nat.zero_le ((W+1)*(P+1)^2)]
/-- Native q430 -> ACTUAL computed bitLength W at strict local q613, on the
same candidate. Every intermediate whole Config and bank-floor is proved;
phase1's q430 override uses the real Cursor row, not old CarryWindow Ready. -/
private theorem prepared (k N B L n F C g W : Nat) (Z : Nat → Option Bool) (m : Fin 144)
    (ph : phase m.val=1) (room : L+n+1 < F) (wr : W ≤ C)
    (blank : ∀ j,j ≤ 6 → Z (SerializedBody.delimiter F C n j)=none)
    (b0 : ∀ i,F+1 < i → i < F+C+2 → ∃ b,Z i=some b)
    (b1 : ∀ i,F+C+2 < i → i < F+C+n+3 → ∃ b,Z i=some b)
    (fit : F+5*C+n+7 < tapeLength N B) :
    let A:=CappedWeight.Target.image Z L n F C 0 g W 0 0
    let old : Config (Cursor.machine k).stateCount N B:=⟨Cursor.q k (430+93*k),⟨F+C+n+3,by omega⟩,fun i=>A i.val⟩
    let start : Config (machine k).stateCount N B:=⟨control k (tableControl k (430+93*k)) m,⟨F+C+n+3,by omega⟩,fun i=>A i.val⟩
    ∃ t,t ≤ 4096*(W+1)*(F+5*C+n+8)^2 ∧
      (machine k).run t start=⟨control k (tableControl k (613+93*k)) m,⟨F+1,by omega⟩,
        fun i=>CappedWeight.Target.image Z L n F C (bitLength W) 0 0 W 0 i.val⟩ ∧
      (∀ u,u ≤ t → (machine k).run u start=lift k m ((Cursor.machine k).run u old) ∧
        F+1 ≤ ((machine k).run u start).head.val ∧ ((machine k).run u start).head.val ≤ F+5*C+n+7) ∧
      (∀ u,u < t → ∀ flag : Fin 144,((machine k).run u start).state≠control k (tableControl k (613+93*k)) flag) := by
  intro A old start
  let P:=F+5*C+n+7
  have fr : Banks Z L n F C:=banksMk room (by
    intro j hj
    interval_cases j <;> exact blank _ (by omega))
  obtain ⟨t,tp,phasePath⟩:=postLength (k:=k) fr (P:=P) le_rfl g W wr ((ellLe W).trans wr)
  have seek:=seekStart (k:=k) fr (P:=P) le_rfl (bitLength W) W b0 b1
  have joined:=joinPath phasePath seek
  have inputShape : Shape F C n A:=by
    apply shapeOfBanks
    · intro j hj;exact atD fr 0 g W 0 j hj
    · intro j hj i lo hi
      by_cases small : j < 2
      · have equal : A i=Z i:=by
          interval_cases j <;> dsimp only [D] at lo hi <;>
            dsimp only [A,CappedWeight.Target.image] <;>
            rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]
        rw [equal]
        interval_cases j
        · exact b0 i lo hi
        · exact b1 i lo hi
      · exact ⟨_,atBank fr 0 g W 0 j i (by omega) hj lo hi⟩
  have good : Good k F C n (node (Cursor.q k (430+93*k)) (F+C+n+3) A):=
    ⟨430,4,by decide,by decide,rfl,by decide,by decide,by dsimp only [Loc];rfl,inputShape⟩
  have trace:=pathTrace (N:=N) (B:=B) joined good rfl fit
  have ranged : ∀ u,u ≤ t+(3*C+n+8) → 430+93*k ≤ ((Cursor.machine k).run u old).state.val ∧
      ((Cursor.machine k).run u old).state.val ≤ 613+93*k ∧
      F+1 ≤ ((Cursor.machine k).run u old).head.val ∧ ((Cursor.machine k).run u old).head.val ≤ P ∧
      (u < t+(3*C+n+8) → ((Cursor.machine k).run u old).state.val≠613+93*k) := by
    intro u hu
    obtain ⟨v,hv,run,vg,vfirst⟩:=trace (by change F+C+n+3 < tapeLength N B;omega) u hu
    have bounds:=goodBounds vg
    change (Cursor.machine k).run u old=embed v hv at run
    rw [run]
    refine ⟨bounds.1,bounds.2.1,bounds.2.2.1,bounds.2.2.2,?_⟩
    intro early equal
    apply vfirst early
    apply Fin.ext
    exact equal.trans (q_value k (613+93*k) (by omega)).symm
  have simulation:=runLift k m old (t+(3*C+n+8)) ph
    (by intro u hu;have b:=ranged u hu;exact ⟨by omega,by omega⟩)
    (by intro u hu;have b:=ranged u hu.le;exact ⟨by omega,by omega,by omega,b.2.2.2.2 hu⟩)
  have initial : start=lift k m old:=by
    apply Config.ext_parts
    · exact (congrArg (fun i=>control k (tableControl k i) m) (q_value k (430+93*k) (by omega))).symm
    · rfl
    · rfl
  have oldDone:=execute (N:=N) (B:=B) joined fit
  change (Cursor.machine k).run (t+(3*C+n+8)) old=
    ⟨Cursor.q k (613+93*k),⟨F+1,by omega⟩,
      fun i=>CappedWeight.Target.image Z L n F C (bitLength W) 0 0 W 0 i.val⟩ at oldDone
  have done:=simulation (t+(3*C+n+8)) le_rfl
  rw [←initial,oldDone] at done
  refine ⟨t+(3*C+n+8),price P C n W t tp (by dsimp only [P];omega),?_,?_,?_⟩
  · simpa only [lift,q_value k (613+93*k) (by omega)] using done
  · intro u hu
    rw [initial,simulation u hu]
    have b:=ranged u hu
    exact ⟨rfl,b.2.2.1,b.2.2.2.1⟩
  · intro u hu flag equal
    have trace:=simulation u hu.le
    rw [←initial] at trace
    have val : ((machine k).run u start).state.val=144*(375+((Cursor.machine k).run u old).state.val)+m.val:=by
      rw [trace];exact slotValue k ((Cursor.machine k).run u old).state m
    have target:=slotValue k (Cursor.q k (613+93*k)) flag
    rw [q_value k (613+93*k) (by omega)] at target
    have same:=congrArg Fin.val equal
    rw [val,target] at same
    have fm:=m.isLt
    have ff:=flag.isLt
    have no:=(ranged u hu.le).2.2.2.2 hu
    omega
#print axioms q_value
#print axioms price
#print axioms prepared
end VirtualFinalClosure.PostReplay
