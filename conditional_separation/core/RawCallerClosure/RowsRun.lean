import RawCallerClosure.Frame
import RawCallerClosure.Work
namespace RawCallerClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
run_cmd do
  let e←getEnv
  for (owner,ns,leaf,aliasName,kind) in [
    (`PhysicalCallerClosure.AllRows,`PhysicalCallerClosure,"Layout","Layout","inductive"),
    (`RawCallerClosure.Rows,`RawCallerClosure,"caller_run","callerRun","theorem"),
    (`RawCallerClosure.Work,`RawCallerClosure,"caller_injective","callerInjective","theorem"),
    (`RawCallerClosure.Work,`RawCallerClosure,"caller_accept","callerAccept","theorem"),
    (`RawCallerClosure.Work,`RawCallerClosure,"caller_reject","callerReject","theorem")] do
    let found:=e.constants.toList.filter fun (n,_)=>n.toString.startsWith ("_private."++owner.toString++".") && n.toString.endsWith ("."++ns.toString++"."++leaf)
    let [(n,ci)]:=found | throwError "Nonunique whole caller application"
    let actual:=match ci with|.thmInfo _=>"theorem"|.inductInfo _=>"inductive"|_=>"other"
    unless actual==kind do throwError "Wrong caller application kind"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong caller application owner"
    logInfo m!"ordinary-caller-application|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
private theorem rows_run (k B R S z n r g W M A Q : Nat) (source : Fin S → Bool) (T : Nat → Option Bool)
    (layout:Layout B R S z n r g W M A Q source T)
    (hH:S+z+2+n+1 < tapeLength R B)
    (c : Config (machine k).stateCount R B) (pre : Nat)
    (handoff:(machine k).run pre c=callerConfig k
      ⟨PhysicalCallerClosure.oldState k (BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode source M))),
        ⟨S+z+2+n+1,hH⟩,fun i=>SerializedBody.prepared T S M (FixedRawLengthFence.fencePos R) r n g W i.val⟩)
    (safe:∀ u,u≤pre → ((machine k).run u c).state≠(machine k).accept)
    (first:∀ u,u<pre → ((machine k).run u c).state≠(machine k).reject ∧
      ((machine k).run u c).state≠callerState k (PhysicalCallerClosure.rowsDone k)) :
    ∃ elapsed,elapsed≤1099511627776*(R+1)^8 ∧
      Target.RowsResult k B R S z n r g W M A Q source T hH c (pre+elapsed) := by
  rcases layout with ⟨rp,rs,sr,gf,wp,wf,ef,af,ap,asrc,margin,qp,arena,hole,marker,src,eof,reg,left,right,beta,marks,gap,fence,metadata,fit,_room⟩
  have hEq:S+z+2+n+1=S+z+n+3:=by omega
  have arena':S+z+2+n+1+Q<FixedRawLengthFence.fencePos R:=by omega
  have beta':∀ j:Fin n,T (S+z+2+n+1-1-j.val)=some false:=by
    intro j
    simpa only [show S+z+2+n+1-1-j.val=S+z+n+2-j.val by omega] using beta j
  obtain ⟨elapsed,price,localSafe,localFirst,outcome⟩:=PhysicalCallerClosure.caller_rows k B R S z n r g W M A Q source T
    rp rs sr gf wp wf ef af ap asrc margin qp arena' hole marker src eof reg left (by simpa only [hEq] using right)
    beta' (by simpa only [hEq] using marks) (by simpa only [hEq] using gap) fence metadata fit hH
  let start : Config (PhysicalCallerClosure.callerMachine k).stateCount R B:=
    ⟨PhysicalCallerClosure.oldState k (BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode source M))),
      ⟨S+z+2+n+1,hH⟩,fun i=>SerializedBody.prepared T S M (FixedRawLengthFence.fencePos R) r n g W i.val⟩
  have after (u : Nat) : (machine k).run (pre+u) c=callerConfig k ((PhysicalCallerClosure.callerMachine k).run u start):=by
    rw [UniformTM.run_add,handoff,callerRun]
  refine ⟨elapsed,price,?_⟩
  dsimp only [Target.RowsResult]
  refine ⟨?_,?_,?_⟩
  · intro u hu
    by_cases earlier:u≤pre
    · exact safe u earlier
    · have eq:u=pre+(u-pre):=by omega
      rw [eq,after]
      intro bad
      change callerState k _=(machine k).accept at bad
      exact localSafe (u-pre) (by omega) (callerInjective k (bad.trans (callerAccept k).symm))
  · intro u hu
    by_cases earlier:u<pre
    · exact first u earlier
    · have eq:u=pre+(u-pre):=by omega
      rw [eq,after]
      constructor
      · intro bad
        change callerState k _=(machine k).reject at bad
        exact (localFirst (u-pre) (by omega)).1 (callerInjective k (bad.trans (callerReject k).symm))
      · intro bad
        change callerState k _=callerState k _ at bad
        exact (localFirst (u-pre) (by omega)).2 (callerInjective k bad)
  · cases decoded:decodeCircuitFull n (bitLength n) (SerializedBody.window source M W) with
    | none=>
      simp only [decoded] at outcome ⊢
      rw [after,outcome]
      rfl
    | some pair=>
      rcases pair with ⟨circuit,tail⟩
      simp only [decoded] at outcome ⊢
      rcases outcome with ⟨large,eq⟩|⟨cap,usedBound,tailEq,paid,finish⟩
      · left
        refine ⟨large,?_⟩
        rw [after,eq]
        rfl
      · right
        refine ⟨cap,usedBound,tailEq,?_,?_⟩
        · obtain ⟨starts,entries,ordered⟩:=paid
          refine ⟨fun i=>pre+starts i,?_,?_⟩
          · intro i hi
            obtain ⟨bound,entry⟩:=entries i hi
            refine ⟨Nat.add_lt_add_left bound pre,?_⟩
            rw [after,entry]
            rfl
          · intro i j ij good
            exact Nat.add_lt_add_left (ordered i j ij good) pre
        · rcases finish with ⟨room,good,eq⟩|⟨row,bound,good,bad,eq⟩|⟨short,good,eq⟩
          · left
            refine ⟨room,good,?_⟩
            rw [after,eq]
            rfl
          · right;left
            refine ⟨row,bound,good,bad,?_⟩
            rw [after,eq]
            rfl
          · right;right
            refine ⟨short,good,?_⟩
            rw [after,eq]
            rfl
private theorem rows_terminal (k B R S z n r g W M A Q : Nat) (source : Fin S → Bool) (T : Nat → Option Bool)
    (hH:S+z+2+n+1 < tapeLength R B) (c : Config (machine k).stateCount R B) (t : Nat)
    (rows:Target.RowsResult k B R S z n r g W M A Q source T hH c t) :
    ((machine k).run t c).state=(machine k).reject ∨
    ((machine k).run t c).state=callerState k (PhysicalCallerClosure.rowsDone k) := by
  rcases rows with ⟨_safe,_first,outcome⟩
  cases decoded:decodeCircuitFull n (bitLength n) (SerializedBody.window source M W) with
  | none=>
    simp only [decoded] at outcome
    exact Or.inl (congrArg Config.state outcome)
  | some pair=>
    rcases pair with ⟨circuit,tail⟩
    simp only [decoded] at outcome
    rcases outcome with ⟨_large,eq⟩|⟨_cap,_used,_tail,_starts,finish⟩
    · exact Or.inl (congrArg Config.state eq)
    · rcases finish with ⟨_room,_good,eq⟩|⟨_row,_bound,_good,_bad,eq⟩|⟨_short,_good,eq⟩
      · exact Or.inr (congrArg Config.state eq)
      · exact Or.inl (congrArg Config.state eq)
      · exact Or.inl (congrArg Config.state eq)
end RawCallerClosure
