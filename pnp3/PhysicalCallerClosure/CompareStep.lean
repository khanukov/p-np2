import PhysicalCallerClosure.Compare
import PhysicalCallerClosure.Callbacks
import PhysicalCallerClosure.Reset
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
private def select (owner : Name) (leaf kind : String) : TacticM Unit := do
  let e←getEnv
  let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure")
  let some ci:=e.find? n | throwError "Missing exact comparison interface {n}"
  let actual:=match ci with | .defnInfo _=>"definition" | .thmInfo _=>"theorem" | .ctorInfo _=>"constructor" | _=>"other"
  unless actual==kind do throwError "Wrong comparison term kind"
  let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
  unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
  unless e.header.moduleNames[i]! == owner do throwError "Wrong comparison owner"
  logInfo m!"comparison-adapter|{n}|{ci.type}"
  closeMainGoal `select (mkConst n (ci.levelParams.map Level.param))
run_cmd do
  let e←getEnv
  for (owner,leaves) in [(`PhysicalCallerClosure.Engine,["Node","Path","Grid","ns","NativeSafe","ns_safe","embed"]),
      (`PhysicalCallerClosure.Compare,["flags","command","callbackEntry","rejectEntry","payEntry","comparison_path"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing comparison support {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong comparison support owner"
      logInfo m!"comparison-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac select `PhysicalCallerClosure.Engine "Node.mk" "constructor"
private abbrev callback : ∀ k,Fin 7500 → Fin (callerMachine k).stateCount := by
  run_tac select `PhysicalCallerClosure.Callbacks "callback" "definition"
private theorem callback_step : ∀ (k N B : Nat) (q : Fin 7500) (h : Fin (tapeLength N B))
    (T : Fin (tapeLength N B) → Option Bool),0 < q.val → q.val < 4 →
    (callerMachine k).run 1 ⟨evalState k q,h,T⟩=⟨callback k q,h,T⟩ := by
  run_tac select `PhysicalCallerClosure.Callbacks "callback_step" "theorem"
private theorem safe_verdict : ∀ k q,NativeSafe k q →
    q≠(callerMachine k).accept ∧ q≠(callerMachine k).reject ∧ q≠rowsDone k := by
  run_tac select `PhysicalCallerClosure.Reset "safe_verdict" "theorem"
private def terminal (result : Fin 3) : Fin 7500 :=
  if result.val=2 then SerializedBody.machine.reject else SerializedBody.done (decide (result.val=1))
private theorem enter (k : Nat) (result : Fin 3) (N B : Nat) (h : Fin (tapeLength N B))
    (T : Fin (tapeLength N B) → Option Bool) :
    (callerMachine k).run 1 ⟨evalState k (terminal result),h,T⟩=⟨callbackEntry k result,h,T⟩ := by
  fin_cases result
  · exact callback_step k N B (SerializedBody.done false) h T (by decide) (by decide)
  · exact callback_step k N B (SerializedBody.done true) h T (by decide) (by decide)
  · exact callback_step k N B SerializedBody.machine.reject h T (by decide) (by decide)
private theorem eval_safe (k : Nat) (q : Fin 7500) :
    evalState k q≠(callerMachine k).accept ∧ evalState k q≠(callerMachine k).reject ∧ evalState k q≠rowsDone k := by
  refine ⟨?_,?_,?_⟩
  · intro bad;have values:=congrArg Fin.val bad
    change (BodyIngress.machine k).stateCount+q.val=(BodyIngress.machine k).accept.val at values
    have bound:=(BodyIngress.machine k).accept.isLt;omega
  · intro bad;have values:=congrArg Fin.val bad
    change (BodyIngress.machine k).stateCount+q.val=(BodyIngress.machine k).reject.val at values
    have bound:=(BodyIngress.machine k).reject.isLt;omega
  · intro bad;have values:=congrArg Fin.val bad
    change (BodyIngress.machine k).stateCount+q.val=(BodyIngress.machine k).stateCount+7500+1432 at values
    have bound:=q.isLt;omega
private theorem reject_safe (k : Nat) (a t : Fin 3) : NativeSafe k (rejectEntry k a t) := by
  fin_cases a <;> fin_cases t <;> exact ns_safe k _ (by decide) (by decide)
private theorem pay_safe (k : Nat) (a t : Fin 3) : NativeSafe k (payEntry k a t) := by
  fin_cases a <;> fin_cases t <;> exact ns_safe k _ (by decide) (by decide)
private theorem command_safe (k : Nat) (result a t : Fin 3) (last : Bool) : NativeSafe k (command k result a t last) := by
  unfold command
  split_ifs <;> first | exact reject_safe k a t | exact pay_safe k a t
private theorem compare_run (k : Nat) (result a t : Fin 3) (last : Bool)
    (N B H Q F P : Nat) (D : Nat → Nat) (T : Nat → Option Bool) (grid:Grid D T)
    (anchor:D 0=F+1) (metaWidth:D 13=D 12+6) (room:D 13 ≤ P) (fit:P < tapeLength N B)
    (positive:0 < Q) (arena:H+Q < F) (th:T H=none) (tf:T F=some false)
    (marks:∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap:∀ i,H+Q < i → i < F → T i=none)
    (metadata:∀ j:Fin 5,T (D 12+1+j.val)=some (flags a t last j)) (hH:H < tapeLength N B) :
    let c : Config (callerMachine k).stateCount N B:=⟨evalState k (terminal result),⟨H,hH⟩,fun i=>T i.val⟩
    (callerMachine k).run (2*(D 12-H)+39) c=⟨command k result a t last,⟨H,hH⟩,fun i=>T i.val⟩ ∧
    (∀ u,u ≤ 2*(D 12-H)+39 → ((callerMachine k).run u c).state≠(callerMachine k).accept ∧
      ((callerMachine k).run u c).state≠(callerMachine k).reject ∧ ((callerMachine k).run u c).state≠rowsDone k) ∧
    (∀ u,u ≤ 2*(D 12-H)+39 → ((callerMachine k).run u c).head.val ≤ P ∧
      ∀ i:Fin (tapeLength N B),P < i.val → ((callerMachine k).run u c).tape i=T i.val) := by
  dsimp only
  let c : Config (callerMachine k).stateCount N B:=⟨evalState k (terminal result),⟨H,hH⟩,fun i=>T i.val⟩
  have one:=enter k result N B ⟨H,hH⟩ (fun i=>T i.val)
  have path:=comparison_path k result a t last D T H Q F P grid anchor metaWidth room positive arena th tf marks gap metadata
  have runMeta:(callerMachine k).run (2*(D 12-H)+38) ⟨callbackEntry k result,⟨H,hH⟩,fun i=>T i.val⟩=
      ⟨command k result a t last,⟨H,hH⟩,fun i=>T i.val⟩:=by simpa only [embed] using path.execute fit
  have endEq:(callerMachine k).run (2*(D 12-H)+39) c=⟨command k result a t last,⟨H,hH⟩,fun i=>T i.val⟩:=by
    rw [show 2*(D 12-H)+39=1+(2*(D 12-H)+38) by omega,UniformTM.run_add,one,runMeta]
  refine ⟨endEq,?_,?_⟩
  · intro u hu
    by_cases zero:u=0
    · subst u;exact eval_safe k (terminal result)
    · have transport:(callerMachine k).run u c=(callerMachine k).run (u-1)
          ⟨callbackEntry k result,⟨H,hH⟩,fun i=>T i.val⟩:=by
        rw [show u=1+(u-1) by omega,UniformTM.run_add,one]
        rw [show 1+(u-1)-1=u-1 by omega]
      by_cases early:u-1 < 2*(D 12-H)+38
      · rw [transport]
        have safe:=path.safe_prefix fit (u-1) early
        exact safe_verdict k _ safe
      · have eq:u=2*(D 12-H)+39:=by omega
        rw [eq,endEq]
        exact safe_verdict k _ (command_safe k result a t last)
  · intro u hu
    by_cases zero:u=0
    · subst u;exact ⟨path.bounds.1,by intro i _;rfl⟩
    · rw [show u=1+(u-1) by omega,UniformTM.run_add,one]
      simpa only [embed] using path.footprint fit (u-1) (by omega)
end PhysicalCallerClosure
