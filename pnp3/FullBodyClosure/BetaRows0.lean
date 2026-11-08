import FullBodyClosure.Beta
namespace FullBodyClosure
open Pnp3.Complexity.Uniform.V1
open Lean Elab Tactic in
private def checkedFrom (owner : Name) (userNS leaf : String) : TacticM Unit := do
  let env ← getEnv
  let root:=Name.str (Name.num (Name.append `_private owner) 0) userNS
  let name:=(leaf.splitOn ".").foldl Name.str root
  let some ci:=env.find? name | throwError "Missing exact immutable declaration: {name}"
  let some mi:=env.getModuleIdxFor? name | throwError "Missing immutable module: {name}"
  unless mi.toNat < env.header.moduleNames.size do throwError "Owner index outside header"
  unless env.header.moduleNames[mi]! == owner do throwError "Wrong owner for {name}"
  logInfo m!"row-adapter|{owner}|{name}|{ci.type}"
  closeMainGoal `checkedFrom (mkConst name (ci.levelParams.map Level.param))
private abbrev RouteR : Nat → Nat → Fin 7500 → Fin 7500 → Prop := by run_tac checkedFrom `SerializedBodyCompletion.Kernel "SerializedBodyCompletion" "RouteR"
private abbrev RouteL : Nat → Nat → Fin 7500 → Fin 7500 → Prop := by run_tac checkedFrom `SerializedBodyCompletion.Kernel "SerializedBodyCompletion" "RouteL"
private abbrev ClearRows : Nat → Bool → Fin 7500 → Fin 7500 → Prop := by run_tac checkedFrom `SerializedBodyCompletion.Kernel "SerializedBodyCompletion" "ClearRows"
private abbrev ClearPlan : List (Nat × Bool) → Fin 7500 → Fin 7500 → Prop := by run_tac checkedFrom `SerializedBodyCompletion.Kernel "SerializedBodyCompletion" "ClearPlan"
private abbrev ToHRows : Fin 7500 → Fin 7500 → Prop := by run_tac checkedFrom `SerializedBodyCompletion.Kernel "SerializedBodyCompletion" "ToHRows"
private abbrev RestoreRows : Bool → Fin 7500 → Fin 7500 → Prop := by run_tac checkedFrom `SerializedBodyCompletion.Kernel "SerializedBodyCompletion" "RestoreRows"
private theorem rnil : ∀ i q,RouteR i i q q := by run_tac checkedFrom `SerializedBodyCompletion.Kernel "SerializedBodyCompletion" "RouteR.nil"
private theorem lnil : ∀ i q,RouteL i i q q := by run_tac checkedFrom `SerializedBodyCompletion.Kernel "SerializedBodyCompletion" "RouteL.nil"
private theorem rnext : ∀ {i j e s q x}, 4 ≤ e.val → 4 ≤ s.val →
    SerializedBody.machine.step e none=(s,none,.right) →
    (∀ b,SerializedBody.machine.step s (some b)=(s,some b,.right)) →
    SerializedBody.machine.step s none=(q,none,.stay) → RouteR (i+1) j q x → RouteR i j e x := by run_tac checkedFrom `SerializedBodyCompletion.Kernel "SerializedBodyCompletion" "RouteR.next"
private theorem lnext : ∀ {i j e s q x}, 4 ≤ e.val → 4 ≤ s.val →
    SerializedBody.machine.step e none=(s,none,.left) →
    (∀ b,SerializedBody.machine.step s (some b)=(s,some b,.left)) →
    SerializedBody.machine.step s none=(q,none,.stay) → RouteL i j q x → RouteL (i+1) j e x := by run_tac checkedFrom `SerializedBodyCompletion.Kernel "SerializedBodyCompletion" "RouteL.next"
private theorem plan_nil : ∀ q,ClearPlan [] q q := by run_tac checkedFrom `SerializedBodyCompletion.Kernel "SerializedBodyCompletion" "ClearPlan.nil"
private theorem plan_cons : ∀ {j b xs q mid out}, j < 12 → ClearRows j b q mid → ClearPlan xs mid out → ClearPlan ((j,b)::xs) q out := by run_tac checkedFrom `SerializedBodyCompletion.Kernel "SerializedBodyCompletion" "ClearPlan.cons"
private abbrev st : Nat → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Support "FullBodyClosure" "st"
private abbrev FromHRows : Fin 7500 → Fin 7500 → Prop := by run_tac checkedFrom `FullBodyClosure.Beta "FullBodyClosure" "FromHRows"
private abbrev DecRows : Nat → Fin 7500 → Fin 7500 → Fin 7500 → Prop := by run_tac checkedFrom `FullBodyClosure.Beta "FullBodyClosure" "DecRows"
private abbrev BetaSeekRows : Fin 7500 → Fin 7500 → Prop := by run_tac checkedFrom `FullBodyClosure.Beta "FullBodyClosure" "BetaSeekRows"
private abbrev BetaReturnRows : Fin 7500 → Fin 7500 → Prop := by run_tac checkedFrom `FullBodyClosure.Beta "FullBodyClosure" "BetaReturnRows"
private abbrev BetaLiftRows : Fin 7500 → (Bool → Fin 7500) → Prop := by run_tac checkedFrom `FullBodyClosure.Beta "FullBodyClosure" "BetaLiftRows"
private abbrev BetaMoveRows : Fin 7500 → Bool → (Bool → Fin 7500) → Prop := by run_tac checkedFrom `FullBodyClosure.Beta "FullBodyClosure" "BetaMoveRows"
private abbrev BetaDoneRows : Fin 7500 → Fin 7500 → Bool → Prop := by run_tac checkedFrom `FullBodyClosure.Beta "FullBodyClosure" "BetaDoneRows"
private abbrev lookupState : Fin 3 → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Beta "FullBodyClosure" "lookupState"
private abbrev lookupLoopState : Fin 3 → Bool → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Beta "FullBodyClosure" "lookupLoopState"
private abbrev returnState : Fin 3 → Bool → Fin 7500 := by run_tac checkedFrom `FullBodyClosure.Beta "FullBodyClosure" "returnState"
private abbrev LookupRows : Fin 3 → Prop := by run_tac checkedFrom `FullBodyClosure.Beta "FullBodyClosure" "LookupRows"
section LiteralRows
set_option maxRecDepth 4000
private theorem betaLiftCode0 : BetaLiftRows (lookupState ⟨0,by decide⟩) (lookupLoopState ⟨0,by decide⟩) := by
  refine ⟨(st 2988),(st 2984),(st 2983),(fun b=>if b then (st 2982) else (st 2978)),by decide,by decide,by decide,rfl,⟨(st 2987),(st 2986),(st 2985),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,?_⟩
  intro b;cases b
  · exact ⟨rfl,⟨(st 2977),by decide,(by intro x;cases x <;> rfl),rfl,⟨(st 2975),(st 2976),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩⟩
  · exact ⟨rfl,⟨(st 2981),by decide,(by intro x;cases x <;> rfl),rfl,⟨(st 2979),(st 2980),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩⟩
private theorem betaDoneCode0_0 : BetaDoneRows (st 2997) (returnState ⟨0,by decide⟩ false) false := by
  exact ⟨(st 2991),(st 2990),⟨(st 2993),(st 2992),⟨(st 2996),(st 2995),(st 2994),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩,by decide,by decide,rfl,(by intro x;cases x <;> rfl),rfl⟩,by decide,rfl,⟨(st 1415),by decide,(by intro x;cases x <;> rfl),rfl,⟨(st 1413),(st 1414),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩⟩
private theorem betaMoveCode0_0 : BetaMoveRows (st 3006) false (lookupLoopState ⟨0,by decide⟩) := by
  refine ⟨(st 2998),(st 2999),(fun b=>if b then (st 2982) else (st 2978)),⟨(st 3002),(st 3001),⟨(st 3005),(st 3004),(st 3003),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩,by decide,by decide,rfl,(by intro x;cases x <;> rfl),rfl⟩,by decide,by decide,rfl,?_⟩
  intro b;cases b
  · exact ⟨rfl,⟨(st 2977),by decide,(by intro x;cases x <;> rfl),rfl,⟨(st 2975),(st 2976),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩⟩
  · exact ⟨rfl,⟨(st 2981),by decide,(by intro x;cases x <;> rfl),rfl,⟨(st 2979),(st 2980),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩⟩
private theorem betaDoneCode0_1 : BetaDoneRows (st 3028) (returnState ⟨0,by decide⟩ true) true := by
  exact ⟨(st 3022),(st 3021),⟨(st 3024),(st 3023),⟨(st 3027),(st 3026),(st 3025),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩,by decide,by decide,rfl,(by intro x;cases x <;> rfl),rfl⟩,by decide,rfl,⟨(st 3020),by decide,(by intro x;cases x <;> rfl),rfl,⟨(st 3018),(st 3019),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩⟩
private theorem betaMoveCode0_1 : BetaMoveRows (st 3037) true (lookupLoopState ⟨0,by decide⟩) := by
  refine ⟨(st 3029),(st 3030),(fun b=>if b then (st 2982) else (st 2978)),⟨(st 3033),(st 3032),⟨(st 3036),(st 3035),(st 3034),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩,by decide,by decide,rfl,(by intro x;cases x <;> rfl),rfl⟩,by decide,by decide,rfl,?_⟩
  intro b;cases b
  · exact ⟨rfl,⟨(st 2977),by decide,(by intro x;cases x <;> rfl),rfl,⟨(st 2975),(st 2976),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩⟩
  · exact ⟨rfl,⟨(st 2981),by decide,(by intro x;cases x <;> rfl),rfl,⟨(st 2979),(st 2980),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩⟩
private theorem lookupCode0 : LookupRows ⟨0,by decide⟩ := by
  refine ⟨(fun b : Bool=>if b then (st 3047) else (st 3016)),(fun b : Bool=>if b then (st 3028) else (st 2997)),(fun b : Bool=>if b then (st 3037) else (st 3006)),?_⟩
  intro b;cases b
  · exact ⟨by decide,rfl,⟨(st 3014),(st 3007),(st 3013),(st 3012),(st 3009),(st 3011),by decide,by decide,by decide,by decide,(rnext (s:=(st 3015)) (q:=(st 3014)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (rnil 1 (st 3014))),(lnext (s:=(st 3008)) (q:=(st 2997)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (lnil 0 (st 2997))),(lnext (s:=(st 3010)) (q:=(st 3006)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (lnil 0 (st 3006))),rfl,rfl,(by intro x hx;cases x with | none => rfl | some x => cases x with | false => rfl | true => exact False.elim (hx rfl)),rfl,rfl,(by intro x;cases x <;> rfl),rfl⟩,betaDoneCode0_0,betaMoveCode0_0⟩
  · exact ⟨by decide,rfl,⟨(st 3045),(st 3038),(st 3044),(st 3043),(st 3040),(st 3042),by decide,by decide,by decide,by decide,(rnext (s:=(st 3046)) (q:=(st 3045)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (rnil 1 (st 3045))),(lnext (s:=(st 3039)) (q:=(st 3028)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (lnil 0 (st 3028))),(lnext (s:=(st 3041)) (q:=(st 3037)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (lnil 0 (st 3037))),rfl,rfl,(by intro x hx;cases x with | none => rfl | some x => cases x with | false => rfl | true => exact False.elim (hx rfl)),rfl,rfl,(by intro x;cases x <;> rfl),rfl⟩,betaDoneCode0_1,betaMoveCode0_1⟩
end LiteralRows
end FullBodyClosure
