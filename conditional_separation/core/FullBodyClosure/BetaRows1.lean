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
private theorem betaLiftCode1 : BetaLiftRows (lookupState ⟨1,by decide⟩) (lookupLoopState ⟨1,by decide⟩) := by
  refine ⟨(st 5375),(st 5371),(st 5370),(fun b=>if b then (st 5369) else (st 5365)),by decide,by decide,by decide,rfl,⟨(st 5374),(st 5373),(st 5372),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,?_⟩
  intro b;cases b
  · exact ⟨rfl,⟨(st 5364),by decide,(by intro x;cases x <;> rfl),rfl,⟨(st 5362),(st 5363),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩⟩
  · exact ⟨rfl,⟨(st 5368),by decide,(by intro x;cases x <;> rfl),rfl,⟨(st 5366),(st 5367),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩⟩
private theorem betaDoneCode1_0 : BetaDoneRows (st 5384) (returnState ⟨1,by decide⟩ false) false := by
  exact ⟨(st 5378),(st 5377),⟨(st 5380),(st 5379),⟨(st 5383),(st 5382),(st 5381),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩,by decide,by decide,rfl,(by intro x;cases x <;> rfl),rfl⟩,by decide,rfl,⟨(st 1423),by decide,(by intro x;cases x <;> rfl),rfl,⟨(st 1421),(st 1422),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩⟩
private theorem betaMoveCode1_0 : BetaMoveRows (st 5393) false (lookupLoopState ⟨1,by decide⟩) := by
  refine ⟨(st 5385),(st 5386),(fun b=>if b then (st 5369) else (st 5365)),⟨(st 5389),(st 5388),⟨(st 5392),(st 5391),(st 5390),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩,by decide,by decide,rfl,(by intro x;cases x <;> rfl),rfl⟩,by decide,by decide,rfl,?_⟩
  intro b;cases b
  · exact ⟨rfl,⟨(st 5364),by decide,(by intro x;cases x <;> rfl),rfl,⟨(st 5362),(st 5363),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩⟩
  · exact ⟨rfl,⟨(st 5368),by decide,(by intro x;cases x <;> rfl),rfl,⟨(st 5366),(st 5367),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩⟩
private theorem betaDoneCode1_1 : BetaDoneRows (st 5412) (returnState ⟨1,by decide⟩ true) true := by
  exact ⟨(st 5406),(st 5405),⟨(st 5408),(st 5407),⟨(st 5411),(st 5410),(st 5409),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩,by decide,by decide,rfl,(by intro x;cases x <;> rfl),rfl⟩,by decide,rfl,⟨(st 4049),by decide,(by intro x;cases x <;> rfl),rfl,⟨(st 4047),(st 4048),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩⟩
private theorem betaMoveCode1_1 : BetaMoveRows (st 5421) true (lookupLoopState ⟨1,by decide⟩) := by
  refine ⟨(st 5413),(st 5414),(fun b=>if b then (st 5369) else (st 5365)),⟨(st 5417),(st 5416),⟨(st 5420),(st 5419),(st 5418),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩,by decide,by decide,rfl,(by intro x;cases x <;> rfl),rfl⟩,by decide,by decide,rfl,?_⟩
  intro b;cases b
  · exact ⟨rfl,⟨(st 5364),by decide,(by intro x;cases x <;> rfl),rfl,⟨(st 5362),(st 5363),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩⟩
  · exact ⟨rfl,⟨(st 5368),by decide,(by intro x;cases x <;> rfl),rfl,⟨(st 5366),(st 5367),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩⟩
private theorem lookupCode1 : LookupRows ⟨1,by decide⟩ := by
  refine ⟨(fun b : Bool=>if b then (st 5431) else (st 5403)),(fun b : Bool=>if b then (st 5412) else (st 5384)),(fun b : Bool=>if b then (st 5421) else (st 5393)),?_⟩
  intro b;cases b
  · exact ⟨by decide,rfl,⟨(st 5401),(st 5394),(st 5400),(st 5399),(st 5396),(st 5398),by decide,by decide,by decide,by decide,(rnext (s:=(st 5402)) (q:=(st 5401)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (rnil 1 (st 5401))),(lnext (s:=(st 5395)) (q:=(st 5384)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (lnil 0 (st 5384))),(lnext (s:=(st 5397)) (q:=(st 5393)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (lnil 0 (st 5393))),rfl,rfl,(by intro x hx;cases x with | none => rfl | some x => cases x with | false => rfl | true => exact False.elim (hx rfl)),rfl,rfl,(by intro x;cases x <;> rfl),rfl⟩,betaDoneCode1_0,betaMoveCode1_0⟩
  · exact ⟨by decide,rfl,⟨(st 5429),(st 5422),(st 5428),(st 5427),(st 5424),(st 5426),by decide,by decide,by decide,by decide,(rnext (s:=(st 5430)) (q:=(st 5429)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (rnil 1 (st 5429))),(lnext (s:=(st 5423)) (q:=(st 5412)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (lnil 0 (st 5412))),(lnext (s:=(st 5425)) (q:=(st 5421)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (lnil 0 (st 5421))),rfl,rfl,(by intro x hx;cases x with | none => rfl | some x => cases x with | false => rfl | true => exact False.elim (hx rfl)),rfl,rfl,(by intro x;cases x <;> rfl),rfl⟩,betaDoneCode1_1,betaMoveCode1_1⟩
end LiteralRows
end FullBodyClosure
