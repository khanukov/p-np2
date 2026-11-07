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
private theorem betaLiftCode2 : BetaLiftRows (lookupState ⟨2,by decide⟩) (lookupLoopState ⟨2,by decide⟩) := by
  refine ⟨(st 7442),(st 7438),(st 7437),(fun b=>if b then (st 7436) else (st 7432)),by decide,by decide,by decide,rfl,⟨(st 7441),(st 7440),(st 7439),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,?_⟩
  intro b;cases b
  · exact ⟨rfl,⟨(st 7431),by decide,(by intro x;cases x <;> rfl),rfl,⟨(st 7429),(st 7430),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩⟩
  · exact ⟨rfl,⟨(st 7435),by decide,(by intro x;cases x <;> rfl),rfl,⟨(st 7433),(st 7434),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩⟩
private theorem betaDoneCode2_0 : BetaDoneRows (st 7451) (returnState ⟨2,by decide⟩ false) false := by
  exact ⟨(st 7445),(st 7444),⟨(st 7447),(st 7446),⟨(st 7450),(st 7449),(st 7448),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩,by decide,by decide,rfl,(by intro x;cases x <;> rfl),rfl⟩,by decide,rfl,⟨(st 1408),by decide,(by intro x;cases x <;> rfl),rfl,⟨(st 1406),(st 1407),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩⟩
private theorem betaMoveCode2_0 : BetaMoveRows (st 7460) false (lookupLoopState ⟨2,by decide⟩) := by
  refine ⟨(st 7452),(st 7453),(fun b=>if b then (st 7436) else (st 7432)),⟨(st 7456),(st 7455),⟨(st 7459),(st 7458),(st 7457),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩,by decide,by decide,rfl,(by intro x;cases x <;> rfl),rfl⟩,by decide,by decide,rfl,?_⟩
  intro b;cases b
  · exact ⟨rfl,⟨(st 7431),by decide,(by intro x;cases x <;> rfl),rfl,⟨(st 7429),(st 7430),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩⟩
  · exact ⟨rfl,⟨(st 7435),by decide,(by intro x;cases x <;> rfl),rfl,⟨(st 7433),(st 7434),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩⟩
private theorem betaDoneCode2_1 : BetaDoneRows (st 7479) (returnState ⟨2,by decide⟩ true) true := by
  exact ⟨(st 7473),(st 7472),⟨(st 7475),(st 7474),⟨(st 7478),(st 7477),(st 7476),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩,by decide,by decide,rfl,(by intro x;cases x <;> rfl),rfl⟩,by decide,rfl,⟨(st 4037),by decide,(by intro x;cases x <;> rfl),rfl,⟨(st 4035),(st 4036),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩⟩
private theorem betaMoveCode2_1 : BetaMoveRows (st 7488) true (lookupLoopState ⟨2,by decide⟩) := by
  refine ⟨(st 7480),(st 7481),(fun b=>if b then (st 7436) else (st 7432)),⟨(st 7484),(st 7483),⟨(st 7487),(st 7486),(st 7485),by decide,by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩,by decide,by decide,rfl,(by intro x;cases x <;> rfl),rfl⟩,by decide,by decide,rfl,?_⟩
  intro b;cases b
  · exact ⟨rfl,⟨(st 7431),by decide,(by intro x;cases x <;> rfl),rfl,⟨(st 7429),(st 7430),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩⟩
  · exact ⟨rfl,⟨(st 7435),by decide,(by intro x;cases x <;> rfl),rfl,⟨(st 7433),(st 7434),by decide,by decide,by decide,rfl,rfl,rfl,rfl,rfl,rfl⟩⟩⟩
private theorem lookupCode2 : LookupRows ⟨2,by decide⟩ := by
  refine ⟨(fun b : Bool=>if b then (st 7498) else (st 7470)),(fun b : Bool=>if b then (st 7479) else (st 7451)),(fun b : Bool=>if b then (st 7488) else (st 7460)),?_⟩
  intro b;cases b
  · exact ⟨by decide,rfl,⟨(st 7468),(st 7461),(st 7467),(st 7466),(st 7463),(st 7465),by decide,by decide,by decide,by decide,(rnext (s:=(st 7469)) (q:=(st 7468)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (rnil 1 (st 7468))),(lnext (s:=(st 7462)) (q:=(st 7451)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (lnil 0 (st 7451))),(lnext (s:=(st 7464)) (q:=(st 7460)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (lnil 0 (st 7460))),rfl,rfl,(by intro x hx;cases x with | none => rfl | some x => cases x with | false => rfl | true => exact False.elim (hx rfl)),rfl,rfl,(by intro x;cases x <;> rfl),rfl⟩,betaDoneCode2_0,betaMoveCode2_0⟩
  · exact ⟨by decide,rfl,⟨(st 7496),(st 7489),(st 7495),(st 7494),(st 7491),(st 7493),by decide,by decide,by decide,by decide,(rnext (s:=(st 7497)) (q:=(st 7496)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (rnil 1 (st 7496))),(lnext (s:=(st 7490)) (q:=(st 7479)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (lnil 0 (st 7479))),(lnext (s:=(st 7492)) (q:=(st 7488)) (by decide) (by decide) rfl (by intro x;cases x <;> rfl) rfl (lnil 0 (st 7488))),rfl,rfl,(by intro x hx;cases x with | none => rfl | some x => cases x with | false => rfl | true => exact False.elim (hx rfl)),rfl,rfl,(by intro x;cases x <;> rfl),rfl⟩,betaDoneCode2_1,betaMoveCode2_1⟩
end LiteralRows
end FullBodyClosure
