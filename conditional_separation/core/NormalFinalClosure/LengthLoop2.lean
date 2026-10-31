import NormalFinalClosure.Halving2
import BitLengthDriver.Kernel
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path","Grid","Unary","keep","dec_zero","dec_positive","inc_success"]),
    (`PhysicalCallerClosure.UnaryCopy,`PhysicalCallerClosure,["field","field_dec","field_inc","mono","blanks"]),
    (`NormalFinalClosure.Copy2,`NormalFinalClosure,["op_price","transfer_run"]),
    (`NormalFinalClosure.Halving2,`NormalFinalClosure,["I","ig","iv","ia","ic","iwv","iwa","iwc","pair_loop"]),
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["ns2","Safe2","ns2_safe"]),
    (`NormalFinalClosure.CodeCertificates2,`NormalFinalClosure,["decCode_9","incCode_10","incCode_11","decCode_12","decCode_13","incCode_14"]),
    (`NormalFinalClosure.MacroCertificates2,`NormalFinalClosure,["transferCore_1","macroEntry_1"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing exact length-loop API {name}"
      let some i:=e.getModuleIdxFor? name | throwError "Missing length-loop owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong length-loop owner"
      let kind:=match ci with|.defnInfo _=>"definition"|.thmInfo _=>"theorem"|.inductInfo _=>"inductive"|_=>"other"
      unless kind != "other" do throwError "Wrong length-loop kind"
      logInfo m!"literal-length-loop-interface|{name}|{kind}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) name::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac do
    let owner:=`PhysicalCallerClosure.Engine
    let name:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") "Node") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? name | throwError "Missing literal node constructor"
    let some i:=e.getModuleIdxFor? name | throwError "Missing literal node owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong literal node owner"
    closeMainGoal `node (mkConst name (ci.levelParams.map Level.param))
private theorem length_step : ∀ v : Nat,0 < v → bitLength v=bitLength (v/2)+1 := by
  run_tac do
    let owner:=`BitLengthDriver.Kernel
    let name:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "BitLengthDriver") "length_step"
    let e←getEnv
    let some (.thmInfo ci):=e.find? name | throwError "Missing exact arithmetic length identity"
    let some i:=e.getModuleIdxFor? name | throwError "Missing arithmetic owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong arithmetic owner"
    logInfo m!"actual-length-identity-full-type|{name}|{ci.type}"
    closeMainGoal `length_step (mkConst name (ci.levelParams.map Level.param))
private theorem loop_price (v d P t h : Nat) (dv:d < v)
    (small:h ≤ 512*(v+1)*(P+1)) (tail:t ≤ 1024*(d+1)^2*(P+1)) :
    h+t ≤ 1024*(v+1)^2*(P+1) := by
  have square:(d+1)^2+v+1 ≤ (v+1)^2:=by nlinarith
  have monotone:=Nat.mul_le_mul_right (P+1) (Nat.mul_le_mul_left 1024 square)
  nlinarith only [small,tail,monotone]
/-- Complete physical bitLength loop of ROM v2, including zero detection,
positive probe/reinsert, counted pair drains, every transfer and return stay. -/
private theorem length_loop (k : Nat) {D T w P} (grid:Grid D T) (room:D 13 ≤ P)
    (width:∀ j,j=4 ∨ j=5 ∨ j=6 → D (j+1)=D j+w+1)
    (v c : Nat) (vr:v ≤ w) (cap:c+bitLength v ≤ w) :
    ∃ t,t ≤ 1024*(v+1)^2*(P+1) ∧ Path (machine2 k) (Safe2 k) P t
      (node (ns2 k 238) (D 0) (I T D v 0 c))
      (node (ns2 k 445) (D 0) (I T D 0 0 (c+bitLength v))) := by
  have sw:D 5=D 4+w+1:=width 4 (by simp)
  have dw:D 6=D 5+w+1:=width 5 (by simp)
  have cw:D 7=D 6+w+1:=width 6 (by simp)
  have wP:w ≤ P:=by have h:=mono grid 5 13 (by decide) le_rfl;omega
  have d4:D 4 ≤ P:=(mono grid 4 13 (by decide) le_rfl).trans room
  have d6:D 6 ≤ P:=(mono grid 6 13 (by decide) le_rfl).trans room
  induction v using Nat.strong_induction_on generalizing c with
  | h v ih=>
    by_cases vz:v=0
    · subst v
      have step:=dec_zero (ig (v:=0) (a:=0) (c:=c) grid) (by decide) room sw (iv grid) (decCode_9 k)
      refine ⟨2*(D 4-D 0+4)+3,?_,?_⟩
      · have price:=op_price D 4 0 P d4 (by decide) (by omega)
        norm_num only [Nat.zero_add,one_pow,one_mul]
        omega
      · simpa only [show bitLength 0=0 from rfl,Nat.add_zero] using step
    · have vp:0 < v:=by omega
      have ell:=length_step v vp
      have g:=ig (v:=v) (a:=0) (c:=c) grid
      have probe:=dec_positive g (by decide) room sw (iv grid) vp vr (decCode_9 k)
      rw [field_dec g (by decide) sw (iv grid) vp vr,iwv grid] at probe
      have g1:=ig (v:=v-1) (a:=0) (c:=c) grid
      have restore:=inc_success g1 (by decide) room sw (iv grid) (by omega) (incCode_10 k)
      rw [field_inc g1 (by decide) sw (iv grid) (by omega),iwv grid,show v-1+1=v by omega] at restore
      have count:=inc_success g (by decide) room cw (ic T D v 0 c) (by omega) (incCode_11 k)
      rw [field_inc g (by decide) cw (ic T D v 0 c) (by omega),iwc] at count
      obtain ⟨pairT,pairPrice,pairs⟩:=pair_loop grid room sw dw (decCode_12 k) (decCode_13 k) (incCode_14 k) v 0 (c+1) vr (by omega)
      simp only [Nat.zero_add] at pairs
      have g2:=ig (v:=0) (a:=v/2) (c:=c+1) grid
      have at0:=blanks g2 0 (by decide)
      have stay:=keep (ns2 k 391) (ns2 k 392) (D 0) (D 0) (I T D 0 (v/2) (c+1)) .stay
        (P:=P) ((mono grid 0 13 (by decide) le_rfl).trans room) ((mono grid 0 13 (by decide) le_rfl).trans room)
        (ns2_safe k 391) (by rw [at0];exact macroEntry_1 k) rfl
      obtain ⟨transferT,transferPrice,transfer⟩:=transfer_run g2 (by decide) (by decide) (by decide) room dw sw
        (ia grid) (iv grid) (by omega) (transferCore_1 k)
      rw [iwa grid,iwv grid] at transfer
      simp only [Nat.zero_add] at transfer
      have smaller:v/2 < v:=Nat.div_lt_self vp (by decide)
      obtain ⟨tailT,tailPrice,tail⟩:=ih (v/2) smaller (c+1) (by omega) (by omega)
      have path:=probe.append (restore.append (count.append (pairs.append (stay.append (transfer.append tail)))))
      let h:=(2*(D 4-D 0+4)+2*v+3)+((2*(D 4-D 0+4)+2*(v-1)+3)+((2*(D 6-D 0+6)+2*c+3)+(pairT+(1+transferT))))
      refine ⟨h+tailT,?_,?_⟩
      · have p1:=op_price D 4 v P d4 (by decide) (by omega)
        have p2:=op_price D 4 (v-1) P d4 (by decide) (by omega)
        have p3:=op_price D 6 c P d6 (by decide) (by omega)
        have phase:h ≤ 512*(v+1)*(P+1):=by
          dsimp only [h]
          have d:v/2+1 ≤ v+1:=by omega
          have pt:=Nat.mul_le_mul_right (P+1) (Nat.mul_le_mul_left 128 d)
          nlinarith only [p1,p2,p3,pairPrice,transferPrice,pt]
        exact loop_price v (v/2) P tailT h smaller phase tailPrice
      · rw [show c+1+bitLength (v/2)=c+bitLength v by omega] at path
        simpa only [h,Nat.add_assoc] using path
end NormalFinalClosure
