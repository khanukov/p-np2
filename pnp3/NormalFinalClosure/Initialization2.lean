import NormalFinalClosure.LengthLoop2
import NormalFinalClosure.FrameFacts2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path","Grid","Unary","from_H","clear_run","keep"]),
    (`PhysicalCallerClosure.UnaryCopy,`PhysicalCallerClosure,["field","field_grid","field_unary","field_other","field_self","field_repeat","field_comm","mono","blanks"]),
    (`NormalFinalClosure.Copy2,`NormalFinalClosure,["copy_run","paint_field","three"]),
    (`NormalFinalClosure.Halving2,`NormalFinalClosure,["I"]),
    (`NormalFinalClosure.LengthLoop2,`NormalFinalClosure,["length_loop","length_step"]),
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["ns2","Safe2","ns2_safe"]),
    (`NormalFinalClosure.CodeCertificates2,`NormalFinalClosure,["clearCode_0","clearCode_1","clearCode_2","clearCode_3"]),
    (`NormalFinalClosure.MacroCertificates2,`NormalFinalClosure,["fromHCode","copyCore_0","macroEntry_0"]),
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,["D","GuardFrame","GuardFrame.window","GuardFrame.windowRoom","GuardFrame.positive","GuardFrame.right","GuardFrame.paid","GuardFrame.gap","GuardFrame.fence","GuardFrame.headBefore"]),
    (`NormalFinalClosure.FrameFacts2,`NormalFinalClosure,["frame_grid","d_mono"])] do
    for leaf in leaves do
      let name:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? name | throwError "Missing exact initialization API {name}"
      let some i:=e.getModuleIdxFor? name | throwError "Missing initialization owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong initialization owner"
      logInfo m!"native-initialization-interface|{name}|{ci.type}"
      let aliasName:=(leaf.splitOn ".").getLast!
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac do
    let owner:=`PhysicalCallerClosure.Engine
    let name:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") "Node") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? name | throwError "Missing initialization Node constructor"
    let some i:=e.getModuleIdxFor? name | throwError "Missing initialization Node owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong initialization Node owner"
    closeMainGoal `node (mkConst name (ci.levelParams.map Level.param))
private def reset (T : Nat → Option Bool) (d : Nat → Nat) : Nat → Option Bool :=
  field (field (field (field T d 4 0) d 5 0) d 6 0) d 11 0
private theorem reset_grid {T d} (g:Grid d T) : Grid d (reset T d) :=
  field_grid (field_grid (field_grid (field_grid g 4 0 (by decide)) 5 0 (by decide)) 6 0 (by decide)) 11 0 (by decide)
private theorem reset_same {T d j v} (g:Grid d T) (hj:j < 13)
    (j4:j≠4) (j5:j≠5) (j6:j≠6) (j11:j≠11) (original:Unary d T j v) : Unary d (reset T d) j v :=
  field_other (field_grid (field_grid (field_grid g 4 0 (by decide)) 5 0 (by decide)) 6 0 (by decide)) (by decide) hj j11.symm
    (field_other (field_grid (field_grid g 4 0 (by decide)) 5 0 (by decide)) (by decide) hj j6.symm
      (field_other (field_grid g 4 0 (by decide)) (by decide) hj j5.symm
        (field_other g (by decide) hj j4.symm original)))
private theorem reset_zero4 {T d} (g:Grid d T) : Unary d (reset T d) 4 0 := by
  apply field_other (field_grid (field_grid (field_grid g 4 0 (by decide)) 5 0 (by decide)) 6 0 (by decide)) (by decide) (by decide) (by decide)
  apply field_other (field_grid (field_grid g 4 0 (by decide)) 5 0 (by decide)) (by decide) (by decide) (by decide)
  exact field_other (field_grid g 4 0 (by decide)) (by decide) (by decide) (by decide) (field_unary T d 4 0)
private theorem reset_zero5 {T d} (g:Grid d T) : Unary d (reset T d) 5 0 := by
  apply field_other (field_grid (field_grid (field_grid g 4 0 (by decide)) 5 0 (by decide)) 6 0 (by decide)) (by decide) (by decide) (by decide)
  exact field_other (field_grid (field_grid g 4 0 (by decide)) 5 0 (by decide)) (by decide) (by decide) (by decide) (field_unary _ d 5 0)
private theorem reset_zero6 {T d} (g:Grid d T) : Unary d (reset T d) 6 0 :=
  field_other (field_grid (field_grid (field_grid g 4 0 (by decide)) 5 0 (by decide)) 6 0 (by decide)) (by decide) (by decide) (by decide) (field_unary _ d 6 0)
/-- The actual H-entry through reset, W copy and the COMPLETE physical length
loop, at arbitrary source/beta and including all zero-width delimiter geometry. -/
private theorem initialization (k : Nat) {S z n F r W source T}
    (frame:GuardFrame S z n F r W source T) :
    let d:=D F r n
    ∃ t,t ≤ 4096*(r+1)^2*(d 13+1) ∧ Path (machine2 k) (Safe2 k) (d 13) t
      (node (ns2 k 1) (S+z+2+n+1) T)
      (node (ns2 k 445) (d 0) (I (reset T d) d 0 0 (bitLength W))) := by
  intro d
  have g:=frame_grid frame
  change Grid d T at g
  have width (j : Nat) (hj:j=3 ∨ j=4 ∨ j=5 ∨ j=6):d (j+1)=d j+r+1:=by
    rcases hj with eq|eq|eq|eq <;> subst j <;> norm_num only [d,D,SerializedBody.delimiter,ite_true,ite_false] <;> omega
  have paidRoom:S+z+2+n+2 < F:=by
    have h:=headBefore frame
    by_contra bad
    have eq:F=S+z+2+n+2:=by omega
    have a:=paid frame;have b:=fence frame
    rw [eq] at b
    rw [a] at b
    cases b
  have head:=from_H (Q:=1) (by decide) (by omega) (show F+1 ≤ d 13 by change F+1 ≤ F+13*r+2*n+22;omega)
    (fence frame) (right frame)
    (by
      intro i lo hi
      have eq:i=S+z+2+n+2:=by omega
      rw [eq]
      exact paid frame) (gap frame) (fromHCode k)
  have c4:=clear_run g (by decide) le_rfl (clearCode_0 k)
  rw [paint_field g 4 (by decide) false] at c4
  have g4:=field_grid g 4 0 (by decide)
  have c5:=clear_run g4 (by decide) le_rfl (clearCode_1 k)
  rw [paint_field g4 5 (by decide) false] at c5
  have g5:=field_grid g4 5 0 (by decide)
  have c6:=clear_run g5 (by decide) le_rfl (clearCode_2 k)
  rw [paint_field g5 6 (by decide) false] at c6
  have g6:=field_grid g5 6 0 (by decide)
  have c11:=clear_run g6 (by decide) le_rfl (clearCode_3 k)
  rw [paint_field g6 11 (by decide) false] at c11
  have gr:=reset_grid g
  have entry:=keep (ns2 k 124) (ns2 k 125) (d 0) (d 0) (reset T d) .stay (P:=d 13)
    (d_mono F r n 0 13 (by decide) (by decide)) (d_mono F r n 0 13 (by decide) (by decide)) (ns2_safe k 124)
    (by rw [blanks gr 0 (by decide)];exact macroEntry_0 k) rfl
  have original:Unary d T 3 W:=by
    intro i lo hi
    exact window frame i lo hi
  have saved:=reset_same g (by decide) (by decide) (by decide) (by decide) (by decide) original
  obtain ⟨ct,cp,copy⟩:=copy_run gr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    le_rfl (fun j hj=>width j (by rcases hj with h|h|h;exact Or.inl h;exact Or.inr (Or.inl h);exact Or.inr (Or.inr (Or.inl h))))
    saved (reset_zero4 g) (reset_zero5 g) (windowRoom frame) (copyCore_0 k)
  have ellLe:∀ v : Nat,bitLength v ≤ v:=by
    intro v
    induction v using Nat.strong_induction_on with
    | h v ih=>
      by_cases hz:v=0
      · subst v;exact le_rfl
      · have eq:=length_step v (by omega)
        have half:=ih (v/2) (Nat.div_lt_self (by omega) (by decide))
        omega
  have ellCap:bitLength W ≤ r:=(ellLe W).trans (windowRoom frame)
  obtain ⟨lt,lp,length⟩:=length_loop k gr le_rfl
    (fun j hj=>width j (Or.inr hj)) W 0 (windowRoom frame) (by simpa only [Nat.zero_add] using ellCap)
  have start:I (reset T d) d W 0 0=field (reset T d) d 4 W:=by
    dsimp only [I,three]
    rw [field_self (field_other gr (by decide) (by decide) (by decide) (reset_zero5 g))]
    exact field_self (field_other (j:=4) (k:=6) gr (by decide) (by decide) (by decide) (reset_zero6 g))
  rw [start] at length
  have path:=head.append (c4.append (c5.append (c6.append (c11.append (entry.append (copy.append length))))))
  refine ⟨_,?_,by simpa only [Nat.zero_add,reset] using path⟩
  have widths (j : Nat) (hj:j ≤ 12):d j ≤ d 13:=d_mono F r n j 13 (by omega) (by decide)
  have p4:2*(d 5-d 0+4)+2 ≤ 64*(d 13+1):=by have h:=widths 5 (by decide);omega
  have p5:2*(d 6-d 0+5)+2 ≤ 64*(d 13+1):=by have h:=widths 6 (by decide);omega
  have p6:2*(d 7-d 0+6)+2 ≤ 64*(d 13+1):=by have h:=widths 7 (by decide);omega
  have p11:2*(d 12-d 0+11)+2 ≤ 64*(d 13+1):=by have h:=widths 12 (by decide);omega
  have hPrice:F+1-(S+z+2+n+1) ≤ d 13+1:=by change _ ≤ F+13*r+2*n+22+1;omega
  have wp:=windowRoom frame
  have monoSq:(W+1)^2 ≤ (r+1)^2:=Nat.pow_le_pow_left (by omega) 2
  have upper:=Nat.mul_le_mul_right (d 13+1) (Nat.mul_le_mul_left 1024 monoSq)
  have oneSq:r+1 ≤ (r+1)^2:=by nlinarith
  nlinarith only [p4,p5,p6,p11,hPrice,cp,lp,upper,wp,oneSq]
end NormalFinalClosure
