import NormalFinalClosure.Copy2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path","Grid","Unary","DecRows","IncRows","dec_zero","dec_positive","inc_success"]),
    (`PhysicalCallerClosure.UnaryCopy,`PhysicalCallerClosure,["field","field_dec","field_inc","mono"]),
    (`NormalFinalClosure.Copy2,`NormalFinalClosure,["three","three_grid","three_s","three_d","three_5","three_write_s","three_write_d","three_write_5","op_price"])] do
    for leaf in leaves do
      let name:=Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns) leaf
      let some ci:=e.find? name | throwError "Missing exact native Horner API"
      let some i:=e.getModuleIdxFor? name | throwError "Missing Horner owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong Horner owner"
      logInfo m!"capped-native-Horner-interface|{name}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) name::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac do
    let owner:=`PhysicalCallerClosure.Engine
    let name:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") "Node") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? name | throwError "Missing Horner Node"
    let some i:=e.getModuleIdxFor? name | throwError "Missing Horner Node owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong Horner Node owner"
    closeMainGoal `node (mkConst name (ci.levelParams.map Level.param))
variable {M : UniformTM} {Safe : Fin M.stateCount → Prop}
private abbrev J (T : Nat → Option Bool) (D : Nat → Nat) (v a q : Nat) := three T D 11 5 4 v a q
private theorem jg {T D v a q} (g:Grid D T) : Grid D (J T D v a q) :=
  three_grid g (by decide) (by decide) (by decide)
private theorem jv {T D v a q} (g:Grid D T) : Unary D (J T D v a q) 11 v :=
  three_s g (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem ja {T D v a q} (g:Grid D T) : Unary D (J T D v a q) 5 a :=
  three_d g (by decide) (by decide) (by decide) (by decide)
private theorem jq (T D v a q) : Unary D (J T D v a q) 4 q := three_5 T D 11 5 4 v a q
private theorem jwv {T D v a q x} (g:Grid D T) : field (J T D v a q) D 11 x=J T D x a q :=
  three_write_s g (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem jwa {T D v a q x} (g:Grid D T) : field (J T D v a q) D 5 x=J T D v x q :=
  three_write_d g (by decide) (by decide) (by decide) (by decide)
private theorem jwq (T D v a q x) : field (J T D v a q) D 4 x=J T D v a x := three_write_5 T D 11 5 4 v a q x
/-- The actual doubling loop aborts through the paid available-field read,
before any unbounded materialization. This theorem also specifies the dirty
finite counter image on overflow, for the common real cleanup. -/
private theorem double_loop {D T w P start available add1 add2 out fail}
    (grid:Grid D T) (room:D 13 ≤ P)
    (iw:D 12=D 11+w+1) (aw:D 6=D 5+w+1) (qw:D 5=D 4+w+1)
    (take:DecRows (M:=M) (Safe:=Safe) 11 start out available)
    (pay:DecRows (M:=M) (Safe:=Safe) 4 available fail add1)
    (inc1:IncRows (M:=M) (Safe:=Safe) 5 add1 add2)
    (inc2:IncRows (M:=M) (Safe:=Safe) 5 add2 start)
    (v a q : Nat) (vr:v ≤ w) (qr:q ≤ w) (cap:a+2*min v q ≤ w) :
    ∃ t,t ≤ 256*(min v q+1)*(P+1) ∧
      if v ≤ q then Path M Safe P t (node start (D 0) (J T D v a q))
        (node out (D 0) (J T D 0 (a+2*v) (q-v)))
      else Path M Safe P t (node start (D 0) (J T D v a q))
        (node fail (D 0) (J T D (v-q-1) (a+2*q) 0)) := by
  have wP:w ≤ P:=by have h:=mono grid 12 13 (by decide) le_rfl;omega
  have di:D 11 ≤ P:=(mono grid 11 13 (by decide) le_rfl).trans room
  have da:D 5 ≤ P:=(mono grid 5 13 (by decide) le_rfl).trans room
  have dq:D 4 ≤ P:=(mono grid 4 13 (by decide) le_rfl).trans room
  induction v generalizing a q with
  | zero=>
    have zero:=dec_zero (jg (v:=0) (a:=a) (q:=q) grid) (by decide) room iw (jv grid) take
    refine ⟨2*(D 11-D 0+11)+3,?_,?_⟩
    · have p:=op_price D 11 0 P di (by decide) (by omega)
      simp only [Nat.zero_min,Nat.zero_add]
      omega
    · simpa only [Nat.zero_le,if_true,Nat.mul_zero,Nat.add_zero,Nat.sub_zero] using zero
  | succ v ih=>
    have g:=jg (v:=v+1) (a:=a) (q:=q) grid
    have one:=dec_positive g (by decide) room iw (jv grid) (by omega) vr take
    rw [field_dec g (by decide) iw (jv grid) (by omega) vr,jwv grid,show v+1-1=v by omega] at one
    cases q with
    | zero=>
      have two:=dec_zero (jg (v:=v) (a:=a) (q:=0) grid) (by decide) room qw (jq T D v a 0) pay
      have path:=one.append two
      refine ⟨(2*(D 11-D 0+11)+2*(v+1)+3)+(2*(D 4-D 0+4)+3),?_,?_⟩
      · have p1:=op_price D 11 (v+1) P di (by decide) (by omega)
        have p2:=op_price D 4 0 P dq (by decide) (by omega)
        simp only [Nat.min_zero,Nat.zero_add]
        omega
      · simpa only [show ¬v+1 ≤ 0 by omega,if_false,Nat.sub_zero,Nat.add_sub_cancel,Nat.mul_zero,Nat.add_zero] using path
    | succ q=>
      have g1:=jg (v:=v) (a:=a) (q:=q+1) grid
      have two:=dec_positive g1 (by decide) room qw (jq T D v a (q+1)) (by omega) qr pay
      rw [field_dec g1 (by decide) qw (jq T D v a (q+1)) (by omega) qr,jwq,show q+1-1=q by omega] at two
      have g2:=jg (v:=v) (a:=a) (q:=q) grid
      have three:=inc_success g2 (by decide) room aw (ja grid) (by omega) inc1
      rw [field_inc g2 (by decide) aw (ja grid) (by omega),jwa grid] at three
      have g3:=jg (v:=v) (a:=a+1) (q:=q) grid
      have four:=inc_success g3 (by decide) room aw (ja grid) (by omega) inc2
      rw [field_inc g3 (by decide) aw (ja grid) (by omega),jwa grid] at four
      obtain ⟨t,price,tail⟩:=ih (a+2) q (by omega) (by omega) (by omega)
      have mid:a+1+1=a+2:=by omega
      rw [mid] at four
      by_cases success:v ≤ q
      · rw [if_pos success] at tail
        have path:=one.append (two.append (three.append (four.append tail)))
        refine ⟨(2*(D 11-D 0+11)+2*(v+1)+3)+((2*(D 4-D 0+4)+2*(q+1)+3)+((2*(D 5-D 0+5)+2*a+3)+((2*(D 5-D 0+5)+2*(a+1)+3)+t))),?_,?_⟩
        · have p1:=op_price D 11 (v+1) P di (by decide) (by omega)
          have p2:=op_price D 4 (q+1) P dq (by decide) (by omega)
          have p3:=op_price D 5 a P da (by decide) (by omega)
          have p4:=op_price D 5 (a+1) P da (by decide) (by omega)
          rw [show min (v+1) (q+1)=min v q+1 by omega]
          simp only [Nat.add_mul,Nat.mul_add] at price ⊢
          omega
        · rw [if_pos (by omega : v+1 ≤ q+1)]
          rw [show a+2+2*v=a+2*(v+1) by omega,show q-v=q+1-(v+1) by omega] at path
          exact path
      · rw [if_neg success] at tail
        have path:=one.append (two.append (three.append (four.append tail)))
        refine ⟨(2*(D 11-D 0+11)+2*(v+1)+3)+((2*(D 4-D 0+4)+2*(q+1)+3)+((2*(D 5-D 0+5)+2*a+3)+((2*(D 5-D 0+5)+2*(a+1)+3)+t))),?_,?_⟩
        · have p1:=op_price D 11 (v+1) P di (by decide) (by omega)
          have p2:=op_price D 4 (q+1) P dq (by decide) (by omega)
          have p3:=op_price D 5 a P da (by decide) (by omega)
          have p4:=op_price D 5 (a+1) P da (by decide) (by omega)
          rw [show min (v+1) (q+1)=min v q+1 by omega]
          simp only [Nat.add_mul,Nat.mul_add] at price ⊢
          omega
        · rw [if_neg (by omega : ¬v+1 ≤ q+1)]
          rw [show a+2+2*q=a+2*(q+1) by omega,show v-q-1=v+1-(q+1)-1 by omega] at path
          exact path
end NormalFinalClosure
