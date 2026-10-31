import NormalFinalClosure.MacroCertificates2
import NormalFinalClosure.Copy2
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
    (`PhysicalCallerClosure.Engine,`PhysicalCallerClosure,["Node","Path","Grid","Unary","DecRows","IncRows","keep","dec_zero","dec_positive","inc_success"]),
    (`PhysicalCallerClosure.UnaryCopy,`PhysicalCallerClosure,["field","field_grid","field_unary","field_other","field_dec","field_inc","field_self","field_comm","field_repeat","mono"]),
    (`NormalFinalClosure.Copy2,`NormalFinalClosure,["three","three_grid","three_s","three_d","three_5","three_write_s","three_write_d","three_write_5","op_price","TransferRows","transfer_run"]),
    (`NormalFinalClosure.Rows2Code,`NormalFinalClosure,["ns2","Safe2"])] do
    for leaf in leaves do
      let n:=Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns) leaf
      let some ci:=e.find? n | throwError "Missing unique actual halving API {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing halving API owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong halving API owner"
      let kind:=match ci with|.defnInfo _=>"definition"|.thmInfo _=>"theorem"|.inductInfo _=>"inductive"|_=>"other"
      unless kind != "other" do throwError "Unexpected halving API kind"
      logInfo m!"halving-exact-interface|{n}|{kind}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private def select (owner : Name) (leaf kind : String) : TacticM Unit := do
  let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num (Name.append `_private owner) 0) "NormalFinalClosure")
  let e←getEnv
  let some ci:=e.find? n | throwError "Missing exact halving term {n}"
  let actual:=match ci with|.defnInfo _=>"definition"|.thmInfo _=>"theorem"|.ctorInfo _=>"constructor"|_=>"other"
  unless actual==kind do throwError "Wrong halving term kind"
  let some i:=e.getModuleIdxFor? n | throwError "Missing halving term owner"
  unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong halving term owner"
  logInfo m!"halving-typed-selection|{n}|{kind}|{ci.type}"
  closeMainGoal `select (mkConst n (ci.levelParams.map Level.param))
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac do
    let owner:=`PhysicalCallerClosure.Engine
    let n:=Name.str (Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") "Node") "mk"
    let e←getEnv
    let some (.ctorInfo ci):=e.find? n | throwError "Missing native Node constructor"
    let some i:=e.getModuleIdxFor? n | throwError "Missing Node owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong Node owner"
    logInfo m!"halving-typed-node|{n}|{ci.type}"
    closeMainGoal `node (mkConst n (ci.levelParams.map Level.param))
variable {M : UniformTM} {Safe : Fin M.stateCount → Prop}
private abbrev I (T : Nat → Option Bool) (D : Nat → Nat) (v a c : Nat) := three T D 4 5 6 v a c
private theorem ig {T D v a c} (g:Grid D T) : Grid D (I T D v a c) :=
  three_grid g (by decide) (by decide) (by decide)
private theorem iv {T D v a c} (g:Grid D T) : Unary D (I T D v a c) 4 v :=
  three_s g (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem ia {T D v a c} (g:Grid D T) : Unary D (I T D v a c) 5 a :=
  three_d g (by decide) (by decide) (by decide) (by decide)
private theorem ic (T D v a c) : Unary D (I T D v a c) 6 c := three_5 T D 4 5 6 v a c
private theorem iwv {T D v a c x} (g:Grid D T) : field (I T D v a c) D 4 x=I T D x a c :=
  three_write_s g (by decide) (by decide) (by decide) (by decide) (by decide)
private theorem iwa {T D v a c x} (g:Grid D T) : field (I T D v a c) D 5 x=I T D v x c :=
  three_write_d g (by decide) (by decide) (by decide) (by decide)
private theorem iwc (T D v a c x) : field (I T D v a c) D 6 x=I T D v a x := three_write_5 T D 4 5 6 v a c x
/-- A complete pair-drain loop. Each pair performs two actual decrements and an
actual increment, with all native scans priced by the LEFT-writing ABI. -/
private theorem pair_loop {D T w P start second add out}
    (grid:Grid D T) (room:D 13 ≤ P)
    (sw:D 5=D 4+w+1) (dw:D 6=D 5+w+1)
    (first:DecRows (M:=M) (Safe:=Safe) 4 start out second)
    (next:DecRows (M:=M) (Safe:=Safe) 4 second out add)
    (inc:IncRows (M:=M) (Safe:=Safe) 5 add start) (v a c : Nat)
    (vr:v ≤ w) (cap:a+v/2 ≤ w) :
    ∃ t,t ≤ 128*(v+1)*(P+1) ∧ Path M Safe P t
      (node start (D 0) (I T D v a c))
      (node out (D 0) (I T D 0 (a+v/2) c)) := by
  have wP:w ≤ P:=by have h:=mono grid 5 13 (by decide) le_rfl;omega
  have d4:D 4 ≤ P:=(mono grid 4 13 (by decide) le_rfl).trans room
  have d5:D 5 ≤ P:=(mono grid 5 13 (by decide) le_rfl).trans room
  induction v using Nat.strong_induction_on generalizing a with
  | h v ih=>
    by_cases vz:v=0
    · subst v
      have step:=dec_zero (ig (v:=0) (a:=a) (c:=c) grid) (by decide) room sw (iv grid) first
      refine ⟨2*(D 4-D 0+4)+3,?_,?_⟩
      · have price:=op_price D 4 0 P d4 (by decide) (by omega)
        simp only [Nat.zero_add];omega
      · simpa only [Nat.zero_div,Nat.add_zero] using step
    · have vp:0 < v:=by omega
      have g:=ig (v:=v) (a:=a) (c:=c) grid
      have one:=dec_positive g (by decide) room sw (iv grid) vp vr first
      rw [field_dec g (by decide) sw (iv grid) vp vr,iwv grid] at one
      by_cases v1:v=1
      · subst v
        have two:=dec_zero (ig (v:=0) (a:=a) (c:=c) grid) (by decide) room sw (iv grid) next
        have path:=one.append two
        refine ⟨(2*(D 4-D 0+4)+2+3)+(2*(D 4-D 0+4)+3),?_,?_⟩
        · have price:=op_price D 4 1 P d4 (by decide) (by omega);omega
        · simpa only [Nat.reduceDiv,Nat.add_zero] using path
      · have gt:1 < v:=by omega
        have g1:=ig (v:=v-1) (a:=a) (c:=c) grid
        have two:=dec_positive g1 (by decide) room sw (iv grid) (by omega) (by omega) next
        rw [field_dec g1 (by decide) sw (iv grid) (by omega) (by omega),iwv grid,
          show v-1-1=v-2 by omega] at two
        have g2:=ig (v:=v-2) (a:=a) (c:=c) grid
        have plus:=inc_success g2 (by decide) room dw (ia grid) (by omega) inc
        rw [field_inc g2 (by decide) dw (ia grid) (by omega),iwa grid] at plus
        have divEq:(v-2)/2+1=v/2:=by omega
        obtain ⟨t,ht,tail⟩:=ih (v-2) (by omega) (a+1) (by omega) (by omega)
        have path:=one.append (two.append (plus.append tail))
        refine ⟨(2*(D 4-D 0+4)+2*v+3)+((2*(D 4-D 0+4)+2*(v-1)+3)+((2*(D 5-D 0+5)+2*a+3)+t)),?_,?_⟩
        · have p1:=op_price D 4 v P d4 (by decide) (by omega)
          have p2:=op_price D 4 (v-1) P d4 (by decide) (by omega)
          have p3:=op_price D 5 a P d5 (by decide) (by omega)
          have eq:v-2+1=v-1:=by omega
          rw [eq] at ht
          have budget:128*(v+1)*(P+1)=128*(v-1)*(P+1)+256*(P+1):=by
            rw [show v+1=(v-1)+2 by omega];ring
          rw [budget]
          nlinarith only [ht,p1,p2,p3]
        · rw [show a+1+(v-2)/2=a+v/2 by omega] at path
          exact path
end NormalFinalClosure
