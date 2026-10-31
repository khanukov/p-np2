import PhysicalCallerClosure.UnaryCopy
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
private def support (leaf kind : String) : TacticM Unit := do
  let e←getEnv
  let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Engine 0) "PhysicalCallerClosure")
  let some ci:=e.find? n | throwError "Missing Engine term {n}"
  let actual:=match ci with | .defnInfo _=>"definition" | .thmInfo _=>"theorem" | .inductInfo _=>"inductive" | .ctorInfo _=>"constructor" | _=>"other"
  unless actual==kind do throwError "Wrong Engine kind: {n}"
  let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
  unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
  unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Engine do throwError "Wrong owner"
  logInfo m!"copy-support|{actual}|{n}|{ci.type}"
  closeMainGoal `support (mkConst n (ci.levelParams.map Level.param))
run_cmd do
  let e←getEnv
  for leaf in ["Node","Path","Grid","Unary","DecRows","IncRows","put","keep","dec_zero","dec_positive","inc_success"] do
    let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Engine 0) "PhysicalCallerClosure")
    let some ci:=e.find? n | throwError "Missing Engine support {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Engine do throwError "Wrong owner"
    logInfo m!"copy-open|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac support "Node.mk" "constructor"
run_cmd do
  let e←getEnv
  for leaf in ["field","field_self","field_repeat","field_unary","field_other","field_grid","field_comm","field_dec","field_inc","mono","blanks"] do
    let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.UnaryCopy 0) "PhysicalCallerClosure") leaf
    let some ci:=e.find? n | throwError "Missing unary support {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.UnaryCopy do throwError "Wrong owner"
    logInfo m!"copy-kernel-open|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
variable {M : UniformTM} {Safe : Fin M.stateCount → Prop}
private structure CopyRows (s d : Nat) (start out : Fin M.stateCount) where
  rd : Fin M.stateCount
  restore : Fin M.stateCount
  rr : Fin M.stateCount
  id : Fin M.stateCount
  it : Fin M.stateCount
  ir : Fin M.stateCount
  safeStart : Safe start
  safeRestore : Safe restore
  enter : M.step start none=(rd,none,.stay)
  source : DecRows (Safe:=Safe) s rd restore id
  dest : IncRows (Safe:=Safe) d id it
  temp : IncRows (Safe:=Safe) 5 it start
  returnEnter : M.step restore none=(rr,none,.stay)
  restoreDec : DecRows (Safe:=Safe) 5 rr out ir
  restoreInc : IncRows (Safe:=Safe) s ir restore
private def three (T : Nat → Option Bool) (D : Nat → Nat) (s d a b c : Nat) :=
  field (field (field T D s a) D d b) D 5 c
private theorem three_grid {T D s d a b c} (grid:Grid D T) (hs:s < 13) (hd:d < 13) :
    Grid D (three T D s d a b c) :=
  field_grid (field_grid (field_grid grid s a hs) d b hd) 5 c (by decide)
private theorem three_s {T D s d a b c} (grid:Grid D T) (hs:s < 13) (hd:d < 13)
    (sd:s≠d) (s5:s≠5) : Unary D (three T D s d a b c) s a :=
  field_other (field_grid (field_grid grid s a hs) d b hd) (by decide) hs s5.symm
    (field_other (field_grid grid s a hs) hd hs sd.symm (field_unary T D s a))
private theorem three_d {T D s d a b c} (grid:Grid D T) (hs:s < 13) (hd:d < 13)
    (d5:d≠5) : Unary D (three T D s d a b c) d b :=
  field_other (field_grid (field_grid grid s a hs) d b hd) (by decide) hd d5.symm
    (field_unary (field T D s a) D d b)
private theorem three_5 (T D s d a b c) : Unary D (three T D s d a b c) 5 c :=
  field_unary _ D 5 c
private theorem three_write_s {T D s d a b c v} (grid:Grid D T) (hs:s < 13) (hd:d < 13)
    (sd:s≠d) (s5:s≠5) :
    field (three T D s d a b c) D s v=three T D s d v b c := by
  dsimp only [three]
  rw [field_comm (field_grid (field_grid grid s a hs) d b hd) (by decide) hs s5.symm,
    field_comm (field_grid grid s a hs) hd hs sd.symm,field_repeat]
private theorem three_write_d {T D s d a b c v} (grid:Grid D T) (hs:s < 13) (hd:d < 13)
    (d5:d≠5) :
    field (three T D s d a b c) D d v=three T D s d a v c := by
  dsimp only [three]
  rw [field_comm (field_grid (field_grid grid s a hs) d b hd) (by decide) hd d5.symm,field_repeat]
private theorem three_write_5 (T D s d a b c v) :
    field (three T D s d a b c) D 5 v=three T D s d a b v := by
  exact field_repeat _ _ _ _ _
private theorem op_price (D : Nat → Nat) (j v P : Nat)
    (dj:D j ≤ P) (hj:j ≤ 12) (hv:v ≤ P) :
    2*(D j-D 0+j)+2*v+3 ≤ 32*(P+1) := by omega
private theorem copy_restore {D T s d w P start out} (grid:Grid D T)
    (hs:s < 13) (hd:d < 13) (sd:s≠d) (s5:s≠5) (_d5:d≠5)
    (room:D 13 ≤ P) (width:∀ j,j=s ∨ j=d ∨ j=5 → D (j+1)=D j+w+1)
    (code:CopyRows (Safe:=Safe) s d start out) (b q a : Nat) (cap:a+q ≤ w) :
    ∃ t,t ≤ (q+1)*(128*(P+1)) ∧ Path M Safe P t
      (node code.restore (D 0) (three T D s d a b q))
      (node out (D 0) (three T D s d (a+q) b 0)) := by
  have d0:D 0 ≤ P:=le_trans (mono grid 0 13 (by omega) le_rfl) room
  have sw:=width s (Or.inl rfl)
  have tw:=width 5 (Or.inr (Or.inr rfl))
  have wP:w ≤ P:=by
    have h:=mono grid (s+1) 13 (by omega) le_rfl
    omega
  induction q generalizing a with
  | zero =>
    have g:=three_grid (a:=a) (b:=b) (c:=0) grid hs hd
    have first:=keep code.restore code.rr (D 0) (D 0) (three T D s d a b 0) .stay
      d0 d0 code.safeRestore (by rw [blanks g 0 (by omega)];exact code.returnEnter) rfl
    have dec:=dec_zero g (by decide : 5 < 13) room tw (three_5 T D s d a b 0) code.restoreDec
    have path:=first.append dec
    refine ⟨1+(2*(D 5-D 0+5)+3),?_,?_⟩
    · have pr:=op_price D 5 0 P (le_trans (mono grid 5 13 (by omega) le_rfl) room) (by omega) (by omega)
      omega
    · simpa only [Nat.add_zero] using path
  | succ q ih =>
    have g:=three_grid (a:=a) (b:=b) (c:=q+1) grid hs hd
    have first:=keep code.restore code.rr (D 0) (D 0) (three T D s d a b (q+1)) .stay
      d0 d0 code.safeRestore (by rw [blanks g 0 (by omega)];exact code.returnEnter) rfl
    have dec:=dec_positive g (by decide : 5 < 13) room tw (three_5 T D s d a b (q+1)) (by omega) (by omega) code.restoreDec
    rw [field_dec g (by decide) tw (three_5 T D s d a b (q+1)) (by omega) (by omega),three_write_5,
      show q+1-1=q by omega] at dec
    have g1:=three_grid (a:=a) (b:=b) (c:=q) grid hs hd
    have inc:=inc_success g1 hs room sw (three_s grid hs hd sd s5) (by omega) code.restoreInc
    rw [field_inc g1 hs sw (three_s grid hs hd sd s5) (by omega),three_write_s grid hs hd sd s5] at inc
    obtain ⟨t,price,tail⟩:=ih (a+1) (by omega)
    have path:=first.append (dec.append (inc.append tail))
    refine ⟨1+((2*(D 5-D 0+5)+2*(q+1)+3)+((2*(D s-D 0+s)+2*a+3)+t)),?_,?_⟩
    · have p1:=op_price D 5 (q+1) P (le_trans (mono grid 5 13 (by omega) le_rfl) room) (by omega) (by omega)
      have p2:=op_price D s a P (le_trans (mono grid s 13 (by omega) le_rfl) room) (by omega) (by omega)
      simp only [Nat.add_mul] at price ⊢
      omega
    · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using path
private theorem copy_drain {D T s d w P start out} (grid:Grid D T)
    (hs:s < 13) (hd:d < 13) (sd:s≠d) (s5:s≠5) (d5:d≠5)
    (room:D 13 ≤ P) (width:∀ j,j=s ∨ j=d ∨ j=5 → D (j+1)=D j+w+1)
    (code:CopyRows (Safe:=Safe) s d start out) (v a : Nat) (cap:v+a ≤ w) :
    ∃ t,t ≤ (v+1)*(128*(P+1))+(v+a+1)*(128*(P+1)) ∧ Path M Safe P t
      (node start (D 0) (three T D s d v a a))
      (node out (D 0) (three T D s d (v+a) (v+a) 0)) := by
  have d0:D 0 ≤ P:=le_trans (mono grid 0 13 (by omega) le_rfl) room
  have sw:=width s (Or.inl rfl)
  have dw:=width d (Or.inr (Or.inl rfl))
  have tw:=width 5 (Or.inr (Or.inr rfl))
  have wP:w ≤ P:=by have h:=mono grid (s+1) 13 (by omega) le_rfl;omega
  induction v generalizing a with
  | zero =>
    have g:=three_grid (a:=0) (b:=a) (c:=a) grid hs hd
    have first:=keep start code.rd (D 0) (D 0) (three T D s d 0 a a) .stay
      d0 d0 code.safeStart (by rw [blanks g 0 (by omega)];exact code.enter) rfl
    have dec:=dec_zero g hs room sw (three_s grid hs hd sd s5) code.source
    obtain ⟨t,price,tail⟩:=copy_restore grid hs hd sd s5 d5 room width code a a 0 (by omega)
    have path:=first.append (dec.append tail)
    refine ⟨1+((2*(D s-D 0+s)+3)+t),?_,?_⟩
    · have pr:=op_price D s 0 P (le_trans (mono grid s 13 (by omega) le_rfl) room) (by omega) (by omega)
      simp only [Nat.zero_add,one_mul] at price ⊢
      omega
    · simpa only [Nat.zero_add] using path
  | succ v ih =>
    have g:=three_grid (a:=v+1) (b:=a) (c:=a) grid hs hd
    have first:=keep start code.rd (D 0) (D 0) (three T D s d (v+1) a a) .stay
      d0 d0 code.safeStart (by rw [blanks g 0 (by omega)];exact code.enter) rfl
    have dec:=dec_positive g hs room sw (three_s grid hs hd sd s5) (by omega) (by omega) code.source
    rw [field_dec g hs sw (three_s grid hs hd sd s5) (by omega) (by omega),three_write_s grid hs hd sd s5,
      show v+1-1=v by omega] at dec
    have g1:=three_grid (a:=v) (b:=a) (c:=a) grid hs hd
    have inc1:=inc_success g1 hd room dw (three_d grid hs hd d5) (by omega) code.dest
    rw [field_inc g1 hd dw (three_d grid hs hd d5) (by omega),three_write_d grid hs hd d5] at inc1
    have g2:=three_grid (a:=v) (b:=a+1) (c:=a) grid hs hd
    have inc2:=inc_success g2 (by decide : 5 < 13) room tw (three_5 T D s d v (a+1) a) (by omega) code.temp
    rw [field_inc g2 (by decide) tw (three_5 T D s d v (a+1) a) (by omega),three_write_5] at inc2
    obtain ⟨t,price,tail⟩:=ih (a+1) (by omega)
    have path:=first.append (dec.append (inc1.append (inc2.append tail)))
    refine ⟨1+((2*(D s-D 0+s)+2*(v+1)+3)+((2*(D d-D 0+d)+2*a+3)+((2*(D 5-D 0+5)+2*a+3)+t))),?_,?_⟩
    · have p1:=op_price D s (v+1) P (le_trans (mono grid s 13 (by omega) le_rfl) room) (by omega) (by omega)
      have p2:=op_price D d a P (le_trans (mono grid d 13 (by omega) le_rfl) room) (by omega) (by omega)
      have p3:=op_price D 5 a P (le_trans (mono grid 5 13 (by omega) le_rfl) room) (by omega) (by omega)
      have eq:v+(a+1)+1=(v+1)+a+1:=by omega
      rw [eq] at price
      simp only [Nat.add_mul] at price ⊢
      omega
    · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using path
private theorem copy_run {D T s d w v P start out} (grid:Grid D T)
    (hs:s < 13) (hd:d < 13) (sd:s≠d) (s5:s≠5) (d5:d≠5)
    (room:D 13 ≤ P) (width:∀ j,j=s ∨ j=d ∨ j=5 → D (j+1)=D j+w+1)
    (source:Unary D T s v) (dest0:Unary D T d 0) (temp0:Unary D T 5 0) (cap:v ≤ w)
    (code:CopyRows (Safe:=Safe) s d start out) :
    ∃ t,t ≤ 256*(v+1)*(P+1) ∧ Path M Safe P t
      (node start (D 0) T) (node out (D 0) (field T D d v)) := by
  obtain ⟨t,price,path⟩:=copy_drain grid hs hd sd s5 d5 room width code v 0 (by omega)
  have before:three T D s d v 0 0=T:=by
    dsimp only [three];rw [field_self source,field_self dest0,field_self temp0]
  have after:three T D s d v v 0=field T D d v:=by
    dsimp only [three];rw [field_self source]
    exact field_self (field_other grid hd (by decide) d5 temp0)
  simp only [Nat.add_zero,before,after] at path
  refine ⟨t,?_,path⟩
  have eq:(v+1)*(128*(P+1))+(v+1)*(128*(P+1))=256*(v+1)*(P+1):=by ring
  simpa only [Nat.add_zero,eq] using price
end PhysicalCallerClosure
