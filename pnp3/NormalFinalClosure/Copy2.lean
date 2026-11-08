import NormalFinalClosure.Support
namespace NormalFinalClosure
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
  for leaf in ["Node","Path","Grid","Unary","DecRows","IncRows","put","keep","paint","clear_run","dec_zero","dec_positive","inc_success"] do
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
  for leaf in ["field","field_self","field_repeat","field_unary","field_other","field_grid","field_comm","field_dec","field_inc","mono","rise","blanks"] do
    let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.UnaryCopy 0) "PhysicalCallerClosure") leaf
    let some ci:=e.find? n | throwError "Missing unary support {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.UnaryCopy do throwError "Wrong owner"
    logInfo m!"copy-kernel-open|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
variable {M : UniformTM} {Safe : Fin M.stateCount → Prop}
private structure CopyRows (s d tmp : Nat) (start out : Fin M.stateCount) where
  restore : Fin M.stateCount
  id : Fin M.stateCount
  it : Fin M.stateCount
  ir : Fin M.stateCount
  source : DecRows (Safe:=Safe) s start restore id
  dest : IncRows (Safe:=Safe) d id it
  temp : IncRows (Safe:=Safe) tmp it start
  restoreDec : DecRows (Safe:=Safe) tmp restore out ir
  restoreInc : IncRows (Safe:=Safe) s ir restore
private def three (T : Nat → Option Bool) (D : Nat → Nat) (s d tmp a b c : Nat) :=
  field (field (field T D s a) D d b) D tmp c
private theorem three_grid {T D s d tmp a b c} (grid:Grid D T) (hs:s < 13) (hd:d < 13) (ht:tmp < 13) :
    Grid D (three T D s d tmp a b c) :=
  field_grid (field_grid (field_grid grid s a hs) d b hd) tmp c ht
private theorem three_s {T D s d tmp a b c} (grid:Grid D T) (hs:s < 13) (hd:d < 13) (ht:tmp < 13)
    (sd:s≠d) (s5:s≠tmp) : Unary D (three T D s d tmp a b c) s a :=
  field_other (field_grid (field_grid grid s a hs) d b hd) ht hs s5.symm
    (field_other (field_grid grid s a hs) hd hs sd.symm (field_unary T D s a))
private theorem three_d {T D s d tmp a b c} (grid:Grid D T) (hs:s < 13) (hd:d < 13) (ht:tmp < 13)
    (d5:d≠tmp) : Unary D (three T D s d tmp a b c) d b :=
  field_other (field_grid (field_grid grid s a hs) d b hd) ht hd d5.symm
    (field_unary (field T D s a) D d b)
private theorem three_5 (T D s d tmp a b c) : Unary D (three T D s d tmp a b c) tmp c :=
  field_unary _ D tmp c
private theorem three_write_s {T D s d tmp a b c v} (grid:Grid D T) (hs:s < 13) (hd:d < 13) (ht:tmp < 13)
    (sd:s≠d) (s5:s≠tmp) :
    field (three T D s d tmp a b c) D s v=three T D s d tmp v b c := by
  dsimp only [three]
  rw [field_comm (field_grid (field_grid grid s a hs) d b hd) ht hs s5.symm,
    field_comm (field_grid grid s a hs) hd hs sd.symm,field_repeat]
private theorem three_write_d {T D s d tmp a b c v} (grid:Grid D T) (hs:s < 13) (hd:d < 13) (ht:tmp < 13)
    (d5:d≠tmp) :
    field (three T D s d tmp a b c) D d v=three T D s d tmp a v c := by
  dsimp only [three]
  rw [field_comm (field_grid (field_grid grid s a hs) d b hd) ht hd d5.symm,field_repeat]
private theorem three_write_5 (T D s d tmp a b c v) :
    field (three T D s d tmp a b c) D tmp v=three T D s d tmp a b v := by
  exact field_repeat _ _ _ _ _
private theorem op_price (D : Nat → Nat) (j v P : Nat)
    (dj:D j ≤ P) (hj:j ≤ 12) (hv:v ≤ P) :
    2*(D j-D 0+j)+2*v+3 ≤ 32*(P+1) := by omega
private theorem copy_restore {D T s d tmp w P start out} (grid:Grid D T)
    (hs:s < 13) (hd:d < 13) (ht:tmp < 13) (sd:s≠d) (s5:s≠tmp) (_d5:d≠tmp)
    (room:D 13 ≤ P) (width:∀ j,j=s ∨ j=d ∨ j=tmp → D (j+1)=D j+w+1)
    (code:CopyRows (Safe:=Safe) s d tmp start out) (b q a : Nat) (cap:a+q ≤ w) :
    ∃ t,t ≤ (q+1)*(128*(P+1)) ∧ Path M Safe P t
      (node code.restore (D 0) (three T D s d tmp a b q))
      (node out (D 0) (three T D s d tmp (a+q) b 0)) := by
  have sw:=width s (Or.inl rfl)
  have tw:=width tmp (Or.inr (Or.inr rfl))
  have wP:w ≤ P:=by
    have h:=mono grid (s+1) 13 (by omega) le_rfl
    omega
  induction q generalizing a with
  | zero =>
    have g:=three_grid (tmp:=tmp) (a:=a) (b:=b) (c:=0) grid hs hd ht
    have dec:=dec_zero g (ht : tmp < 13) room tw (three_5 T D s d tmp a b 0) code.restoreDec
    have path:=dec
    refine ⟨2*(D tmp-D 0+tmp)+3,?_,?_⟩
    · have pr:=op_price D tmp 0 P (le_trans (mono grid tmp 13 (by omega) le_rfl) room) (by omega) (by omega)
      omega
    · simpa only [Nat.add_zero] using path
  | succ q ih =>
    have g:=three_grid (tmp:=tmp) (a:=a) (b:=b) (c:=q+1) grid hs hd ht
    have dec:=dec_positive g (ht : tmp < 13) room tw (three_5 T D s d tmp a b (q+1)) (by omega) (by omega) code.restoreDec
    rw [field_dec g ht tw (three_5 T D s d tmp a b (q+1)) (by omega) (by omega),three_write_5,
      show q+1-1=q by omega] at dec
    have g1:=three_grid (tmp:=tmp) (a:=a) (b:=b) (c:=q) grid hs hd ht
    have inc:=inc_success g1 hs room sw (three_s grid hs hd ht sd s5) (by omega) code.restoreInc
    rw [field_inc g1 hs sw (three_s grid hs hd ht sd s5) (by omega),three_write_s grid hs hd ht sd s5] at inc
    obtain ⟨t,price,tail⟩:=ih (a+1) (by omega)
    have path:=dec.append (inc.append tail)
    refine ⟨(2*(D tmp-D 0+tmp)+2*(q+1)+3)+((2*(D s-D 0+s)+2*a+3)+t),?_,?_⟩
    · have p1:=op_price D tmp (q+1) P (le_trans (mono grid tmp 13 (by omega) le_rfl) room) (by omega) (by omega)
      have p2:=op_price D s a P (le_trans (mono grid s 13 (by omega) le_rfl) room) (by omega) (by omega)
      simp only [Nat.add_mul] at price ⊢
      omega
    · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using path
private theorem copy_drain {D T s d tmp w P start out} (grid:Grid D T)
    (hs:s < 13) (hd:d < 13) (ht:tmp < 13) (sd:s≠d) (s5:s≠tmp) (d5:d≠tmp)
    (room:D 13 ≤ P) (width:∀ j,j=s ∨ j=d ∨ j=tmp → D (j+1)=D j+w+1)
    (code:CopyRows (Safe:=Safe) s d tmp start out) (v a : Nat) (cap:v+a ≤ w) :
    ∃ t,t ≤ (v+1)*(128*(P+1))+(v+a+1)*(128*(P+1)) ∧ Path M Safe P t
      (node start (D 0) (three T D s d tmp v a a))
      (node out (D 0) (three T D s d tmp (v+a) (v+a) 0)) := by
  have sw:=width s (Or.inl rfl)
  have dw:=width d (Or.inr (Or.inl rfl))
  have tw:=width tmp (Or.inr (Or.inr rfl))
  have wP:w ≤ P:=by have h:=mono grid (s+1) 13 (by omega) le_rfl;omega
  induction v generalizing a with
  | zero =>
    have g:=three_grid (tmp:=tmp) (a:=0) (b:=a) (c:=a) grid hs hd ht
    have dec:=dec_zero g hs room sw (three_s grid hs hd ht sd s5) code.source
    obtain ⟨t,price,tail⟩:=copy_restore grid hs hd ht sd s5 d5 room width code a a 0 (by omega)
    have path:=dec.append tail
    refine ⟨(2*(D s-D 0+s)+3)+t,?_,?_⟩
    · have pr:=op_price D s 0 P (le_trans (mono grid s 13 (by omega) le_rfl) room) (by omega) (by omega)
      simp only [Nat.zero_add,one_mul] at price ⊢
      omega
    · simpa only [Nat.zero_add] using path
  | succ v ih =>
    have g:=three_grid (tmp:=tmp) (a:=v+1) (b:=a) (c:=a) grid hs hd ht
    have dec:=dec_positive g hs room sw (three_s grid hs hd ht sd s5) (by omega) (by omega) code.source
    rw [field_dec g hs sw (three_s grid hs hd ht sd s5) (by omega) (by omega),three_write_s grid hs hd ht sd s5,
      show v+1-1=v by omega] at dec
    have g1:=three_grid (tmp:=tmp) (a:=v) (b:=a) (c:=a) grid hs hd ht
    have inc1:=inc_success g1 hd room dw (three_d grid hs hd ht d5) (by omega) code.dest
    rw [field_inc g1 hd dw (three_d grid hs hd ht d5) (by omega),three_write_d grid hs hd ht d5] at inc1
    have g2:=three_grid (tmp:=tmp) (a:=v) (b:=a+1) (c:=a) grid hs hd ht
    have inc2:=inc_success g2 (ht : tmp < 13) room tw (three_5 T D s d tmp v (a+1) a) (by omega) code.temp
    rw [field_inc g2 ht tw (three_5 T D s d tmp v (a+1) a) (by omega),three_write_5] at inc2
    obtain ⟨t,price,tail⟩:=ih (a+1) (by omega)
    have path:=dec.append (inc1.append (inc2.append tail))
    refine ⟨(2*(D s-D 0+s)+2*(v+1)+3)+((2*(D d-D 0+d)+2*a+3)+((2*(D tmp-D 0+tmp)+2*a+3)+t)),?_,?_⟩
    · have p1:=op_price D s (v+1) P (le_trans (mono grid s 13 (by omega) le_rfl) room) (by omega) (by omega)
      have p2:=op_price D d a P (le_trans (mono grid d 13 (by omega) le_rfl) room) (by omega) (by omega)
      have p3:=op_price D tmp a P (le_trans (mono grid tmp 13 (by omega) le_rfl) room) (by omega) (by omega)
      have eq:v+(a+1)+1=(v+1)+a+1:=by omega
      rw [eq] at price
      simp only [Nat.add_mul] at price ⊢
      omega
    · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using path
private theorem copy_run {D T s d tmp w v P start out} (grid:Grid D T)
    (hs:s < 13) (hd:d < 13) (ht:tmp < 13) (sd:s≠d) (s5:s≠tmp) (d5:d≠tmp)
    (room:D 13 ≤ P) (width:∀ j,j=s ∨ j=d ∨ j=tmp → D (j+1)=D j+w+1)
    (source:Unary D T s v) (dest0:Unary D T d 0) (temp0:Unary D T tmp 0) (cap:v ≤ w)
    (code:CopyRows (Safe:=Safe) s d tmp start out) :
    ∃ t,t ≤ 256*(v+1)*(P+1) ∧ Path M Safe P t
      (node start (D 0) T) (node out (D 0) (field T D d v)) := by
  obtain ⟨t,price,path⟩:=copy_drain grid hs hd ht sd s5 d5 room width code v 0 (by omega)
  have before:three T D s d tmp v 0 0=T:=by
    dsimp only [three];rw [field_self source,field_self dest0,field_self temp0]
  have after:three T D s d tmp v v 0=field T D d v:=by
    dsimp only [three];rw [field_self source]
    exact field_self (field_other grid hd ht d5 temp0)
  simp only [Nat.add_zero,before,after] at path
  refine ⟨t,?_,path⟩
  have eq:(v+1)*(128*(P+1))+(v+1)*(128*(P+1))=256*(v+1)*(P+1):=by ring
  simpa only [Nat.add_zero,eq] using price
private structure TransferRows (s d : Nat) (start out : Fin M.stateCount) where
  pos : Fin M.stateCount
  source : DecRows (Safe:=Safe) s start out pos
  dest : IncRows (Safe:=Safe) d pos start
private theorem two_grid {D T s d a b} (grid:Grid D T) (hs:s < 13) (hd:d < 13) :
    Grid D (field (field T D s a) D d b) := field_grid (field_grid grid s a hs) d b hd
private theorem two_source {D T s d a b} (grid:Grid D T) (hs:s < 13) (hd:d < 13) (sd:s≠d) :
    Unary D (field (field T D s a) D d b) s a :=
  field_other (field_grid grid s a hs) hd hs sd.symm (field_unary T D s a)
private theorem two_write_s {D T s d a b v} (grid:Grid D T) (hs:s < 13) (hd:d < 13) (sd:s≠d) :
    field (field (field T D s a) D d b) D s v=field (field T D s v) D d b := by
  rw [field_comm (field_grid grid s a hs) hd hs sd.symm,field_repeat]
private theorem transfer_loop {D T s d w P start out} (grid:Grid D T)
    (hs:s < 13) (hd:d < 13) (sd:s≠d) (room:D 13 ≤ P)
    (sw:D (s+1)=D s+w+1) (dw:D (d+1)=D d+w+1)
    (code:TransferRows (Safe:=Safe) s d start out) (v a : Nat) (cap:v+a ≤ w) :
    ∃ t,t ≤ (v+1)*(128*(P+1)) ∧ Path M Safe P t
      (node start (D 0) (field (field T D s v) D d a))
      (node out (D 0) (field (field T D s 0) D d (a+v))) := by
  have wP:w ≤ P:=by have bound:=mono grid (s+1) 13 (by omega) le_rfl;omega
  induction v generalizing a with
  | zero=>
    have g:=two_grid (a:=0) (b:=a) grid hs hd
    have step:=dec_zero g hs room sw (two_source grid hs hd sd) code.source
    refine ⟨2*(D s-D 0+s)+3,?_,?_⟩
    · have pr:=op_price D s 0 P (le_trans (mono grid s 13 (by omega) le_rfl) room) (by omega) (by omega)
      simp only [Nat.zero_add,one_mul]
      omega
    · simpa only [Nat.add_zero] using step
  | succ v ih=>
    have g:=two_grid (a:=v+1) (b:=a) grid hs hd
    have dec:=dec_positive g hs room sw (two_source grid hs hd sd) (by omega) (by omega) code.source
    rw [field_dec g hs sw (two_source grid hs hd sd) (by omega) (by omega),two_write_s grid hs hd sd,
      show v+1-1=v by omega] at dec
    have g1:=two_grid (a:=v) (b:=a) grid hs hd
    have dest:=field_unary (field T D s v) D d a
    have inc:=inc_success g1 hd room dw dest (by omega) code.dest
    rw [field_inc g1 hd dw dest (by omega),field_repeat] at inc
    obtain ⟨t,price,tail⟩:=ih (a+1) (by omega)
    have path:=dec.append (inc.append tail)
    refine ⟨(2*(D s-D 0+s)+2*(v+1)+3)+((2*(D d-D 0+d)+2*a+3)+t),?_,?_⟩
    · have p1:=op_price D s (v+1) P (le_trans (mono grid s 13 (by omega) le_rfl) room) (by omega) (by omega)
      have p2:=op_price D d a P (le_trans (mono grid d 13 (by omega) le_rfl) room) (by omega) (by omega)
      simp only [Nat.add_mul] at price ⊢
      omega
    · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using path
private theorem transfer_run {D T s d w v a P start out} (grid:Grid D T)
    (hs:s < 13) (hd:d < 13) (sd:s≠d) (room:D 13 ≤ P)
    (sw:D (s+1)=D s+w+1) (dw:D (d+1)=D d+w+1)
    (source:Unary D T s v) (dest:Unary D T d a) (cap:v+a ≤ w)
    (code:TransferRows (Safe:=Safe) s d start out) :
    ∃ t,t ≤ 128*(v+1)*(P+1) ∧ Path M Safe P t
      (node start (D 0) T) (node out (D 0) (field (field T D s 0) D d (a+v))) := by
  obtain ⟨t,price,path⟩:=transfer_loop grid hs hd sd room sw dw code v a cap
  rw [field_self source,field_self dest] at path
  exact ⟨t,by nlinarith,path⟩
private theorem paint_field {D T} (grid:Grid D T) (j : Nat) (hj:j < 13) (b : Bool) :
    paint T (D j+1) (D (j+1)-D j-1) b=
      field T D j (if b then D (j+1)-D j-1 else 0) := by
  have step:=rise grid j hj
  funext i
  have intervals:(D j+1 ≤ i ∧ i < D j+1+(D (j+1)-D j-1)) ↔ (D j < i ∧ i < D (j+1)) := by omega
  by_cases inside:D j < i ∧ i < D (j+1)
  · have off0:¬i-D j ≤ 0:=by omega
    have offMax:i-D j ≤ D (j+1)-D j-1:=by omega
    simp only [paint,field,intervals,if_pos inside]
    cases b
    · change some false=some (decide (i-D j ≤ 0))
      rw [decide_eq_false off0]
    · change some true=some (decide (i-D j ≤ D (j+1)-D j-1))
      rw [decide_eq_true offMax]
  · simp only [paint,field,intervals,if_neg inside]
end NormalFinalClosure
