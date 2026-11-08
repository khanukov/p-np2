import FullBodyClosure.Copy
namespace FullBodyClosure
open Lean Elab Tactic in
private def checkedKernel (leaf : String) : TacticM Unit := do
  let env ← getEnv
  let name := (leaf.splitOn ".").foldl Lean.Name.str
    (Lean.Name.str (Lean.Name.num `_private.SerializedBodyCompletion.Kernel 0) "SerializedBodyCompletion")
  let some ci := env.find? name | throwError "Missing exact immutable declaration: {name}"
  let some owner := env.getModuleIdxFor? name | throwError "Missing immutable owner: {name}"
  unless owner.toNat < env.header.moduleNames.size do throwError "Owner index outside imported header"
  unless env.header.moduleNames[owner]! == `SerializedBodyCompletion.Kernel do
    throwError "Wrong immutable owner: {name}"
  logInfo m!"kernel-adapter|{name}|{ci.type}"
  closeMainGoal `checkedKernel (mkConst name (ci.levelParams.map Level.param))
private abbrev Node : Type := by run_tac checkedKernel "Node"
private abbrev Path : Nat → Nat → Node → Node → Prop := by run_tac checkedKernel "Path"
private abbrev Grid : (Nat → Nat) → (Nat → Option Bool) → Prop := by run_tac checkedKernel "Grid"
private abbrev Unary : (Nat → Nat) → (Nat → Option Bool) → Nat → Nat → Prop := by run_tac checkedKernel "Unary"
private abbrev DecRows : Nat → Fin 7500 → Fin 7500 → Fin 7500 → Prop := by run_tac checkedKernel "DecRows"
private abbrev IncRows : Nat → Fin 7500 → Fin 7500 → Prop := by run_tac checkedKernel "IncRows"
open Pnp3.Complexity.Uniform.V1
private abbrev node : Fin 7500 → Nat → (Nat → Option Bool) → Node := by run_tac checkedKernel "Node.mk"
private abbrev nodeHead : Node → Nat := by run_tac checkedKernel "Node.head"
private abbrev put : (Nat → Option Bool) → Nat → Option Bool → Nat → Option Bool := by run_tac checkedKernel "put"
private abbrev dest : Nat → Move → Nat := by run_tac checkedKernel "dest"
private theorem Path.append : ∀ {P t u c d e} (_h : Path P t c d) (_g : Path P u d e),
    Path P (t+u) c e := by run_tac checkedKernel "Path.append"
private theorem keep : ∀ {P : Nat} (s s' : Fin 7500) (h h' : Nat) (T : Nat → Option Bool) (m : Move) (_hb : h ≤ P) (_ha : h' ≤ P)
    (_safe : 4 ≤ s.val)
    (_row : SerializedBody.machine.step s (T h) = (s',T h,m)) (_hm : dest h m=h'),
    Path P 1 (node (s) (h) (T)) (node (s') (h') (T)) := by run_tac checkedKernel "keep"
private theorem dec_zero : ∀ {D T j w P start zero pos} (_grid : Grid D T)
    (_hj : j < 12) (_fit : D 12 ≤ P) (_len : D (j+1)=D j+w+1)
    (_unary : Unary D T j 0) (_code : DecRows j start zero pos),
    Path P (2*(D j-D 0+j)+3) (node (start) (D 0) (T)) (node (zero) (D 0) (T)) := by run_tac checkedKernel "dec_zero"
private theorem dec_positive : ∀ {D T j w v P start zero pos} (_grid : Grid D T)
    (_hj : j < 12) (_fit : D 12 ≤ P) (_len : D (j+1)=D j+w+1)
    (_unary : Unary D T j v) (_positive : 0 < v) (_small : v ≤ w)
    (_code : DecRows j start zero pos),
    Path P (2*(D j-D 0+j)+2*v+4) (node (start) (D 0) (T))
      (node (pos) (D 0) (put T (D j+v) (some false))) := by run_tac checkedKernel "dec_positive"
private theorem inc_success : ∀ {D T j w v P start out} (_grid : Grid D T)
    (_hj : j < 12) (_fit : D 12 ≤ P) (_len : D (j+1)=D j+w+1)
    (_unary : Unary D T j v) (_small : v < w) (_code : IncRows j start out),
    Path P (2*(D j-D 0+j)+2*v+4) (node (start) (D 0) (T))
      (node (out) (D 0) (put T (D j+v+1) (some true))) := by run_tac checkedKernel "inc_success"
private theorem grid_mono : ∀ {D T}, Grid D T → ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b := by run_tac checkedKernel "Grid.mono"
private theorem grid_blank : ∀ {D T}, Grid D T → ∀ j,j ≤ 12 → T (D j)=none := by run_tac checkedKernel "Grid.blank"
open Pnp3.Complexity.Uniform.V1
open Lean Elab Tactic in
private def checkedFrom (owner : Name) (leaf : String) : TacticM Unit := do
  let env ← getEnv
  let name:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num (Name.append `_private owner) 0) "FullBodyClosure")
  let some ci:=env.find? name | throwError "Missing exact declaration: {name}"
  let some mi:=env.getModuleIdxFor? name | throwError "Missing owner: {name}"
  unless mi.toNat < env.header.moduleNames.size do throwError "Owner index outside header"
  unless env.header.moduleNames[mi]! == owner do throwError "Wrong owner for {name}"
  logInfo m!"transfer-adapter|{owner}|{name}|{ci.type}"
  closeMainGoal `checkedFrom (mkConst name (ci.levelParams.map Level.param))
private abbrev counter : (Nat → Option Bool) → (Nat → Nat) → Nat → Nat → Nat → Option Bool := by run_tac checkedFrom `FullBodyClosure.Index "counter"
private theorem counter_grid : ∀ {D T},Grid D T → ∀ j v,j < 12 → Grid D (counter T D j v) := by run_tac checkedFrom `FullBodyClosure.Index "counter_grid"
private theorem counter_unary : ∀ T D j v,Unary D (counter T D j v) j v := by run_tac checkedFrom `FullBodyClosure.Index "counter_unary"
private theorem counter_down : ∀ T D j v w,D (j+1)=D j+w+1 → 0 < v → v≤w →
  put (counter T D j v) (D j+v) (some false)=counter T D j (v-1) := by run_tac checkedFrom `FullBodyClosure.Index "counter_down"
private theorem counter_up : ∀ T D j v w,D (j+1)=D j+w+1 → v < w →
  put (counter T D j v) (D j+v+1) (some true)=counter T D j (v+1) := by run_tac checkedFrom `FullBodyClosure.Index "counter_up"
private theorem counter_put_outside : ∀ T D j v h b,¬(D j < h ∧ h < D (j+1)) →
  put (counter T D j v) h b=counter (put T h b) D j v := by run_tac checkedFrom `FullBodyClosure.Index "counter_put_outside"
private theorem separate_fields : ∀ {D T j k i},Grid D T → j < 12 → k < 12 → j≠k → D j < i → i < D (j+1) →
  ¬(D k < i ∧ i < D (k+1)) := by run_tac checkedFrom `FullBodyClosure.Copy "separate_fields"
private theorem counter_other : ∀ {D T j k v w},Grid D T → j < 12 → k < 12 → j≠k → Unary D T j v →
  Unary D (counter T D k w) j v := by run_tac checkedFrom `FullBodyClosure.Copy "counter_other"
private def Twin (T : Nat → Option Bool) (D : Nat → Nat) (j k a b : Nat) : Nat → Option Bool :=
  counter (counter T D j a) D k b
private def TransferRows (j k : Nat) (start out : Fin 7500) : Prop :=
  ∃ dec inc : Fin 7500,4≤start.val ∧ SerializedBody.machine.step start none=(dec,none,.stay) ∧
    DecRows j dec out inc ∧ IncRows k inc start
private theorem transfer_price (P a d i t : Nat) (hd : d≤4*P+28) (hi : i≤4*P+28)
    (ht : t≤128*(a+1)*(P+1)) : 1+d+i+t≤128*(a+2)*(P+1) := by nlinarith
private theorem transfer_run {D T P j k wj wk start out} (grid : Grid D T) (fit : D 12≤P)
    (hj : j < 12) (hk : k < 12) (ne : j≠k) (lenj : D (j+1)=D j+wj+1) (lenk : D (k+1)=D k+wk+1)
    (code : TransferRows j k start out) :
    ∀ a b,a≤wj → a+b≤wk → ∃ t,t≤128*(a+1)*(P+1) ∧
      Path P t (node start (D 0) (Twin T D j k a b)) (node out (D 0) (Twin T D j k 0 (a+b))) := by
  rcases code with ⟨dec,inc,ss,jump,decrement,increment⟩
  have rootFit : D 0≤P:=le_trans (grid_mono grid 0 12 (by decide) (by decide)) fit
  have orderj:=grid_mono grid 0 j (by omega) (by omega)
  have orderk:=grid_mono grid 0 k (by omega) (by omega)
  have bankj:=grid_mono grid (j+1) 12 (by omega) (by decide)
  have bankk:=grid_mono grid (k+1) 12 (by omega) (by decide)
  intro a
  induction a with
  | zero =>
    intro b ha hb
    have g : Grid D (Twin T D j k 0 b):=counter_grid (counter_grid grid j 0 hj) k b hk
    have unary : Unary D (Twin T D j k 0 b) j 0:=counter_other (w:=b) (counter_grid grid j 0 hj) hj hk ne (counter_unary T D j 0)
    have one:=keep start dec (D 0) (D 0) (Twin T D j k 0 b) .stay (P:=P) rootFit rootFit ss
      (by rw [grid_blank g 0 (by decide)];exact jump) rfl
    have last:=dec_zero g hj fit lenj unary decrement
    have path:=one.append last
    simp only [Nat.zero_add]
    refine ⟨_,?_,path⟩
    omega
  | succ a ih =>
    intro b ha hb
    have g : Grid D (Twin T D j k (a+1) b):=counter_grid (counter_grid grid j (a+1) hj) k b hk
    have unary : Unary D (Twin T D j k (a+1) b) j (a+1):=counter_other (w:=b) (counter_grid grid j (a+1) hj) hj hk ne (counter_unary T D j (a+1))
    have one:=keep start dec (D 0) (D 0) (Twin T D j k (a+1) b) .stay (P:=P) rootFit rootFit ss
      (by rw [grid_blank g 0 (by decide)];exact jump) rfl
    have down:=dec_positive g hj fit lenj unary (by omega) ha decrement
    have outside:=separate_fields grid hj hk ne (i:=D j+(a+1)) (by omega) (by omega)
    have downEq : put (Twin T D j k (a+1) b) (D j+(a+1)) (some false)=Twin T D j k a b := by
      rw [Twin,counter_put_outside _ D k b _ _ outside,counter_down _ D j (a+1) wj lenj (by omega) ha]
      simp only [Nat.add_sub_cancel]
      rfl
    rw [downEq] at down
    have up:=inc_success (counter_grid (counter_grid grid j a hj) k b hk) hk fit lenk
      (counter_unary (counter T D j a) D k b) (by omega) increment
    rw [counter_up _ D k b wk lenk (by omega)] at up
    obtain ⟨t,price,tail⟩:=ih (b+1) (by omega) (by omega)
    have path:=one.append (down.append (up.append tail))
    rw [show a+(b+1)=(a+1)+b by omega] at path
    refine ⟨_,?_,path⟩
    have hd : 2*(D j-D 0+j)+2*(a+1)+4≤4*P+28 := by omega
    have hi : 2*(D k-D 0+k)+2*b+4≤4*P+28 := by omega
    have total:=transfer_price P a _ _ t hd hi price
    simpa only [Nat.add_assoc] using total
end FullBodyClosure
