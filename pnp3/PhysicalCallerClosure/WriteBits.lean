import PhysicalCallerClosure.CompareStep
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
  for leaf in ["Node","Path","put","keep","hop","sweepL","sweepR","crossL","crossR","dest"] do
    let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.Engine 0) "PhysicalCallerClosure")
    let some ci:=e.find? n | throwError "Missing Engine support {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
    unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
    unless e.header.moduleNames[i]! == `PhysicalCallerClosure.Engine do throwError "Wrong owner"
    logInfo m!"copy-open|{n}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac support "Node.mk" "constructor"
variable {M : UniformTM} {Safe : Fin M.stateCount → Prop}
private def written (T : Nat → Option Bool) (d : Nat) (bits : Fin 5 → Bool) (m : Nat) : Nat → Option Bool := fun i=>
  if h:d+1 ≤ i ∧ i < d+1+m ∧ i < d+6 then some (bits ⟨i-d-1,by omega⟩) else T i
private theorem written_zero (T d bits) : written T d bits 0=T := by
  funext i;rw [written,dif_neg (by omega)]
private theorem written_step (T d bits m) (hm:m < 5) :
    put (written T d bits m) (d+1+m) (some (bits ⟨m,hm⟩))=written T d bits (m+1) := by
  funext i
  by_cases eq:i=d+1+m
  · subst i
    have h:d+1 ≤ d+1+m ∧ d+1+m < d+1+(m+1) ∧ d+1+m < d+6:=by omega
    simp only [put,ite_true,written,dif_pos h]
    congr 2
    apply Fin.ext;dsimp;omega
  · by_cases h:d+1 ≤ i ∧ i < d+1+m ∧ i < d+6
    · have h':d+1 ≤ i ∧ i < d+1+(m+1) ∧ i < d+6:=by omega
      simp only [put,if_neg eq,written,dif_pos h,dif_pos h']
    · have h':¬(d+1 ≤ i ∧ i < d+1+(m+1) ∧ i < d+6):=by omega
      simp only [put,if_neg eq,written,dif_neg h,dif_neg h']
private theorem written_outside {T d bits m i} (out:i ≤ d ∨ d+6 ≤ i) : written T d bits m i=T i := by
  rw [written,dif_neg (by omega)]
private theorem written_value (T d bits) (j:Fin 5) : written T d bits 5 (d+1+j.val)=some (bits j) := by
  have hj:=j.isLt
  have h:d+1 ≤ d+1+j.val ∧ d+1+j.val < d+1+5 ∧ d+1+j.val < d+6:=by omega
  rw [written,dif_pos h]
  congr 2
  apply Fin.ext;dsimp;omega
private structure WriteRows (bits : Fin 5 → Bool) (entry out : Fin M.stateCount) where
  states : Fin 6 → Fin M.stateCount
  back : Fin M.stateCount
  safeEntry : Safe entry
  safeStates : ∀ j,Safe (states j)
  safeBack : Safe back
  enter : M.step entry none=(states ⟨0,by decide⟩,none,.right)
  writes : ∀ (j:Fin 5) b,M.step (states (Fin.castSucc j)) b=(states (Fin.succ j),some (bits j),.right)
  finish : M.step (states ⟨5,by decide⟩) none=(back,none,.left)
  retreat : ∀ b,M.step back (some b)=(back,some b,.left)
  exit : M.step back none=(out,none,.stay)
private theorem write_forward {d T P bits entry out} (room:d+6 ≤ P)
    (code:WriteRows (Safe:=Safe) bits entry out) : ∀ m,∀ hm:m ≤ 5,
    Path M Safe P m (node (code.states ⟨0,by decide⟩) (d+1) T)
      (node (code.states ⟨m,by omega⟩) (d+1+m) (written T d bits m)) := by
  intro m
  induction m with
  | zero => intro hm;simpa only [written_zero,Nat.add_zero] using Path.nil (node (code.states ⟨0,by decide⟩) (d+1) T) (by omega : d+1 ≤ P)
  | succ m ih =>
    intro hm
    have earlier:=ih (by omega)
    have next:=hop (code.states ⟨m,by omega⟩) (code.states ⟨m+1,by omega⟩) (d+1+m) (d+1+(m+1))
      (written T d bits m) (some (bits ⟨m,by omega⟩)) .right (P:=P) (by omega) (by omega) (code.safeStates _)
      (code.writes ⟨m,by omega⟩ _) (by change (d+1+m)+1=d+1+(m+1);omega)
    rw [written_step T d bits m (by omega)] at next
    exact earlier.append next
private theorem write_path {d T P bits entry out} (room:d+6 ≤ P) (blank:T d=none) (last:T (d+6)=none)
    (code:WriteRows (Safe:=Safe) bits entry out) :
    Path M Safe P 13 (node entry d T) (node out d (written T d bits 5)) := by
  have first:=keep entry (code.states ⟨0,by decide⟩) d (d+1) T .right (P:=P) (by omega) (by omega) code.safeEntry
    (by rw [blank];exact code.enter) rfl
  have forward:=write_forward (T:=T) room code 5 (by decide)
  let U:=written T d bits 5
  have ud:U d=none:=by change written T d bits 5 d=none;rw [written_outside (Or.inl le_rfl)];exact blank
  have ul:U (d+6)=none:=by change written T d bits 5 (d+6)=none;rw [written_outside (Or.inr le_rfl)];exact last
  have take:=keep (code.states ⟨5,by decide⟩) code.back (d+6) (d+5) U .left (P:=P) room (by omega)
    (code.safeStates _) (by rw [ul];exact code.finish) (by change d+6-1=d+5;omega)
  have back:=sweepL code.back U d 5 (P:=P) (by omega) code.safeBack (by
    intro i lo hi
    let j:=i-d-1
    have hj:j < 5:=by dsimp only [j];omega
    have pos:d+1+j=i:=by dsimp only [j];omega
    have val:=written_value T d bits ⟨j,hj⟩
    rw [pos] at val
    rw [show U i=some (bits ⟨j,hj⟩) from val];exact code.retreat _)
  have stop:=keep code.back out d d U .stay (P:=P) (by omega) (by omega) code.safeBack (by rw [ud];exact code.exit) rfl
  exact first.append (forward.append (take.append (back.append stop)))
end PhysicalCallerClosure
