import VirtualLeaf.Target
namespace VirtualLeaf
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
run_cmd do
  for (mod,ns,s) in [("VirtualLeaf.Machine","VirtualLeaf","rows"),
      ("VirtualReady.Kernel","VirtualReady","codes"),("VirtualReady.Kernel","VirtualReady","aft"),
      ("VirtualReady.Kernel","VirtualReady","sym"),("VirtualReady.Kernel","VirtualReady","enc"),("VirtualReady.Kernel","VirtualReady","mov")] do
    let found:=(← getEnv).constants.toList.map Prod.fst |>.filter fun n =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++s)
    unless found.length==1 do throwError "Ambiguous private term {mod}/{s}: {found}"
    logInfo m!"private-term|{found.head!}"
    modifyScope fun st => {st with openDecls:=.explicit ((s.splitOn ".").foldl Name.str Name.anonymous) found.head! :: st.openDecls}
private theorem inject (k : Nat) : Function.Injective (embed k) := by
  intro s t h; apply Fin.ext; exact congrArg (fun q : Fin ((IngressRepair.machine k).stateCount+8) => q.val) h
private theorem entry_val (k : Nat) : (entry k).val=1224+93*k := by
  change 288+((64+265+82*k+1+11*k+604+2)%Cursor.stateCount k)=1224+93*k
  rw [Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)]; omega
private theorem entry_ne (k : Nat) : entry k≠(IngressRepair.machine k).accept ∧ entry k≠(IngressRepair.machine k).reject := by
  have a : (IngressRepair.machine k).accept.val=327 := (AllArityCursor.control_values k).2.2.1
  have r : (IngressRepair.machine k).reject.val=328 := (AllArityCursor.control_values k).2.2.2
  constructor <;> intro h <;> have e:=congrArg Fin.val h
  · rw [entry_val,a] at e; omega
  · rw [entry_val,r] at e; omega
/-- Exact authorized delta relative to the REPAIRED base; all other old rows agree. -/
theorem table_delta (k : Nat) : Function.Injective (embed k) ∧
    ∀ s b, (machine k).step (embed k s) b=
      if s=entry k ∧ b=none then (extra k ⟨0,by decide⟩,none,.stay)
      else (embed k ((IngressRepair.machine k).step s b).1,((IngressRepair.machine k).step s b).2) := by
  refine ⟨inject k,?_⟩; intro s b
  by_cases ha : s=(IngressRepair.machine k).accept
  · subst s
    have ni : ¬((IngressRepair.machine k).accept=entry k ∧ b=none) :=
      fun h => (entry_ne k).1 h.1.symm
    rw [if_neg ni]
    change (machine k).step (machine k).accept b=_
    rw [UniformTM.step_accept,UniformTM.step_accept]; rfl
  by_cases hr : s=(IngressRepair.machine k).reject
  · subst s
    have ni : ¬((IngressRepair.machine k).reject=entry k ∧ b=none) :=
      fun h => (entry_ne k).2 h.1.symm
    rw [if_neg ni]
    change (machine k).step (machine k).reject b=_
    rw [UniformTM.step_reject,UniformTM.step_reject]; rfl
  have na : embed k s≠(machine k).accept := by
    change embed k s≠embed k (IngressRepair.machine k).accept
    exact fun h => ha (inject k h)
  have nr : embed k s≠(machine k).reject := by
    change embed k s≠embed k (IngressRepair.machine k).reject
    exact fun h => hr (inject k h)
  rw [UniformTM.step_of_ne (machine k) na nr]
  change rows k (embed k s) b=_
  dsimp only [rows,embed]
  rw [dif_pos s.isLt]
private theorem extra_row (k : Nat) (j : Fin 8) (b : Option Bool) :
    (machine k).step (extra k j) b=rows k (extra k j) b := by
  have ne (s : Fin (IngressRepair.machine k).stateCount) : extra k j≠embed k s := by
    intro h; have e:=congrArg Fin.val h; dsimp only [extra,embed] at e; have hs:=s.isLt; omega
  exact UniformTM.step_of_ne _ (ne _) (ne _) b
private theorem ready_index (k : Nat) : Cursor.mReady k ⟨2,by decide⟩=Cursor.q k (936+93*k) := by
  apply Fin.ext
  change (64+265+82*k+1+11*k+604+2)%Cursor.stateCount k=(936+93*k)%Cursor.stateCount k
  congr 1; omega
private theorem ready_row (k : Nat) (b : Option Bool) :
    (Cursor.machine k).step (Cursor.mReady k ⟨2,by decide⟩) b=(Cursor.mReady k ⟨2,by decide⟩,b,.stay) := by
  rw [ready_index]
  have tail : (aft k).drop 1818=[8425+837*k,8428+837*k,8431+837*k] := by
    unfold aft
    fromDonor "Cursor.Machine" "Cursor" "after" => simp only [OLD,List.append_assoc]
    rfl
  have got : (codes k)[3*(936+93*k-64)+sym b]?=some (enc (936+93*k) b .stay) := by
    fromDonor "VirtualReady.Kernel" "VirtualReady" "program_split" => rw [OLD]
    rw [List.getElem?_toArray,List.getElem?_append]
    fromDonor "VirtualReady.Kernel" "VirtualReady" "pref_len" =>
      rw [if_neg (by rw [OLD]; cases b with | none => simp [sym]; omega | some v => cases v <;> simp [sym] <;> omega)]
      rw [show 3*(936+93*k-64)+sym b-_ =1818+sym b by rw [OLD]; omega]
    rw [←List.getElem?_drop,tail]
    cases b with
    | none => simp [sym,enc,mov]; ring
    | some v => cases v <;> simp [sym,enc,mov] <;> ring
  fromDonor "VirtualReady.Kernel" "VirtualReady" "decode_actual" =>
    have h:=OLD k (936+93*k) (enc (936+93*k) b .stay) b (by omega) (by unfold Cursor.stateCount; omega) got
  fromDonor "VirtualReady.Kernel" "VirtualReady" "dec_enc" => have eq:=OLD k (936+93*k) b .stay
  exact h.trans eq
private theorem old_ready (k : Nat) (b : Option Bool) :
    (IngressRepair.machine k).step (entry k) b=(entry k,b,.stay) := by
  change (IngressRepair.producer.seq (Cursor.machine k)).step _ b=_
  unfold entry
  rw [UniformTM.seq_step_right,ready_row]
private theorem keep {M : UniformTM} {N B : Nat} (s s' : Fin M.stateCount) (h h' : Fin (tapeLength N B))
    (T : Fin (tapeLength N B) → Option Bool) (mv : Move)
    (row : M.step s (T h)=(s',T h,mv)) (head : moveHead h mv=h') :
    M.stepConfig ⟨s,h,T⟩=⟨s',h',T⟩ := by
  unfold UniformTM.stepConfig; rw [row]
  apply Config.ext_parts
  · rfl
  · exact head
  funext i; dsimp only
  split_ifs with eq
  · subst i; rfl
  · rfl
private theorem old_fixed {k N B : Nat} (c : Config (IngressRepair.machine k).stateCount N B)
    (atReady : c.state=entry k) : (IngressRepair.machine k).stepConfig c=c := by
  cases c with | mk s h T => change s=entry k at atReady; subst s; exact keep _ _ h h T .stay (old_ready k _) rfl
private theorem fixed_run {M : UniformTM} {N B : Nat} (c : Config M.stateCount N B)
    (fixed : M.stepConfig c=c) (t : Nat) : M.run t c=c := by
  induction t with | zero => rw [UniformTM.run] | succ t ih => rw [UniformTM.run,ih,fixed]
private theorem avoids {k N B t : Nat} (c : Config (IngressRepair.machine k).stateCount N B)
    (last : ((IngressRepair.machine k).run t c).state≠entry k) :
    ∀ u, u≤t → ((IngressRepair.machine k).run u c).state≠entry k := by
  intro u hu bad; apply last
  have fix:=fixed_run _ (old_fixed _ bad) (t-u)
  have eq:=UniformTM.run_add (IngressRepair.machine k) u (t-u) c
  rw [Nat.add_sub_of_le hu,fix] at eq
  exact congrArg Config.state eq |>.trans bad
private theorem first_ready {k N B t : Nat} (c : Config (IngressRepair.machine k).stateCount N B)
    (hit : ((IngressRepair.machine k).run t c).state=entry k) :
    ∃ s, s≤t ∧ (IngressRepair.machine k).run s c=(IngressRepair.machine k).run t c ∧
      ∀ u, u<s → ((IngressRepair.machine k).run u c).state≠entry k := by
  induction t with
  | zero => exact ⟨0,le_rfl,rfl,by omega⟩
  | succ t ih =>
    by_cases h : ((IngressRepair.machine k).run t c).state=entry k
    · obtain ⟨s,hs,eq,prior⟩:=ih h
      exact ⟨s,by omega,eq.trans (by rw [UniformTM.run,old_fixed _ h]),prior⟩
    · exact ⟨t+1,le_rfl,rfl,by intro u hu; exact avoids c h u (by omega)⟩
private theorem step_lift {k N B : Nat} (c : Config (IngressRepair.machine k).stateCount N B) (safe : c.state≠entry k) :
    (machine k).stepConfig (config k c)=config k ((IngressRepair.machine k).stepConfig c) := by
  have row:=(table_delta k).2 c.state (c.tape c.head)
  rw [if_neg (by tauto)] at row
  cases c with | mk s h T =>
    unfold UniformTM.stepConfig config; dsimp only at row ⊢; rw [row]
private theorem transport {k N B t : Nat} (c : Config (IngressRepair.machine k).stateCount N B)
    (safe : ∀ u, u<t → ((IngressRepair.machine k).run u c).state≠entry k) :
    ∀ u, u≤t → (machine k).run u (config k c)=config k ((IngressRepair.machine k).run u c) := by
  intro u hu; induction u with
  | zero => rw [UniformTM.run,UniformTM.run]
  | succ u ih => rw [UniformTM.run,ih (by omega),step_lift _ (safe u (by omega)),UniformTM.run]
end VirtualLeaf
