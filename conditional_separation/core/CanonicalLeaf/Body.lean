import CanonicalLeaf.Rows
import Complexity.PrivateInterfaceLookupResolvedLeaf
namespace CanonicalLeaf
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
run_cmd do
  let rows := [("VirtualLeaf.Body","VirtualLeaf","Trace","Trace"),
      ("VirtualLeaf.Body","VirtualLeaf","Trace.run","trace_run"),("VirtualLeaf.Body","VirtualLeaf","Trace.bound","trace_bound"),
      ("VirtualLeaf.Body","VirtualLeaf","single","single"),("VirtualLeaf.Body","VirtualLeaf","append","append"),
      ("VirtualLeaf.Transport","VirtualLeaf","keep","keep"),("VirtualLeaf.Body","VirtualLeaf","native","old_native"),
      ("VirtualLeaf.Body","VirtualLeaf","extra_ne","extra_ne"),("VirtualLeaf.Transport","VirtualLeaf","entry_ne","entry_ne"),
      ("CanonicalLeaf.Rows","CanonicalLeaf","native","native"),("CanonicalLeaf.Rows","CanonicalLeaf","disjoint","disjoint")]
  let validated ← ofExcept (PartAPrivateLeaf.batch (← getEnv) (rows.map fun (o,ns,s,_) => (PartAPrivateLeaf.key o, PartAPrivateLeaf.key (ns++"."++s))))
  for ((mod,ns,s,localName),target) in rows.zip validated do
    let _ := (mod,ns,s)
    let found := [target]
    logInfo m!"private-term|{found.head!}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str Name.anonymous localName) found.head! :: st.openDecls}
private theorem row (k : Nat) (j : Fin 8) (b : Option Bool) :
    (machine k).step (VirtualLeaf.extra k j) b=
      match j.val,b with
      | 0,none => (VirtualLeaf.extra k ⟨1,by decide⟩,none,.stay)
      | 1,none => (VirtualLeaf.extra k ⟨2,by decide⟩,none,.left)
      | 2,some v => (VirtualLeaf.extra k ⟨if v then 5 else 4,by cases v <;> decide⟩,some v,.right)
      | 2,none => (VirtualLeaf.extra k ⟨3,by decide⟩,none,.right)
      | 3,some v => (VirtualLeaf.extra k ⟨if v then 5 else 4,by cases v <;> decide⟩,some v,.right)
      | 3,none => ((machine k).reject,none,.stay)
      | 4,some v => (VirtualLeaf.extra k ⟨4,by decide⟩,some v,.right)
      | 5,some v => (VirtualLeaf.extra k ⟨5,by decide⟩,some v,.right)
      | 4,none => (result k false,some false,.stay)
      | 5,none => (result k true,some true,.stay)
      | 6,v => (result k false,v,.stay)
      | 7,v => (result k true,v,.stay)
      | _,v => ((machine k).reject,v,.stay) := by
  rw [native]
  by_cases h : j.val=2
  · rw [if_pos h]
    have eq : j=⟨2,by decide⟩:=Fin.ext h
    subst j; cases b <;> rfl
  · rw [if_neg h,old_native]
    fin_cases j
    all_goals first | exact (h rfl).elim | (cases b <;> rfl)
private theorem good_entry (k : Nat) :
    (entry k≠(machine k).accept ∧ entry k≠(machine k).reject) ∧ ∀ b, entry k≠result k b := by
  refine ⟨⟨fun h => (entry_ne k).1 ((VirtualLeaf.table_delta k).1 h),fun h => (entry_ne k).2 ((VirtualLeaf.table_delta k).1 h)⟩,?_⟩
  intro b; exact disjoint k (VirtualLeaf.entry k) _
private theorem good_extra (k : Nat) (j : Fin 8) (hj : j.val<6) :
    (VirtualLeaf.extra k j≠(machine k).accept ∧ VirtualLeaf.extra k j≠(machine k).reject) ∧
    ∀ b, VirtualLeaf.extra k j≠result k b := by
  refine ⟨extra_ne k j,?_⟩
  intro b bad
  cases b with
  | false =>
    have e:=congrArg Fin.val bad
    change (IngressRepair.machine k).stateCount+j.val=(IngressRepair.machine k).stateCount+6 at e
    omega
  | true =>
    have e:=congrArg Fin.val bad
    change (IngressRepair.machine k).stateCount+j.val=(IngressRepair.machine k).stateCount+7 at e
    omega
/-- Canonical beta0 is read at H-1, with no scan/reversal or installed operand oracle. -/
theorem prepared (k : Nat) : Target.Body k := by
  intro N B L n beta T fit sep last digits
  let H : Fin (tapeLength N B):=⟨L+n+1,fit⟩
  let P : Fin (tapeLength N B):=⟨L+n,by omega⟩
  let E (j : Fin 8) (h : Fin (tapeLength N B)) : Config (machine k).stateCount N B:=⟨VirtualLeaf.extra k j,h,T⟩
  have atH : T H=none:=last
  have hb : L≤H.val ∧ H.val≤L+n+1:=⟨by dsimp [H]; omega,le_rfl⟩
  have hp : L≤P.val ∧ P.val≤L+n+1:=⟨by dsimp [P]; omega,by dsimp [P]; omega⟩
  have a:=single (M:=machine k) (lo:=L) (hi:=L+n+1) ⟨entry k,H,T⟩ (E ⟨0,by decide⟩ H) hb hb
    (keep _ _ H H T .stay (by rw [atH]; dsimp only [entry]; rw [repaired_rows,if_pos ⟨rfl,rfl⟩]) rfl)
  have b:=single (M:=machine k) (lo:=L) (hi:=L+n+1) (E ⟨0,by decide⟩ H) (E ⟨1,by decide⟩ H) hb hb
    (keep _ _ H H T .stay (by rw [atH,row]) rfl)
  have c:=single (M:=machine k) (lo:=L) (hi:=L+n+1) (E ⟨1,by decide⟩ H) (E ⟨2,by decide⟩ P) hb hp
    (keep _ _ H P T .left (by rw [atH,row]) (Fin.ext (by dsimp only [moveHead,H,P]; omega)))
  have ab:=append a b
  have abc:=append ab c
  have facts (j : Fin 8) (hj : j.val<6)
      (d : Trace (machine k) L (L+n+1) 1 (E ⟨2,by decide⟩ P) (E j H)) :
      (∀ u, u<5 → ((machine k).run u ⟨entry k,H,T⟩).state≠(machine k).accept ∧ ((machine k).run u ⟨entry k,H,T⟩).state≠(machine k).reject) ∧
      (∀ u, u<5 → ∀ v, ((machine k).run u ⟨entry k,H,T⟩).state≠result k v) ∧
      (∀ u, u<5 → ((machine k).run u ⟨entry k,H,T⟩).tape=T) := by
    have four:=append abc d
    refine ⟨?_,?_,?_⟩
    · intro u hu; interval_cases u
      · rw [UniformTM.run]; exact (good_entry k).1
      · rw [trace_run a]; exact (good_extra k _ (by decide)).1
      · rw [trace_run ab]; exact (good_extra k _ (by decide)).1
      · rw [trace_run abc]; exact (good_extra k _ (by decide)).1
      · rw [trace_run four]; exact (good_extra k j hj).1
    · intro u hu; interval_cases u
      · rw [UniformTM.run]; exact (good_entry k).2
      · rw [trace_run a]; exact (good_extra k _ (by decide)).2
      · rw [trace_run ab]; exact (good_extra k _ (by decide)).2
      · rw [trace_run abc]; exact (good_extra k _ (by decide)).2
      · rw [trace_run four]; exact (good_extra k j hj).2
    · intro u hu; interval_cases u
      · rw [UniformTM.run]
      · rw [trace_run a]
      · rw [trace_run ab]
      · rw [trace_run abc]
      · rw [trace_run four]
  have sem:=VirtualLeaf.decode_leaf k n beta
  by_cases zero : n=0
  · subst n
    have atP : T P=none:=sep
    have d:=single (M:=machine k) (lo:=L) (hi:=L+0+1) (E ⟨2,by decide⟩ P) (E ⟨3,by decide⟩ H) hp hb
      (keep _ _ P H T .right (by rw [atP,row]) (Fin.ext (by dsimp only [moveHead,H,P]; rw [dif_pos fit])))
    have e:=single (M:=machine k) (lo:=L) (hi:=L+0+1) (E ⟨3,by decide⟩ H) ⟨(machine k).reject,H,T⟩ hb hb
      (keep _ _ H H T .stay (by rw [atH,row]) rfl)
    have path:=append (append abc d) e
    obtain ⟨safe,first,tape⟩:=facts _ (by decide) d
    refine ⟨trace_run path,trace_bound path,safe,first,tape,?_,sem.1,by omega⟩
    rw [sem.2.1 rfl]; rfl
  · have pos : 0<n:=by omega
    let value:=beta ⟨0,pos⟩
    let carry : Fin 8:=⟨if value then 5 else 4,by cases value <;> decide⟩
    have first : T P=some value:=by simpa only [Nat.add_sub_cancel,Nat.sub_zero] using digits ⟨0,pos⟩
    have d:=single (M:=machine k) (lo:=L) (hi:=L+n+1) (E ⟨2,by decide⟩ P) (E carry H) hp hb
      (keep _ _ P H T .right (by rw [first,row]) (Fin.ext (by dsimp only [moveHead,H,P]; rw [dif_pos fit])))
    have write : (machine k).stepConfig (E carry H)=⟨result k value,H,Function.update T H (some value)⟩ := by
      unfold UniformTM.stepConfig; dsimp only [E]; rw [atH,row]
      dsimp only [carry]; cases value <;> apply Config.ext_parts
      all_goals first | rfl | (funext i; by_cases hi : i=H <;> simp [Function.update,hi])
    have e:=single (M:=machine k) (lo:=L) (hi:=L+n+1) (E carry H) ⟨result k value,H,Function.update T H (some value)⟩ hb hb write
    have path:=append (append abc d) e
    obtain ⟨safe,prior,tape⟩:=facts carry (by dsimp only [carry]; cases value <;> decide) d
    refine ⟨?_,trace_bound path,safe,prior,tape,?_,sem.1,fun p => (sem.2.2 p).2.1⟩
    · simpa only [if_neg zero,dif_pos pos] using trace_run path
    · rw [(sem.2.2 pos).1]; simp only [Option.map_some,if_neg zero,dif_pos pos]; rfl
end CanonicalLeaf
