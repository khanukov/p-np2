import VirtualLeaf.Source
namespace VirtualLeaf
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
run_cmd do
  for (m,s) in [("Transport","keep"),("Transport","extra_row"),("Machine","rows"),("Transport","entry_ne")] do
    let ns:=(← getEnv).constants.toList.map Prod.fst |>.filter fun n =>
      n.toString.startsWith ("_private.VirtualLeaf."++m++".") && n.toString.endsWith (".VirtualLeaf."++s)
    unless ns.length==1 do throwError "Ambiguous body term {s}: {ns}"
    logInfo m!"private-term|{ns.head!}"
    modifyScope fun st => {st with openDecls:=.explicit ((s.splitOn ".").foldl Name.str Name.anonymous) ns.head! :: st.openDecls}
private structure Trace (M : UniformTM) {N B : Nat} (lo hi t : Nat) (c d : Config M.stateCount N B) : Prop where
  run : M.run t c=d
  bound : ∀ u, u ≤ t → lo ≤ (M.run u c).head.val ∧ (M.run u c).head.val ≤ hi
private theorem nil {M N B lo hi} (c : Config M.stateCount N B) (h : lo ≤ c.head.val ∧ c.head.val ≤ hi) : Trace M lo hi 0 c c :=
  ⟨by rw [UniformTM.run],by
    intro u hu
    have eq : u=0 := by omega
    subst u
    rw [UniformTM.run]
    exact h⟩
private theorem single {M N B lo hi} (c d : Config M.stateCount N B) (hc : lo ≤ c.head.val ∧ c.head.val ≤ hi)
    (hd : lo ≤ d.head.val ∧ d.head.val ≤ hi) (step : M.stepConfig c=d) : Trace M lo hi 1 c d := by
  refine ⟨by rw [UniformTM.run,UniformTM.run]; exact step,?_⟩; intro u hu; interval_cases u
  · rw [UniformTM.run]; exact hc
  · rw [UniformTM.run,UniformTM.run]
    rw [step]; exact hd
private theorem append {M N B lo hi t v c d e} (a : @Trace M N B lo hi t c d) (b : Trace M lo hi v d e) : Trace M lo hi (t+v) c e := by
  refine ⟨by rw [UniformTM.run_add,a.run,b.run],?_⟩
  intro u hu; by_cases first : u ≤ t
  · exact a.bound u first
  · have eq : u=t+(u-t) := by omega
    rw [eq,UniformTM.run_add,a.run]; exact b.bound _ (by omega)
private theorem sweepL {M : UniformTM} {N B lo hi : Nat} (s : Fin M.stateCount) (T : Fin (tapeLength N B) → Option Bool)
    (low v : Nat) (fit : hi < tapeLength N B) (lower : lo ≤ low) (upper : low+v ≤ hi)
    (row : ∀ i : Fin (tapeLength N B), low < i.val → i.val ≤ low+v → M.step s (T i)=(s,T i,.left)) :
    Trace M lo hi v ⟨s,⟨low+v,by omega⟩,T⟩ ⟨s,⟨low,by omega⟩,T⟩ := by
  induction v with
  | zero => exact nil ⟨s,⟨low,by omega⟩,T⟩ ⟨lower,by change low ≤ hi; omega⟩
  | succ v ih =>
    have one:=single (M:=M) (lo:=lo) (hi:=hi) ⟨s,⟨low+(v+1),by omega⟩,T⟩ ⟨s,⟨low+v,by omega⟩,T⟩
      ⟨by dsimp only; omega,upper⟩ ⟨by dsimp only; omega,by dsimp only; omega⟩
      (keep s s ⟨low+(v+1),by omega⟩ ⟨low+v,by omega⟩ T .left
        (row _ (by change low < low+(v+1); omega) (by change low+(v+1) ≤ low+(v+1); rfl))
        (Fin.ext (by dsimp only [moveHead]; omega)))
    have rest:=ih (by omega) (by intro i l h; exact row i l (by omega))
    exact (by simpa only [Nat.add_comm 1 v] using append one rest)
private theorem sweepR {M : UniformTM} {N B lo hi : Nat} (s : Fin M.stateCount) (T : Fin (tapeLength N B) → Option Bool)
    (low v : Nat) (fit : hi < tapeLength N B) (lower : lo ≤ low) (upper : low+v ≤ hi)
    (row : ∀ i : Fin (tapeLength N B), low ≤ i.val → i.val < low+v → M.step s (T i)=(s,T i,.right)) :
    Trace M lo hi v ⟨s,⟨low,by omega⟩,T⟩ ⟨s,⟨low+v,by omega⟩,T⟩ := by
  induction v generalizing low with
  | zero => exact nil ⟨s,⟨low,by omega⟩,T⟩ ⟨lower,by change low ≤ hi; omega⟩
  | succ v ih =>
    have one:=single (M:=M) (lo:=lo) (hi:=hi) ⟨s,⟨low,by omega⟩,T⟩ ⟨s,⟨low+1,by omega⟩,T⟩
      ⟨lower,by dsimp only; omega⟩ ⟨by dsimp only; omega,by dsimp only; omega⟩
      (keep s s ⟨low,by omega⟩ ⟨low+1,by omega⟩ T .right
        (row _ le_rfl (by change low < low+(v+1); omega))
        (Fin.ext (by simp only [moveHead,dif_pos (show low+1 < tapeLength N B by omega)])))
    have rest:=ih (low+1) (by omega) (by omega) (by intro i l h; exact row i (by omega) (by omega))
    simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using append one rest
private theorem native (k : Nat) (j : Fin 8) (b : Option Bool) :
    (machine k).step (extra k j) b=
      match j.val,b with
      | 0,none => (extra k ⟨1,by decide⟩,none,.stay)
      | 1,none => (extra k ⟨2,by decide⟩,none,.left)
      | 2,some v => (extra k ⟨2,by decide⟩,some v,.left)
      | 2,none => (extra k ⟨3,by decide⟩,none,.right)
      | 3,some v => (extra k ⟨if v then 5 else 4,by cases v <;> decide⟩,some v,.right)
      | 3,none => (embed k (IngressRepair.machine k).reject,none,.stay)
      | 4,some v => (extra k ⟨4,by decide⟩,some v,.right)
      | 5,some v => (extra k ⟨5,by decide⟩,some v,.right)
      | 4,none => (result k false,some false,.stay)
      | 5,none => (result k true,some true,.stay)
      | 6,v => (result k false,v,.stay)
      | 7,v => (result k true,v,.stay)
      | _,v => (embed k (IngressRepair.machine k).reject,v,.stay) := by
  rw [extra_row]; dsimp only [rows,extra]
  rw [dif_neg (by omega),Nat.add_sub_cancel_left]
  rfl
private theorem extra_ne (k : Nat) (j : Fin 8) : extra k j ≠ (machine k).accept ∧ extra k j ≠ (machine k).reject := by
  have ne (s : Fin (IngressRepair.machine k).stateCount) : extra k j ≠ embed k s := by
    intro h; have e:=congrArg Fin.val h; dsimp only [extra,embed] at e; have hs:=s.isLt; omega
  exact ⟨ne _,ne _⟩
theorem prepared (k : Nat) : Target.Body k := by
  intro N B L n beta T fit sep last digits
  let H : Fin (tapeLength N B):=⟨L+n+1,fit⟩
  let E (j : Fin 8) (h : Fin (tapeLength N B)) : Config (machine k).stateCount N B:=⟨extra k j,h,T⟩
  have atH : T H=none:=last
  have hb : L ≤ H.val ∧ H.val ≤ L+n+1:=⟨by dsimp [H]; omega,le_rfl⟩
  have a:=single (M:=machine k) (lo:=L) (hi:=L+n+1) ⟨embed k (entry k),H,T⟩ (E ⟨0,by decide⟩ H) hb hb
    (keep _ _ H H T .stay (by rw [atH,(table_delta k).2]; simp) rfl)
  have b:=single (M:=machine k) (lo:=L) (hi:=L+n+1) (E ⟨0,by decide⟩ H) (E ⟨1,by decide⟩ H) hb hb
    (keep _ _ H H T .stay (by rw [atH,native]) rfl)
  have c:=single (M:=machine k) (lo:=L) (hi:=L+n+1) (E ⟨1,by decide⟩ H) (E ⟨2,by decide⟩ ⟨L+n,by omega⟩) hb ⟨by dsimp only [E]; omega,by dsimp only [E]; omega⟩
    (keep _ _ _ _ T .left (by rw [atH,native]) (Fin.ext (by dsimp only [moveHead,H]; omega)))
  have occupied (i : Fin (tapeLength N B)) (lo : L < i.val) (hi : i.val < L+n+1) : ∃ v,T i=some v := by
    let j : Fin n:=⟨i.val-L-1,by omega⟩
    have eq : (⟨L+j.val+1,by omega⟩ : Fin (tapeLength N B))=i := Fin.ext (by dsimp [j]; omega)
    exact ⟨beta j,eq ▸ digits j⟩
  have left:=sweepL (M:=machine k) (lo:=L) (hi:=L+n+1) (extra k ⟨2,by decide⟩) T L n fit le_rfl (by omega) (by
    intro i lo hi; obtain ⟨v,hv⟩:=occupied i lo (by omega); rw [hv,native])
  have d:=single (M:=machine k) (lo:=L) (hi:=L+n+1) (E ⟨2,by decide⟩ ⟨L,by omega⟩) (E ⟨3,by decide⟩ ⟨L+1,by omega⟩)
    ⟨le_rfl,by dsimp only [E]; omega⟩ ⟨by dsimp only [E]; omega,by dsimp only [E]; omega⟩
    (keep _ _ _ _ T .right (by rw [sep,native]) (Fin.ext (by simp only [moveHead,dif_pos (show L+1 < tapeLength N B by omega)])))
  have pre:=append a (append b (append c (append left d)))
  have sem:=decode_leaf k n beta
  by_cases zero : n=0
  · subst n
    have e:=single (M:=machine k) (lo:=L) (hi:=L+0+1) (E ⟨3,by decide⟩ H) ⟨(machine k).reject,H,T⟩ hb hb
      (keep _ _ H H T .stay (by rw [atH,native]; rfl) rfl)
    have path : Trace (machine k) L (L+1) 5 ⟨embed k (entry k),H,T⟩ ⟨(machine k).reject,H,T⟩ := append pre e
    refine ⟨path.run,path.bound,?_,?_⟩
    · have start : embed k (entry k) ≠ (machine k).accept ∧ embed k (entry k) ≠ (machine k).reject := by
        constructor
        · exact fun h => (entry_ne k).1 ((table_delta k).1 h)
        · exact fun h => (entry_ne k).2 ((table_delta k).1 h)
      have ab:=append a b
      have abc:=append ab c
      intro u hu; interval_cases u
      · rw [UniformTM.run]; exact start
      · rw [a.run]; exact extra_ne k _
      · rw [ab.run]; exact extra_ne k _
      · rw [abc.run]; exact extra_ne k _
      · rw [pre.run]; exact extra_ne k _
    · rw [sem.2.1 rfl]; rfl
  · have pos : 0 < n:=by omega
    let value:=beta ⟨0,pos⟩
    let carry : Fin 8:=⟨if value then 5 else 4,by cases value <;> decide⟩
    have first : T ⟨L+1,by omega⟩=some value:=by simpa only [Nat.add_zero] using digits ⟨0,pos⟩
    have e:=single (M:=machine k) (lo:=L) (hi:=L+n+1) (E ⟨3,by decide⟩ ⟨L+1,by omega⟩) (E carry ⟨L+2,by omega⟩)
      ⟨by dsimp only [E]; omega,by dsimp only [E]; omega⟩ ⟨by dsimp only [E]; omega,by dsimp only [E]; omega⟩
      (keep _ _ _ _ T .right (by rw [first,native]) (Fin.ext (by simp only [moveHead,dif_pos (show L+1+1 < tapeLength N B by omega)])))
    have right:=sweepR (M:=machine k) (lo:=L) (hi:=L+n+1) (extra k carry) T (L+2) (n-1) fit (by omega) (by omega) (by
      intro i lo hi; obtain ⟨v,hv⟩:=occupied i (by omega) (by omega)
      rw [hv,native]; dsimp only [carry]; cases value <;> rfl)
    have rightH : Trace (machine k) L (L+n+1) (n-1) (E carry ⟨L+2,by omega⟩) (E carry H) := by
      refine ⟨right.run.trans ?_,right.bound⟩
      apply Config.ext_parts
      · rfl
      · apply Fin.ext; change L+2+(n-1)=L+n+1; omega
      · rfl
    have write : (machine k).stepConfig (E carry H)=⟨result k value,H,Function.update T H (some value)⟩ := by
      unfold UniformTM.stepConfig; dsimp only [E]; rw [atH,native]
      dsimp only [carry]; cases value <;> apply Config.ext_parts
      all_goals first | rfl | (funext i; by_cases hi : i=H <;> simp [Function.update,hi])
    have f:=single (M:=machine k) (lo:=L) (hi:=L+n+1) (E carry H) ⟨result k value,H,Function.update T H (some value)⟩ hb hb write
    have path:=append pre (append e (append rightH f))
    have price : 1+(1+(1+(n+1)))+(1+(n-1+1))=2*n+5:=by omega
    rw [price] at path
    have safe:= (machine k).no_terminal_of_le ⟨embed k (entry k),H,T⟩
      (by rw [path.run]; exact (extra_ne k _).1) (by rw [path.run]; exact (extra_ne k _).2)
    refine ⟨?_,path.bound,fun u hu => safe u (by omega),?_⟩
    · simpa only [if_neg zero,dif_pos pos] using path.run
    · rw [(sem.2.2 pos).1]; simp only [Option.map_some,if_neg zero,dif_pos pos]; rfl
end VirtualLeaf
