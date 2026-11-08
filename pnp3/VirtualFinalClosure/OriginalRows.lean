import VirtualFinalClosure.Wire
namespace VirtualFinalClosure.OriginalRows
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,isThm) in [
      ("VirtualFinalClosure.Wire","VirtualFinalClosure.Wire","pack_value","packValue",true),
      ("VirtualFinalClosure.Wire","VirtualFinalClosure.Wire","pack_div","packDiv",true),
      ("VirtualFinalClosure.Wire","VirtualFinalClosure.Wire","terminal_values","terminalValues",true),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","pack","pk",false),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","rawStep","raw",false),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","oldStep","oldRow",false),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","updateFlag","updateFlag",false),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","table",false),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","leaf","leaf",false),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","body","body",false),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",false),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","encodeMeta","encodeMeta",false)] do
    let found:=env.constants.toList.filter fun (n,_)=>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      let kindOK:=match ci with | .thmInfo _=>isThm | .defnInfo _=>!isThm | _=>false
      unless kindOK do throwError "Wrong selected original-row term kind {n}"
      logInfo m!"private-term|{n}|isTheorem={isThm}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) n::st.openDecls}
    | _=>throwError "Nonunique fixed-row term {mod}/{key}"
private def pack_type : ∀ k,Nat → Nat → Fin (machine k).stateCount := pk
private def oldRow_type : Nat → Nat → Nat → Option Bool → Nat × Nat × Option Bool × Move := oldRow
private def update_type : Nat → Bool → Nat := updateFlag
private def Intercept (k : Nat) (s : Fin (CertificateGuardClosure.machine k).stateCount) (b : Option Bool) : Prop :=
  (s=leaf k false ∨ s=leaf k true) ∨
    (b=none ∧ (s=table k 250 ∨ s=table k 304 ∨ s=table k (798+93*k)))
private theorem original_phase (f : Fin 4) : phase (8+f.val)=0 := by fin_cases f <;> decide
private theorem update_bounds (f : Fin 4) (b : Bool) :
    8 ≤ updateFlag (8+f.val) b ∧ updateFlag (8+f.val) b < 12 := by
  fin_cases f <;> cases b <;> decide
private theorem row_projection (k : Nat) (s : Fin (CertificateGuardClosure.machine k).stateCount)
    (f : Fin 4) (b : Option Bool) (safe : ¬Intercept k s b) :
    ∃ g : Fin 4,oldRow k s.val (8+f.val) b=
      (((CertificateGuardClosure.machine k).step s b).1.val,8+g.val,
        ((CertificateGuardClosure.machine k).step s b).2.1,((CertificateGuardClosure.machine k).step s b).2.2) := by
  let O:=CertificateGuardClosure.machine k
  have hf:=f.isLt
  have hs : (⟨s.val%O.stateCount,Nat.mod_lt _ (by have h:=O.start.isLt;omega)⟩ : Fin O.stateCount)=s :=
    Fin.ext (Nat.mod_eq_of_lt s.isLt)
  dsimp only [oldRow]
  rw [hs]
  have leaves : ¬(s=leaf k false ∨ s=leaf k true) := by intro h;exact safe (Or.inl h)
  have caps : b=none → ¬(s=table k 250 ∨ s=table k 304 ∨ s=table k (798+93*k)) := by
    intro hb h;exact safe (Or.inr ⟨hb,h⟩)
  rw [if_neg leaves]
  rw [if_neg (by intro h;exact caps h.2.1 (by rcases h.2.2 with h|h;exact Or.inl h;exact Or.inr (Or.inl h)))]
  rw [if_neg (by intro h;exact caps h.2.1 (Or.inr (Or.inr h.2.2)))]
  have ph:=original_phase f
  rw [if_neg (by intro h;rw [ph] at h;omega)]
  rw [if_neg (by intro h;rw [ph] at h;omega)]
  let a:=O.step s b
  let next:=if ∃ j : Fin 3,a.1=body k j then encodeMeta 0 2 0 0 0
    else if b=none ∧ s=table k 43 then updateFlag (8+f.val) false
    else if b=none ∧ s=table k 47 then updateFlag (8+f.val) true
    else if b=none ∧ s=table k 51 then updateFlag (8+f.val) false
    else 8+f.val
  have bound : 8 ≤ next ∧ next < 12 := by
    dsimp only [next]
    split_ifs
    · decide
    · exact update_bounds f false
    · exact update_bounds f true
    · exact update_bounds f false
    · omega
  let g:Fin 4:=⟨next-8,by omega⟩
  refine ⟨g,?_⟩
  change (a.1.val,next,a.2)=(a.1.val,8+g.val,a.2)
  have value:next=8+g.val := by dsimp only [g];omega
  rw [value]
private theorem raw_projection (k : Nat) (s : Fin (CertificateGuardClosure.machine k).stateCount)
    (f : Fin 4) (b : Option Bool) (safe : ¬Intercept k s b) :
    ∃ g : Fin 4,(machine k).rawStep (pk k s.val (8+f.val)) b=
      (pk k ((CertificateGuardClosure.machine k).step s b).1.val (8+g.val),
        ((CertificateGuardClosure.machine k).step s b).2) := by
  let O:=CertificateGuardClosure.machine k
  have hm : 8+f.val < 144 := by have h:=f.isLt;omega
  have bound : s.val < O.stateCount+239 := by have h:s.val<O.stateCount:=s.isLt;omega
  have div:=packDiv k s.val (8+f.val) bound hm
  obtain ⟨g,row⟩:=row_projection k s f b safe
  change ∃ g : Fin 4,raw k (pk k s.val (8+f.val)) b=_
  dsimp only [raw]
  rw [div.1,div.2,if_pos s.isLt,row]
  by_cases terminal : (O.step s b).1=O.accept ∨ (O.step s b).1=O.reject
  · refine ⟨⟨0,by decide⟩,?_⟩
    rw [if_pos (by rcases terminal with h|h;exact Or.inl (congrArg Fin.val h);exact Or.inr (congrArg Fin.val h))]
    rfl
  · refine ⟨g,?_⟩
    rw [if_neg (by
      intro h
      apply terminal
      rcases h with h|h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h))]
private theorem step_projection (k : Nat) (s : Fin (CertificateGuardClosure.machine k).stateCount)
    (f : Fin 4) (b : Option Bool) (safe : ¬Intercept k s b) :
    ∃ g : Fin 4,(machine k).step (pk k s.val (8+f.val)) b=
      (pk k ((CertificateGuardClosure.machine k).step s b).1.val (8+g.val),
        ((CertificateGuardClosure.machine k).step s b).2) := by
  let O:=CertificateGuardClosure.machine k
  have hm : 8+f.val < 144 := by have h:=f.isLt;omega
  have val:=packValue k s.val (8+f.val) (by have h:=s.isLt;omega) hm
  have tv:=terminalValues k
  by_cases a : pk k s.val (8+f.val)=(machine k).accept
  · have eq:=congrArg Fin.val a
    rw [val,tv.1] at eq
    have same:s=O.accept := Fin.ext (by have h:=f.isLt;change s.val=(CertificateGuardClosure.machine k).accept.val;omega)
    refine ⟨⟨0,by decide⟩,?_⟩
    rw [a,same,UniformTM.step_accept,UniformTM.step_accept]
    rfl
  · by_cases r : pk k s.val (8+f.val)=(machine k).reject
    · have eq:=congrArg Fin.val r
      rw [val,tv.2] at eq
      have same:s=O.reject := Fin.ext (by have h:=f.isLt;change s.val=(CertificateGuardClosure.machine k).reject.val;omega)
      refine ⟨⟨0,by decide⟩,?_⟩
      rw [r,same,UniformTM.step_reject,UniformTM.step_reject]
      rfl
    · rw [UniformTM.step_of_ne (machine k) a r b]
      exact raw_projection k s f b safe
#print axioms pack_type
#print axioms oldRow_type
#print axioms update_type
#print axioms row_projection
#print axioms raw_projection
#print axioms step_projection
end VirtualFinalClosure.OriginalRows
