import CanonicalLeaf.Target
import Complexity.PrivateInterfaceLookupResolvedLeaf
namespace CanonicalLeaf
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
run_cmd do
  let rows := [("CanonicalLeaf.Machine","CanonicalLeaf","rows","rows"),
      ("VirtualLeaf.Body","VirtualLeaf","native","old_native"),
      ("VirtualLeaf.Body","VirtualLeaf","extra_ne","extra_ne"),
      ("VirtualLeaf.Transport","VirtualLeaf","entry_ne","entry_ne"),
      ("VirtualLeaf.Transport","VirtualLeaf","transport","old_transport")]
  let validated ← ofExcept (PartAPrivateLeaf.batch (← getEnv) (rows.map fun (o,ns,s,_) => (PartAPrivateLeaf.key o, PartAPrivateLeaf.key (ns++"."++s))))
  for ((mod,ns,s,localName),target) in rows.zip validated do
    let _ := (mod,ns,s)
    let found := [target]
    logInfo m!"private-term|{found.head!}"
    modifyScope fun st => {st with openDecls:=.explicit (Name.str Name.anonymous localName) found.head! :: st.openDecls}
private theorem disjoint (k : Nat) (s : Fin (IngressRepair.machine k).stateCount) (j : Fin 8) :
    VirtualLeaf.embed k s≠VirtualLeaf.extra k j := by
  intro bad; have e:=congrArg Fin.val bad
  dsimp only [VirtualLeaf.embed,VirtualLeaf.extra] at e
  have bound:=s.isLt; omega
/-- Exactly two occupied extra2 effective rows change; every other effective row agrees. -/
theorem table_delta (k : Nat) : ∀ s b, (machine k).step s b=
    match b with
    | none => (VirtualLeaf.machine k).step s none
    | some v => if s=VirtualLeaf.extra k ⟨2,by decide⟩ then
        (VirtualLeaf.extra k ⟨if v then 5 else 4,by cases v <;> decide⟩,some v,.right)
      else (VirtualLeaf.machine k).step s (some v) := by
  intro s b
  by_cases a : s=(VirtualLeaf.machine k).accept
  · subst s
    have ne : (VirtualLeaf.machine k).accept≠VirtualLeaf.extra k ⟨2,by decide⟩ := (extra_ne k _).1.symm
    cases b with
    | none => exact ((machine k).step_accept none).trans ((VirtualLeaf.machine k).step_accept none).symm
    | some v => dsimp only; rw [if_neg ne]; exact ((machine k).step_accept (some v)).trans ((VirtualLeaf.machine k).step_accept (some v)).symm
  by_cases r : s=(VirtualLeaf.machine k).reject
  · subst s
    have ne : (VirtualLeaf.machine k).reject≠VirtualLeaf.extra k ⟨2,by decide⟩ := (extra_ne k _).2.symm
    cases b with
    | none => exact ((machine k).step_reject none).trans ((VirtualLeaf.machine k).step_reject none).symm
    | some v => dsimp only; rw [if_neg ne]; exact ((machine k).step_reject (some v)).trans ((VirtualLeaf.machine k).step_reject (some v)).symm
  rw [UniformTM.step_of_ne (machine k) a r]
  change rows k s b=_
  cases b <;> rfl
/-- Original repaired embedding and mode2 entry remain exactly the donor's rows. -/
theorem repaired_rows (k : Nat) : ∀ s b,
    (machine k).step (VirtualLeaf.embed k s) b=
      if s=VirtualLeaf.entry k ∧ b=none then (VirtualLeaf.extra k ⟨0,by decide⟩,none,.stay)
      else (VirtualLeaf.embed k ((IngressRepair.machine k).step s b).1,((IngressRepair.machine k).step s b).2) := by
  intro s b
  rw [table_delta]
  cases b with
  | none => exact (VirtualLeaf.table_delta k).2 s none
  | some v => dsimp only; rw [if_neg (disjoint k s _)]; exact (VirtualLeaf.table_delta k).2 s (some v)
/-- The reviewed missing-FIRST-payload guard survives, uniformly in k. -/
theorem repair138 (k : Nat) :
    (machine k).step (VirtualLeaf.embed k (IngressRepair.producer.seqLeft (Cursor.machine k) (SmallIngress.q 138))) none=
      ((machine k).reject,none,.stay) := by
  rw [repaired_rows]
  have ne : IngressRepair.producer.seqLeft (Cursor.machine k) (SmallIngress.q 138)≠VirtualLeaf.entry k := by
    intro bad; have e:=congrArg Fin.val bad
    fromDonor "VirtualLeaf.Transport" "VirtualLeaf" "entry_val" => rw [OLD] at e
    change 138=1224+93*k at e; omega
  rw [if_neg (by tauto)]
  have row : IngressRepair.producer.step (SmallIngress.q 138) none=(IngressRepair.producer.reject,none,.stay) := by decide
  change (VirtualLeaf.embed k ((IngressRepair.producer.seq (Cursor.machine k)).step _ none).1,
    ((IngressRepair.producer.seq (Cursor.machine k)).step _ none).2)=_
  rw [UniformTM.seq_step_left,row]
  rfl
private theorem base_step (k : Nat) (s : Fin (VirtualLeaf.machine k).stateCount) (b : Option Bool)
    (below : s.val < (IngressRepair.machine k).stateCount) :
    (machine k).step s b=(VirtualLeaf.machine k).step s b := by
  rw [table_delta]
  cases b with
  | none => rfl
  | some v =>
    dsimp only
    have ne : s≠VirtualLeaf.extra k ⟨2,by decide⟩ := by
      intro bad; have e:=congrArg Fin.val bad; dsimp only [VirtualLeaf.extra] at e; omega
    rw [if_neg ne]
private theorem transport {k N B t : Nat} (c : Config (VirtualLeaf.machine k).stateCount N B)
    (safe : ∀ u, u<t → ((VirtualLeaf.machine k).run u c).state.val < (IngressRepair.machine k).stateCount) :
    ∀ u, u≤t → (machine k).run u c=(VirtualLeaf.machine k).run u c := by
  intro u hu; induction u with
  | zero => rw [UniformTM.run,UniformTM.run]
  | succ u ih =>
    rw [UniformTM.run,ih (by omega),UniformTM.run]
    unfold UniformTM.stepConfig
    rw [base_step k _ _ (safe u (by omega))]
private def region (k : Nat) (s : Fin (VirtualLeaf.machine k).stateCount) : Prop :=
  (IngressRepair.machine k).stateCount≤s.val ∨ s=(VirtualLeaf.machine k).reject
private theorem extra_closed (k : Nat) (j : Fin 8) (b : Option Bool) :
    region k ((VirtualLeaf.machine k).step (VirtualLeaf.extra k j) b).1 := by
  rw [old_native]
  fin_cases j <;> cases b with
  | none => first | (left; dsimp only [VirtualLeaf.extra,VirtualLeaf.result]; omega) | (right; rfl)
  | some v => cases v <;> first | (left; dsimp only [VirtualLeaf.extra,VirtualLeaf.result]; omega) | (right; rfl)
private theorem region_step (k : Nat) (s : Fin (VirtualLeaf.machine k).stateCount) (b : Option Bool)
    (inside : region k s) : region k ((VirtualLeaf.machine k).step s b).1 := by
  rcases inside with above | reject
  · let j : Fin 8:=⟨s.val-(IngressRepair.machine k).stateCount,by
      have lim:=s.isLt
      change s.val < (IngressRepair.machine k).stateCount+8 at lim
      omega⟩
    have eq : s=VirtualLeaf.extra k j := Fin.ext (by dsimp only [j,VirtualLeaf.extra]; omega)
    rw [eq]; exact extra_closed k j b
  · rw [reject,UniformTM.step_reject]; exact Or.inr rfl
private theorem region_run {k N B : Nat} (c : Config (VirtualLeaf.machine k).stateCount N B)
    (inside : region k c.state) (t : Nat) : region k ((VirtualLeaf.machine k).run t c).state := by
  induction t with
  | zero => simpa only [UniformTM.run] using inside
  | succ t ih => rw [UniformTM.run]; exact region_step k _ _ ih
private theorem below_before {k N B t : Nat} (c : Config (VirtualLeaf.machine k).stateCount N B)
    (below : ((VirtualLeaf.machine k).run t c).state.val < (IngressRepair.machine k).stateCount)
    (live : ((VirtualLeaf.machine k).run t c).state≠(VirtualLeaf.machine k).reject) :
    ∀ u, u≤t → ((VirtualLeaf.machine k).run u c).state.val < (IngressRepair.machine k).stateCount := by
  intro u hu
  by_contra bad
  have later:=region_run ((VirtualLeaf.machine k).run u c) (Or.inl (by omega)) (t-u)
  rw [←UniformTM.run_add,Nat.add_sub_of_le hu] at later
  rcases later with bound | reject
  · omega
  · exact live reject
private theorem base_end {k N B t : Nat} (c : Config (VirtualLeaf.machine k).stateCount N B)
    (d : Config (IngressRepair.machine k).stateCount N B)
    (done : (VirtualLeaf.machine k).run t c=VirtualLeaf.config k d)
    (live : d.state≠(IngressRepair.machine k).reject) :
    ∀ u, u≤t → ((VirtualLeaf.machine k).run u c).state.val < (IngressRepair.machine k).stateCount := by
  apply below_before c
  · rw [done]; exact d.state.isLt
  · rw [done]; exact fun bad => live ((VirtualLeaf.table_delta k).1 bad)
private theorem native (k : Nat) (j : Fin 8) (b : Option Bool) :
    (machine k).step (VirtualLeaf.extra k j) b=
      if j.val=2 then match b with
        | some v => (VirtualLeaf.extra k ⟨if v then 5 else 4,by cases v <;> decide⟩,some v,.right)
        | none => (VirtualLeaf.extra k ⟨3,by decide⟩,none,.right)
      else (VirtualLeaf.machine k).step (VirtualLeaf.extra k j) b := by
  rw [table_delta]
  have eq : VirtualLeaf.extra k j=VirtualLeaf.extra k ⟨2,by decide⟩ ↔ j.val=2 := by
    constructor
    · intro h; have e:=congrArg Fin.val h; dsimp only [VirtualLeaf.extra] at e; omega
    · intro h; congr 1; exact Fin.ext h
  cases b with
  | none =>
    dsimp only
    by_cases h : j.val=2
    · rw [if_pos h,old_native,h]
    · rw [if_neg h]
  | some v =>
    dsimp only
    by_cases h : j.val=2
    · rw [if_pos (eq.mpr h),if_pos h]
    · rw [if_neg (fun bad => h (eq.mp bad)),if_neg h]
end CanonicalLeaf
