import VirtualFinalClosure.PowerSeedFrame
namespace VirtualFinalClosure.ComputeWeight
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option autoImplicit false
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName,kind) in [
      ("VirtualFinalClosure.SourceWalk","VirtualFinalClosure.SourceWalk","Frame","Frame",(2:Nat)),
      ("VirtualFinalClosure.PowerSeedFrame","VirtualFinalClosure.PowerSeedFrame","power","powerFrame",1),
      ("VirtualFinalClosure.PowerSeedFrame","VirtualFinalClosure.PowerSeedFrame","fields","fields",1),
      ("VirtualFinalClosure.SeedReplay","VirtualFinalClosure.SeedReplay","prepared","seed",1),
      ("VirtualFinalClosure.WeightReplay","VirtualFinalClosure.WeightReplay","prepared","weight",1),
      ("VirtualFinalClosure.CapacityImage","VirtualFinalClosure.CapacityImage","image","image",0),
      ("VirtualFinalClosure.WorkspaceReplay","VirtualFinalClosure.WorkspaceReplay","slot_value","slotValue",1),
      ("VirtualFinalClosure.ArithmeticReplay","VirtualFinalClosure.ArithmeticReplay","lift","lift",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","phase","phase",0),
      ("VirtualFinalClosure.ElasticMachine","VirtualFinalClosure.Elastic","table","tableControl",0)] do
    let found:=env.constants.toList.filter fun (name,_)=>name.toString.startsWith ("_private."++mod++".") && name.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(name,ci)]=>
      let actual : Nat:=match ci with | .defnInfo _=>0 | .thmInfo _=>1 | .inductInfo _=>2 | _=>9
      unless actual=kind do throwError "Wrong actual seed/full-W composition interface {name}"
      logInfo m!"private-term|{name}|kind={actual}|type={ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous aliasName) name::st.openDecls}
    | _=>throwError "Nonunique actual seed/full-W composition interface {mod}/{key}"
private theorem q_value (k i : Nat) (hi : i ≤ 798+93*k) : (Cursor.q k i).val=i:=Nat.mod_eq_of_lt (by unfold Cursor.stateCount;omega)
/-- Physically completed bitLength -> literal seed -> ALL native W arithmetic,
on ONE table/allocation. Actual a and b, full source/cap residuals and local
first W/cap frontier are retained for subsequent raw/growth composition. -/
private theorem prepared (k N B S L n Q F C : Nat) (T : Nat → Option Bool) (m : Fin 144)
    (ph : phase m.val=1) (fr : Frame T S L (L+n+1) Q F)
    (positive : 0 < C) (fits : bitLength n ≤ C) (fit : F+5*C+n+7 < tapeLength N B) :
    let Y:=RuntimeBitLength.Target.fullImage (CappedWorkspace.Target.image (image T F C) L n F C) L n F C
    let Z:=AllArityBitLength.Target.seedImage Y F C n
    let old : Config (Cursor.machine k).stateCount N B:=⟨Cursor.q k 308,⟨L,by obtain ⟨_sl,_lh,_paid,room,_,_,_,_,_,_,_,_,_⟩:=fr;omega⟩,fun i=>Y i.val⟩
    let start : Config (machine k).stateCount N B:=⟨control k (tableControl k 308) m,⟨L,by obtain ⟨_sl,_lh,_paid,room,_,_,_,_,_,_,_,_,_⟩:=fr;omega⟩,fun i=>Y i.val⟩
    ∃ a b,a ≤ 16*(F+5*C+n+8) ∧ b ≤ 2097152*(k+1)*(n+C+1)^2*(F+5*C+n+9) ∧
      (∀ u,u ≤ a → (machine k).run u start=lift k m ((Cursor.machine k).run u old) ∧
        ((Cursor.machine k).run u old).state.val ≤ 329) ∧
      (∀ u,u ≤ b → (machine k).run (a+u) start=lift k m ((Cursor.machine k).run u
        (⟨Cursor.q k 329,⟨F+2*C+n+4,by omega⟩,fun j=>Z j.val⟩ : Config (Cursor.machine k).stateCount N B))) ∧
      (∀ u,u ≤ a+b → ((machine k).run u start).head.val ≤ L+16*(F+5*C+n+8)) ∧
      (∀ u,u < a+b → ∀ j,j=430+93*k ∨ j=798+93*k → ∀ flag : Fin 144,
        ((machine k).run u start).state≠control k (tableControl k j) flag) ∧
      ((Cursor.Target.W k n ≤ C ∧ (machine k).run (a+b) start=
          ⟨control k (tableControl k (430+93*k)) m,⟨F+C+n+3,by omega⟩,
            fun j=>CappedWeight.Target.image Z L n F C 0 (n^k+k) (Cursor.Target.W k n) 0 0 j.val⟩) ∨
       ∃ v2 v3 v4 v5 d,CappedWeight.Target.Cap k n C v2 v3 v4 v5 d ∧
        (machine k).run (a+b) start=
          ⟨control k (tableControl k (798+93*k)) m,⟨F+1,by omega⟩,
            fun j=>CappedWeight.Target.image Z L n F C v2 v3 v4 v5 d j.val⟩) := by
  intro Y Z old start
  obtain ⟨frY,blank,occupied,empty⟩:=fields T S L n Q F C fr positive
  have copyFr:=frY
  obtain ⟨_sl,_lh,_paid,room,_eof,sep,right,d0,fence,_reg,assn,marks,gap⟩:=copyFr
  obtain ⟨a,ap,atSeed,_seedFirst,seedHeads,seedConfigs,seedCeiling⟩:=seed k N B L n Q F C Y m positive room sep assn right
    (by intro i lo hi;by_cases p : i ≤ L+n+1+Q;exact Or.inr (marks i lo p);exact Or.inl (gap i (by omega) hi))
    fence d0 (by intro i lo hi;exact occupied 0 (by decide) i lo hi) (blank 1 (by decide))
    (by intro i lo hi;exact occupied 1 (by decide) i lo hi) (blank 2 (by decide))
    (by intro i lo hi;exact occupied 2 (by decide) i lo hi) (blank 3 (by decide)) empty fit
  obtain ⟨b,bp,weightHeads,weightConfigs,weightFirst,outcome⟩:=weight k N B L n Q F C Z m ph (powerFrame T S L n Q F C fr positive fits) positive fits fit
  refine ⟨a,b,ap,bp,?_,?_,?_,?_,?_⟩
  · intro u hu
    exact ⟨seedConfigs u hu,seedCeiling u hu⟩
  · intro u hu
    rw [UniformTM.run_add,atSeed]
    exact weightConfigs u hu
  · intro u hu
    by_cases early : u ≤ a
    · exact seedHeads u early
    · rw [show u=a+(u-a) by omega,UniformTM.run_add,atSeed]
      exact (weightHeads (u-a) (by omega)).trans (by omega)
  · intro u hu j which flag
    by_cases early : u < a
    · intro equal
      have trace:=seedConfigs u early.le
      have val : ((machine k).run u start).state.val=144*(375+((Cursor.machine k).run u old).state.val)+m.val:=by
        rw [trace]
        exact slotValue k ((Cursor.machine k).run u old).state m
      have target:=slotValue k (Cursor.q k j) flag
      rw [q_value k j (by rcases which with h|h <;> omega)] at target
      have same:=congrArg Fin.val equal
      rw [val,target] at same
      have ce:=seedCeiling u early.le
      change ((Cursor.machine k).run u old).state.val ≤ 329 at ce
      have fm:=m.isLt
      rcases which with h|h <;> omega
    · rw [show u=a+(u-a) by omega,UniformTM.run_add,atSeed]
      exact weightFirst (u-a) (by omega) j which flag
  · rw [UniformTM.run_add,atSeed]
    exact outcome
#print axioms q_value
#print axioms prepared
end VirtualFinalClosure.ComputeWeight
