import PhysicalCallerClosure.RowSource
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command Tactic
private def select (owner : Name) (leaf kind : String) : TacticM Unit := do
  let e←getEnv
  let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure")
  let some ci:=e.find? n | throwError "Missing exact paid-row support {n}"
  let actual:=match ci with | .defnInfo _=>"definition" | .thmInfo _=>"theorem" | .ctorInfo _=>"constructor" | .inductInfo _=>"inductive" | _=>"other"
  unless actual==kind do throwError "Wrong paid-row support kind"
  let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
  unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
  unless e.header.moduleNames[i]! == owner do throwError "Wrong paid-row support owner"
  logInfo m!"paid-row-adapter|{n}|{ci.type}"
  closeMainGoal `select (mkConst n (ci.levelParams.map Level.param))
run_cmd do
  let e←getEnv
  for (owner,leaves) in [(`PhysicalCallerClosure.Engine,["put"]),
      (`PhysicalCallerClosure.RoundFrame,["Exterior"]),(`PhysicalCallerClosure.RoundImage,["frameMk"]),
      (`PhysicalCallerClosure.Compare,["flags"]),
      (`PhysicalCallerClosure.SourceInitialize,["sourceHoles","anchorMode"]),
      (`PhysicalCallerClosure.WriteBits,["written","written_outside","written_value"]),
      (`PhysicalCallerClosure.RowTape,["d12_lower"]),(`PhysicalCallerClosure.RowSource,["zero_beta"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing paid-row term {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong owner"
      logInfo m!"paid-row-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private theorem initial_frame (T : Nat → Option Bool) (S z n F r M A Q : Nat) (a t : Fin 3)
    (arena:S+z+n+3+Q < F) (aS:A ≤ S) (eof:T S=none)
    (beta:∀ j:Fin n,T (S+z+n+2-j.val)=some false)
    (marks:∀ i,S+z+n+3 < i → i ≤ S+z+n+3+Q → T i=some true)
    (gap:∀ i,S+z+n+3+Q < i → i < F → T i=none) :
    Exterior T (written (sourceHoles T S M A) (SerializedBody.delimiter F r n 12) (flags a t false) 5)
      S z n F r M A Q (Pnp3.Core.vecOfNat n 0) (flags a t false) (decide (A < S)) (decide (M < S)) := by
  let U:=sourceHoles T S M A
  have dl:=d12_lower F r n
  have low (i) (hi:i ≤ F) : written (sourceHoles T S M A) (SerializedBody.delimiter F r n 12) (flags a t false) 5 i=sourceHoles T S M A i:=written_outside (Or.inl (by omega))
  have high (i) (hi:S < i) : sourceHoles T S M A i=T i:=by
    unfold sourceHoles
    rw [put,if_neg (by omega)]
    by_cases hm:M < S
    · rw [if_pos hm,put,if_neg (by omega)]
    · rw [if_neg hm]
  refine frameMk ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i hi
    rw [low i (by omega)]
    change U i=(if (decide (A < S)=true ∧ i=A) ∨ (decide (M < S)=true ∧ i=M-1) then none else T i)
    unfold U sourceHoles
    by_cases eq:i=A
    · subst i;simp only [put,ite_true,decide_eq_true_eq];rw [if_pos (Or.inl ⟨hi,True.intro⟩)]
    · rw [put,if_neg eq]
      by_cases hm:M < S
      · rw [if_pos hm,put]
        by_cases anchor:i=M-1
        · rw [if_pos anchor]
          simp only [decide_eq_true_eq]
          rw [if_pos (Or.inr ⟨hm,anchor⟩)]
        · rw [if_neg anchor]
          simp only [decide_eq_true_eq]
          rw [if_neg (by intro h;rcases h with ⟨_,bad⟩|⟨_,bad⟩;exact eq bad;exact anchor bad)]
      · rw [if_neg hm]
        simp only [decide_eq_true_eq]
        rw [if_neg (by intro h;rcases h with ⟨_,bad⟩|⟨bad,_⟩;exact eq bad;exact hm bad)]
  · rw [low S (by omega)]
    unfold sourceHoles
    by_cases eq:S=A
    · rw [put,if_pos eq,eof]
    · rw [put,if_neg eq]
      by_cases hm:M < S
      · rw [if_pos hm,put,if_neg (by omega)]
      · rw [if_neg hm]
  · intro i lo hi;rw [low i (by omega),high i lo]
  · rw [low _ (by omega),high _ (by omega)]
  · rw [low _ (by omega),high _ (by omega)]
  · intro j;have hj:=j.isLt
    rw [low _ (by omega),high _ (by omega),beta j]
    have zero:=congrFun (zero_beta n) j
    rw [zero]
  · intro i lo hi
    rw [low i (by omega),high i (by omega)]
    by_cases inside:i ≤ S+z+n+3+Q
    · rw [if_pos inside];exact marks i lo inside
    · rw [if_neg inside];exact gap i (by omega) hi
  · rw [low F le_rfl,high F (by omega)]
  · intro j;exact written_value U _ (flags a t false) j
  · intro i hi
    rw [written_outside (Or.inr hi),high i (by omega)]
end PhysicalCallerClosure
