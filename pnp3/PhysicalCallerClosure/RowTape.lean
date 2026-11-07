import PhysicalCallerClosure.CallerMemory
import PhysicalCallerClosure.AssignmentSemantics
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command Tactic
private def select (owner : Name) (leaf kind : String) : TacticM Unit := do
  let e←getEnv
  let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure")
  let some ci:=e.find? n | throwError "Missing exact paid-row support {n}"
  let actual:=match ci with | .defnInfo _=>"definition" | .thmInfo _=>"theorem" | .ctorInfo _=>"constructor" | _=>"other"
  unless actual==kind do throwError "Wrong paid-row support kind"
  let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
  unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
  unless e.header.moduleNames[i]! == owner do throwError "Wrong paid-row support owner"
  logInfo m!"paid-row-adapter|{n}|{ci.type}"
  closeMainGoal `select (mkConst n (ci.levelParams.map Level.param))
run_cmd do
  let e←getEnv
  for (owner,leaves) in [(`PhysicalCallerClosure.Compare,["flags"]),
      (`PhysicalCallerClosure.CallerMemory,["frameBase","update","image_inside","image_update","written_image"]),
      (`PhysicalCallerClosure.WriteBits,["written","written_outside","written_value"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing paid-row term {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong paid-row owner"
      logInfo m!"paid-row-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
-- Proof-only memory relation. No constructor/row calls this specification.
private def rowExternal (T : Nat → Option Bool) (S z n F r M p marks : Nat)
    (beta : Fin n → Bool) (a t : Fin 3) (last : Bool) : Nat → Option Bool:=
  let V:=written (frameBase T S z n F r marks beta) (SerializedBody.delimiter F r n 12) (flags a t last) 5
  let U:=if M < S then update V (M-1) none else V
  if p < S then update U p none else U
private def rowMemory (T : Nat → Option Bool) (S z n F r g W M p marks : Nat)
    (beta : Fin n → Bool) (a t : Fin 3) (last : Bool) (nodes used rem quota : Nat) : Nat → Option Bool:=
  SerializedBody.image (rowExternal T S z n F r M p marks beta a t last) F r n g W (S-min M S) nodes used rem quota
private theorem d12_lower (F r n : Nat) : F+1 ≤ SerializedBody.delimiter F r n 12 := by
  change F+1 ≤ F+13*r+2*n+16
  omega
private theorem base_low (T : Nat → Option Bool) (S z n F r marks : Nat) (beta : Fin n → Bool)
    (arena:S+z+n+3 < F) (i : Nat) (hi:i ≤ S) : frameBase T S z n F r marks beta i=T i := by
  have d:=d12_lower F r n
  unfold frameBase
  rw [dif_neg (by omega),if_neg (by omega),if_neg (by omega)]
private theorem external_low (T : Nat → Option Bool) (S z n F r M p marks : Nat)
    (beta : Fin n → Bool) (a t : Fin 3) (last : Bool) (arena:S+z+n+3 < F)
    (i : Nat) (hi:i ≤ S) (np:p < S → i≠p) (na:M < S → i≠M-1) :
    rowExternal T S z n F r M p marks beta a t last i=T i := by
  have d:=d12_lower F r n
  have result:written (frameBase T S z n F r marks beta) (SerializedBody.delimiter F r n 12) (flags a t last) 5 i=T i:=by
    rw [written_outside (Or.inl (show i ≤ SerializedBody.delimiter F r n 12 by omega))]
    exact base_low T S z n F r marks beta arena i hi
  unfold rowExternal
  by_cases hp:p < S
  · rw [if_pos hp,update,if_neg (np hp)]
    by_cases hm:M < S
    · rw [if_pos hm,update,if_neg (na hm)];exact result
    · rw [if_neg hm];exact result
  · rw [if_neg hp]
    by_cases hm:M < S
    · rw [if_pos hm,update,if_neg (na hm)];exact result
    · rw [if_neg hm];exact result
private theorem external_eof (T : Nat → Option Bool) (S z n F r M p marks : Nat)
    (beta : Fin n → Bool) (a t : Fin 3) (last : Bool) (arena:S+z+n+3 < F) (ts:T S=none) :
    rowExternal T S z n F r M p marks beta a t last S=none := by
  rw [external_low T S z n F r M p marks beta a t last arena S le_rfl (by omega) (by omega)]
  exact ts
private theorem external_source (T : Nat → Option Bool) (S z n F r M p marks : Nat)
    (beta : Fin n → Bool) (a t : Fin 3) (last : Bool) (arena:S+z+n+3 < F) (before:M < S → p < M)
    (source : Fin S → Bool) (src:∀ i,M ≤ i → ∀ hi:i < S,T i=some (source ⟨i,hi⟩)) :
    ∀ i,M ≤ i → ∀ hi:i < S,rowExternal T S z n F r M p marks beta a t last i=some (source ⟨i,hi⟩) := by
  intro i lo hi
  rw [external_low T S z n F r M p marks beta a t last arena i (by omega) (by intro _;have h:=before (by omega);omega) (by omega)]
  exact src i lo hi
private theorem base_beta (T : Nat → Option Bool) (S z n F r marks : Nat) (beta : Fin n → Bool) (j : Fin n) :
    frameBase T S z n F r marks beta (S+z+n+2-j.val)=some (beta j) := by
  have hj:=j.isLt
  have h:S+z+2 < S+z+n+2-j.val ∧ S+z+n+2-j.val < S+z+2+n+1:=by omega
  unfold frameBase
  rw [dif_pos h]
  congr 2
  apply Fin.ext
  dsimp
  omega
private theorem external_beta (T : Nat → Option Bool) (S z n F r M p marks : Nat)
    (beta : Fin n → Bool) (a t : Fin 3) (last : Bool) (arena:S+z+n+3 < F) (j : Fin n) :
    rowExternal T S z n F r M p marks beta a t last (S+z+n+2-j.val)=some (beta j) := by
  have hj:=j.isLt
  have d:=d12_lower F r n
  have pos:S < S+z+n+2-j.val:=by omega
  have result:written (frameBase T S z n F r marks beta) (SerializedBody.delimiter F r n 12) (flags a t last) 5 (S+z+n+2-j.val)=some (beta j):=by
    rw [written_outside (Or.inl (show S+z+n+2-j.val ≤ SerializedBody.delimiter F r n 12 by omega))]
    exact base_beta T S z n F r marks beta j
  unfold rowExternal
  by_cases hp:p < S
  · rw [if_pos hp,update,if_neg (by omega)]
    by_cases hm:M < S
    · rw [if_pos hm,update,if_neg (by omega)];exact result
    · rw [if_neg hm];exact result
  · rw [if_neg hp]
    by_cases hm:M < S
    · rw [if_pos hm,update,if_neg (by omega)];exact result
    · rw [if_neg hm];exact result
private theorem external_meta (T : Nat → Option Bool) (S z n F r M p marks : Nat)
    (beta : Fin n → Bool) (a t : Fin 3) (last : Bool) (arena:S+z+n+3 < F) (j : Fin 5) :
    rowExternal T S z n F r M p marks beta a t last (SerializedBody.delimiter F r n 12+1+j.val)=some (flags a t last j) := by
  have d:=d12_lower F r n
  have result:written (frameBase T S z n F r marks beta) (SerializedBody.delimiter F r n 12) (flags a t last) 5 (SerializedBody.delimiter F r n 12+1+j.val)=some (flags a t last j):=
    written_value _ _ _ j
  unfold rowExternal
  by_cases hp:p < S
  · rw [if_pos hp,update,if_neg (by omega)]
    by_cases hm:M < S
    · rw [if_pos hm,update,if_neg (by omega)];exact result
    · rw [if_neg hm];exact result
  · rw [if_neg hp]
    by_cases hm:M < S
    · rw [if_pos hm,update,if_neg (by omega)];exact result
    · rw [if_neg hm];exact result
private theorem external_table_hole (T : Nat → Option Bool) (S z n F r M p marks : Nat)
    (beta : Fin n → Bool) (a t : Fin 3) (last : Bool) (hp:p < S) :
    rowExternal T S z n F r M p marks beta a t last p=none := by
  unfold rowExternal
  simp only [if_pos hp,update,ite_true]
private theorem external_anchor_hole (T : Nat → Option Bool) (S z n F r M p marks : Nat)
    (beta : Fin n → Bool) (a t : Fin 3) (last : Bool) (hm:M < S) (separate:p≠M-1) :
    rowExternal T S z n F r M p marks beta a t last (M-1)=none := by
  unfold rowExternal
  by_cases hp:p < S
  · simp only [if_pos hp,update,if_neg (Ne.symm separate),if_pos hm,ite_true]
  · simp only [if_neg hp,if_pos hm,update,ite_true]
private theorem external_high (T : Nat → Option Bool) (S z n F r M p marks : Nat)
    (beta : Fin n → Bool) (a t : Fin 3) (last : Bool) (i : Nat) (hi:S ≤ i) :
    rowExternal T S z n F r M p marks beta a t last i=
      written (frameBase T S z n F r marks beta) (SerializedBody.delimiter F r n 12) (flags a t last) 5 i := by
  unfold rowExternal
  by_cases hp:p < S
  · rw [if_pos hp,update,if_neg (by omega)]
    by_cases hm:M < S
    · rw [if_pos hm,update,if_neg (by omega)]
    · rw [if_neg hm]
  · rw [if_neg hp]
    by_cases hm:M < S
    · rw [if_pos hm,update,if_neg (by omega)]
    · rw [if_neg hm]
private theorem base_outside (T : Nat → Option Bool) (S z n F r marks : Nat) (beta : Fin n → Bool) (i : Nat)
    (nb:¬(S+z+2 < i ∧ i < S+z+n+3)) (nm:¬(S+z+n+3 < i ∧ i < F))
    (nd:¬(SerializedBody.delimiter F r n 12 < i ∧ i < SerializedBody.delimiter F r n 12+6)) :
    frameBase T S z n F r marks beta i=T i := by
  unfold frameBase
  rw [dif_neg (by omega),if_neg (by omega),if_neg nd]
private theorem external_reg (T : Nat → Option Bool) (S z n F r M p marks : Nat)
    (beta : Fin n → Bool) (a t : Fin 3) (last : Bool) (arena:S+z+n+3 < F)
    (reg:∀ i,S < i → i < S+z+2 → T i=some false) :
    ∀ i,S < i → i < S+z+2 → rowExternal T S z n F r M p marks beta a t last i=some false := by
  intro i lo hi
  have d:=d12_lower F r n
  rw [external_high T S z n F r M p marks beta a t last i (by omega),
    written_outside (Or.inl (show i ≤ SerializedBody.delimiter F r n 12 by omega)),
    base_outside T S z n F r marks beta i (by omega) (by omega) (by omega)]
  exact reg i lo hi
private theorem external_delimiters (T : Nat → Option Bool) (S z n F r M p marks : Nat)
    (beta : Fin n → Bool) (a t : Fin 3) (last : Bool) (arena:S+z+n+3 < F) :
    rowExternal T S z n F r M p marks beta a t last (S+z+2)=T (S+z+2) ∧
    rowExternal T S z n F r M p marks beta a t last (S+z+n+3)=T (S+z+n+3) ∧
    rowExternal T S z n F r M p marks beta a t last F=T F ∧
    rowExternal T S z n F r M p marks beta a t last (SerializedBody.delimiter F r n 12+6)=T (SerializedBody.delimiter F r n 12+6) := by
  have d:=d12_lower F r n
  have atCell (i : Nat) (hi:i=S+z+2 ∨ i=S+z+n+3 ∨ i=F ∨ i=SerializedBody.delimiter F r n 12+6) :
      rowExternal T S z n F r M p marks beta a t last i=T i := by
    have high:S ≤ i:=by rcases hi with h|h|h|h <;> omega
    rw [external_high T S z n F r M p marks beta a t last i high]
    rcases hi with h|h|h|h
    all_goals subst i
    all_goals rw [written_outside (by omega)]
    all_goals exact base_outside T S z n F r marks beta _ (by omega) (by omega) (by omega)
  exact ⟨atCell _ (Or.inl rfl),atCell _ (Or.inr (Or.inl rfl)),atCell _ (Or.inr (Or.inr (Or.inl rfl))),atCell _ (Or.inr (Or.inr (Or.inr rfl)))⟩
private theorem external_marks (T : Nat → Option Bool) (S z n F r M p marks : Nat)
    (beta : Fin n → Bool) (a t : Fin 3) (last : Bool) (_arena:S+z+n+3 < F) :
    ∀ i,S+z+n+3 < i → i < F → rowExternal T S z n F r M p marks beta a t last i=
      if i ≤ S+z+n+3+marks then some true else none := by
  intro i lo hi
  have d:=d12_lower F r n
  rw [external_high T S z n F r M p marks beta a t last i (by omega),
    written_outside (Or.inl (show i ≤ SerializedBody.delimiter F r n 12 by omega))]
  unfold frameBase
  rw [dif_neg (by omega),if_pos (by omega)]
  rw [show S+z+2+n+1=S+z+n+3 by omega]
end PhysicalCallerClosure
