import PhysicalCallerClosure.WriteMetaRows
import PhysicalCallerClosure.ResetReady
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
  for (owner,leaves) in [(`PhysicalCallerClosure.Engine,["Node","Path","Grid","Unary","ns","NativeSafe"]),
      (`PhysicalCallerClosure.Compare,["flags"]),(`PhysicalCallerClosure.WriteMeta,["FrontGrid","WriteMetaRows","write_metadata","front_complete"]),
      (`PhysicalCallerClosure.WriteBits,["written","written_outside"]),
      (`PhysicalCallerClosure.ResetTape,["resetTape"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing paid-row term {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong paid-row owner"
      logInfo m!"paid-row-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac select `PhysicalCallerClosure.Engine "Node.mk" "constructor"
private theorem front_mono : ∀ {D T},FrontGrid D T → ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b := by
  run_tac select `PhysicalCallerClosure.WriteMeta "FrontGrid.mono" "theorem"
private theorem reset_ready_path : ∀ (k : Nat) (a : Fin 3) (D : Nat → Nat) (T : Nat → Option Bool)
    (S L H M Q F P r g W : Nat) (source : Fin S → Bool),
    Grid D T → D 0=F+1 → D 13 ≤ P →
    (∀ j,j=0 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 → D (j+1)=D j+r+1) →
    Unary D T 0 g → Unary D T 3 W → g ≤ r → W ≤ r →
    0 < Q → H+Q < F → T H=none → T F=some false →
    (∀ i,H < i → i ≤ H+Q → T i=some true) → (∀ i,H+Q < i → i < F → T i=none) →
    S < L → L < H → T S=none → T L=none →
    (∀ i,S < i → i < L → ∃ b,T i=some b) → (∀ i,L < i → i < H → ∃ b,T i=some b) →
    (∀ i,M ≤ i → ∀ hi:i < S,T i=some (source ⟨i,hi⟩)) →
    (a.val=2 ↔ S ≤ M) → (M < S → 0 < M ∧ T (M-1)=none) →
    ∃ t,t ≤ 1024*(r+1)*(P+1) ∧ Path (callerMachine k) (NativeSafe k) P t
      (node (resetEntry k a) H T)
      (node (evalState k (SerializedBody.entry (SerializedBody.sourceMode source M))) H
        (fun i=>if i=M ∧ i < S then none else resetTape T D g W i)) := by
  run_tac select `PhysicalCallerClosure.ResetReady "reset_ready_path" "theorem"
private abbrev write_343 : ∀ k : Nat,WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,false,false][j.val]!) (ns k 399) (ns k 336) := by
  run_tac select `PhysicalCallerClosure.WriteMetaRows "code_343" "definition"
private abbrev write_408 : ∀ k : Nat,WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,false,false][j.val]!) (ns k 440) (ns k 336) := by
  run_tac select `PhysicalCallerClosure.WriteMetaRows "code_408" "definition"
private abbrev write_449 : ∀ k : Nat,WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,false,false][j.val]!) (ns k 481) (ns k 336) := by
  run_tac select `PhysicalCallerClosure.WriteMetaRows "code_449" "definition"
private abbrev write_812 : ∀ k : Nat,WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,true,false][j.val]!) (ns k 868) (ns k 805) := by
  run_tac select `PhysicalCallerClosure.WriteMetaRows "code_812" "definition"
private abbrev write_877 : ∀ k : Nat,WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,true,false][j.val]!) (ns k 909) (ns k 805) := by
  run_tac select `PhysicalCallerClosure.WriteMetaRows "code_877" "definition"
private abbrev write_918 : ∀ k : Nat,WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,true,false][j.val]!) (ns k 950) (ns k 805) := by
  run_tac select `PhysicalCallerClosure.WriteMetaRows "code_918" "definition"
private abbrev write_1289 : ∀ k : Nat,WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,true,false,false][j.val]!) (ns k 1345) (ns k 1282) := by
  run_tac select `PhysicalCallerClosure.WriteMetaRows "code_1289" "definition"
private abbrev write_1353 : ∀ k : Nat,WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,true,false,false][j.val]!) (ns k 1385) (ns k 1282) := by
  run_tac select `PhysicalCallerClosure.WriteMetaRows "code_1353" "definition"
private abbrev write_1393 : ∀ k : Nat,WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,true,false,false][j.val]!) (ns k 1425) (ns k 1282) := by
  run_tac select `PhysicalCallerClosure.WriteMetaRows "code_1393" "definition"
private def writerEntry (k : Nat) (a t : Fin 3) : Fin (callerMachine k).stateCount:=
  ns k (#[399,440,481,868,909,950,1345,1385,1425][3*a.val+t.val]!)
private theorem writer_code (k : Nat) (a t : Fin 3) :
    Nonempty (WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (flags a t false)
      (writerEntry k a t) (resetEntry k a)) := by
  fin_cases a <;> fin_cases t
  · exact ⟨write_343 k⟩
  · exact ⟨write_408 k⟩
  · exact ⟨write_449 k⟩
  · exact ⟨write_812 k⟩
  · exact ⟨write_877 k⟩
  · exact ⟨write_918 k⟩
  · exact ⟨write_1289 k⟩
  · exact ⟨write_1353 k⟩
  · exact ⟨write_1393 k⟩
private theorem write_reset_path (k : Nat) (a t : Fin 3) (D : Nat → Nat) (T : Nat → Option Bool)
    (S L H M Q F P r g W : Nat) (source : Fin S → Bool)
    (grid:FrontGrid D T) (d0:D 0=F+1) (metaWidth:D 13=D 12+6) (endBlank:T (D 13)=none) (room:D 13 ≤ P)
    (width:∀ j,j=0 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 → D (j+1)=D j+r+1)
    (ug:Unary D T 0 g) (uw:Unary D T 3 W) (hg:g ≤ r) (hw:W ≤ r)
    (positive:0 < Q) (arena:H+Q < F) (th:T H=none) (tf:T F=some false)
    (marks:∀ i,H < i → i ≤ H+Q → T i=some true) (gap:∀ i,H+Q < i → i < F → T i=none)
    (sl:S < L) (lh:L < H) (ts:T S=none) (tl:T L=none)
    (reg:∀ i,S < i → i < L → ∃ b,T i=some b) (beta:∀ i,L < i → i < H → ∃ b,T i=some b)
    (src:∀ i,M ≤ i → ∀ hi:i < S,T i=some (source ⟨i,hi⟩))
    (tag:a.val=2 ↔ S ≤ M) (anchor:M < S → 0 < M ∧ T (M-1)=none) :
    ∃ price,price ≤ 1088*(r+1)*(P+1) ∧ Path (callerMachine k) (NativeSafe k) P price
      (node (writerEntry k a t) H T)
      (node (evalState k (SerializedBody.entry (SerializedBody.sourceMode source M))) H
        (fun i=>if i=M ∧ i < S then none else resetTape (written T (D 12) (flags a t false) 5) D g W i)) := by
  obtain ⟨code⟩:=writer_code k a t
  have write:=write_metadata grid d0 metaWidth endBlank room positive arena th tf marks gap code
  let U:=written T (D 12) (flags a t false) 5
  have gu:Grid D U:=front_complete grid metaWidth endBlank
  have ord:=front_mono grid 0 12 (by decide) le_rfl
  have low (i) (hi:i ≤ D 12) : U i=T i:=written_outside (Or.inl hi)
  have uu (j v) (hj:j < 12) (u:Unary D T j v) : Unary D U j v:=by
    intro i lo hi
    rw [low i (by have h:=front_mono grid (j+1) 12 (by omega) le_rfl;omega)]
    exact u i lo hi
  obtain ⟨c,cp,reset⟩:=reset_ready_path k a D U S L H M Q F P r g W source gu d0 room width
    (uu 0 g (by decide) ug) (uu 3 W (by decide) uw) hg hw positive arena
    (by rw [low H (by omega)];exact th) (by rw [low F (by omega)];exact tf)
    (by intro i lo hi;rw [low i (by omega)];exact marks i lo hi)
    (by intro i lo hi;rw [low i (by omega)];exact gap i lo hi) sl lh
    (by rw [low S (by omega)];exact ts) (by rw [low L (by omega)];exact tl)
    (by intro i lo hi;rw [low i (by omega)];exact reg i lo hi)
    (by intro i lo hi;rw [low i (by omega)];exact beta i lo hi)
    (by intro i lo hi;rw [low i (by omega)];exact src i lo hi) tag
    (by intro phy;obtain ⟨pos,ah⟩:=anchor phy;exact ⟨pos,by rw [low (M-1) (by omega)];exact ah⟩)
  refine ⟨2*(D 12-H)+38+c,?_,write.append reset⟩
  have base:P+1 ≤ (r+1)*(P+1):=Nat.le_mul_of_pos_left _ (by omega)
  have bound:2*(D 12-H)+38 ≤ 64*(P+1):=by omega
  rw [Nat.mul_assoc] at cp ⊢
  omega
end PhysicalCallerClosure
