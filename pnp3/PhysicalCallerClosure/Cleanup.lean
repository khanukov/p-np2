import PhysicalCallerClosure.WriteMetaRows
import PhysicalCallerClosure.RestoreRows
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
  for (owner,leaves) in [(`PhysicalCallerClosure.Engine,["Node","Path","Grid","ns","NativeSafe","put"]),
      (`PhysicalCallerClosure.Compare,["flags","payEntry","rejectEntry"]),
      (`PhysicalCallerClosure.WriteMeta,["FrontGrid","WriteMetaRows","write_metadata"]),
      (`PhysicalCallerClosure.WriteBits,["written","written_outside"]),
      (`PhysicalCallerClosure.RestoreSource,["RestoreOneRows","RestoreTwoRows","restore_one","restore_two"])] do
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
private abbrev restore_1514 : ∀ k : Nat,RestoreTwoRows (M:=callerMachine k) (Safe:=NativeSafe k) false false (ns k 1514) (ns k 1499) := by
  run_tac select `PhysicalCallerClosure.RestoreRows "code_1514" "definition"
private abbrev restore_2085 : ∀ k : Nat,RestoreTwoRows (M:=callerMachine k) (Safe:=NativeSafe k) false true (ns k 2085) (ns k 1499) := by
  run_tac select `PhysicalCallerClosure.RestoreRows "code_2085" "definition"
private abbrev restore_2219 : ∀ k : Nat,RestoreOneRows (M:=callerMachine k) (Safe:=NativeSafe k) false (ns k 2219) (ns k 1499) := by
  run_tac select `PhysicalCallerClosure.RestoreRows "code_2219" "definition"
private abbrev restore_1751 : ∀ k : Nat,RestoreTwoRows (M:=callerMachine k) (Safe:=NativeSafe k) true false (ns k 1751) (ns k 1499) := by
  run_tac select `PhysicalCallerClosure.RestoreRows "code_1751" "definition"
private abbrev restore_2128 : ∀ k : Nat,RestoreTwoRows (M:=callerMachine k) (Safe:=NativeSafe k) true true (ns k 2128) (ns k 1499) := by
  run_tac select `PhysicalCallerClosure.RestoreRows "code_2128" "definition"
private abbrev restore_2374 : ∀ k : Nat,RestoreOneRows (M:=callerMachine k) (Safe:=NativeSafe k) true (ns k 2374) (ns k 1499) := by
  run_tac select `PhysicalCallerClosure.RestoreRows "code_2374" "definition"
private abbrev restore_1918 : ∀ k : Nat,RestoreOneRows (M:=callerMachine k) (Safe:=NativeSafe k) false (ns k 1918) (ns k 1499) := by
  run_tac select `PhysicalCallerClosure.RestoreRows "code_1918" "definition"
private abbrev restore_2169 : ∀ k : Nat,RestoreOneRows (M:=callerMachine k) (Safe:=NativeSafe k) true (ns k 2169) (ns k 1499) := by
  run_tac select `PhysicalCallerClosure.RestoreRows "code_2169" "definition"
private abbrev restore_1604 : ∀ k : Nat,RestoreTwoRows (M:=callerMachine k) (Safe:=NativeSafe k) false false (ns k 1604) (ns k 1589) := by
  run_tac select `PhysicalCallerClosure.RestoreRows "code_1604" "definition"
private abbrev restore_2767 : ∀ k : Nat,RestoreTwoRows (M:=callerMachine k) (Safe:=NativeSafe k) false true (ns k 2767) (ns k 1589) := by
  run_tac select `PhysicalCallerClosure.RestoreRows "code_2767" "definition"
private abbrev restore_2229 : ∀ k : Nat,RestoreOneRows (M:=callerMachine k) (Safe:=NativeSafe k) false (ns k 2229) (ns k 1589) := by
  run_tac select `PhysicalCallerClosure.RestoreRows "code_2229" "definition"
private abbrev restore_1773 : ∀ k : Nat,RestoreTwoRows (M:=callerMachine k) (Safe:=NativeSafe k) true false (ns k 1773) (ns k 1589) := by
  run_tac select `PhysicalCallerClosure.RestoreRows "code_1773" "definition"
private abbrev restore_2899 : ∀ k : Nat,RestoreTwoRows (M:=callerMachine k) (Safe:=NativeSafe k) true true (ns k 2899) (ns k 1589) := by
  run_tac select `PhysicalCallerClosure.RestoreRows "code_2899" "definition"
private abbrev restore_2384 : ∀ k : Nat,RestoreOneRows (M:=callerMachine k) (Safe:=NativeSafe k) true (ns k 2384) (ns k 1589) := by
  run_tac select `PhysicalCallerClosure.RestoreRows "code_2384" "definition"
private abbrev restore_1936 : ∀ k : Nat,RestoreOneRows (M:=callerMachine k) (Safe:=NativeSafe k) false (ns k 1936) (ns k 1589) := by
  run_tac select `PhysicalCallerClosure.RestoreRows "code_1936" "definition"
private abbrev restore_3027 : ∀ k : Nat,RestoreOneRows (M:=callerMachine k) (Safe:=NativeSafe k) true (ns k 3027) (ns k 1589) := by
  run_tac select `PhysicalCallerClosure.RestoreRows "code_3027" "definition"
private abbrev write_1443 : ∀ k : Nat,WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,false,false][j.val]!) (ns k 1499) ((callerMachine k).reject) := by
  run_tac select `PhysicalCallerClosure.WriteMetaRows "code_1443" "definition"
private abbrev write_1533 : ∀ k : Nat,WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,false,false][j.val]!) (ns k 1589) (ns k 1432) := by
  run_tac select `PhysicalCallerClosure.WriteMetaRows "code_1533" "definition"
private def finishEntry (k : Nat) (done : Bool) : Fin (callerMachine k).stateCount := ns k (if done then 1589 else 1499)
private def finishState (k : Nat) (done : Bool) : Fin (callerMachine k).stateCount := if done then rowsDone k else (callerMachine k).reject
private def cleanupEntry (k : Nat) (done : Bool) (a t : Fin 3) : Fin (callerMachine k).stateCount :=
  ns k ((if done then #[1604,2767,2229,1773,2899,2384,1936,3027,1589]
    else #[1514,2085,2219,1751,2128,2374,1918,2169,1499])[3*a.val+t.val]!)
private def restored (T : Nat → Option Bool) (p anchor : Nat) (a t : Fin 3) : Nat → Option Bool :=
  let U:=if a.val=2 then T else put T anchor (some (decide (a.val=1)))
  if t.val=2 then U else put U p (some (decide (t.val=1)))
private theorem restore_code_one (k : Nat) (done : Bool) (a t : Fin 3)
    (one:(a.val=2 ∧ t.val≠2) ∨ (t.val=2 ∧ a.val≠2)) :
    Nonempty (RestoreOneRows (M:=callerMachine k) (Safe:=NativeSafe k)
      (if a.val=2 then decide (t.val=1) else decide (a.val=1)) (cleanupEntry k done a t) (finishEntry k done)) := by
  fin_cases a <;> fin_cases t <;> cases done <;> dsimp only at one
  · omega
  · omega
  · omega
  · omega
  · exact ⟨restore_2219 k⟩
  · exact ⟨restore_2229 k⟩
  · omega
  · omega
  · omega
  · omega
  · exact ⟨restore_2374 k⟩
  · exact ⟨restore_2384 k⟩
  · exact ⟨restore_1918 k⟩
  · exact ⟨restore_1936 k⟩
  · exact ⟨restore_2169 k⟩
  · exact ⟨restore_3027 k⟩
  · omega
  · omega
private theorem restore_code_two (k : Nat) (done : Bool) (a t : Fin 3) (ha:a.val≠2) (ht:t.val≠2) :
    Nonempty (RestoreTwoRows (M:=callerMachine k) (Safe:=NativeSafe k) (decide (a.val=1)) (decide (t.val=1))
      (cleanupEntry k done a t) (finishEntry k done)) := by
  fin_cases a <;> fin_cases t <;> cases done <;> dsimp only at ha ht
  · exact ⟨restore_1514 k⟩
  · exact ⟨restore_1604 k⟩
  · exact ⟨restore_2085 k⟩
  · exact ⟨restore_2767 k⟩
  · omega
  · omega
  · exact ⟨restore_1751 k⟩
  · exact ⟨restore_1773 k⟩
  · exact ⟨restore_2128 k⟩
  · exact ⟨restore_2899 k⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
  · omega
private theorem finish_code (k : Nat) (done : Bool) :
    Nonempty (WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun _=>false)
      (finishEntry k done) (finishState k done)) := by
  have bits:(fun j:Fin 5=>#[false,false,false,false,false][j.val]!)=(fun _ : Fin 5=>false):=by
    funext j;fin_cases j <;> rfl
  rw [←bits]
  cases done
  · exact ⟨write_1443 k⟩
  · exact ⟨write_1533 k⟩
private theorem cleanup_source (k : Nat) (done : Bool) (a t : Fin 3) (T : Nat → Option Bool)
    (p anchor S L H P : Nat) (sl:S < L) (lh:L < H) (room:H ≤ P)
    (ts:T S=none) (tl:T L=none) (th:T H=none)
    (anchorFacts:a.val≠2 → anchor < S ∧ T anchor=none ∧ ∀ i,anchor < i → i < S → ∃ b,T i=some b)
    (tableFacts:t.val≠2 → p < S ∧ T p=none ∧ ∀ i,p < i → i < S → (a.val=2 ∨ i≠anchor) → ∃ b,T i=some b)
    (order:a.val≠2 → t.val≠2 → p < anchor)
    (reg:∀ i,S < i → i < L → ∃ b,T i=some b)
    (beta:∀ i,L < i → i < H → ∃ b,T i=some b) :
    ∃ price,price ≤ 2*H+7 ∧ Path (callerMachine k) (NativeSafe k) P price
      (node (cleanupEntry k done a t) H T) (node (finishEntry k done) H (restored T p anchor a t)) := by
  by_cases ha:a.val=2
  · by_cases ht:t.val=2
    · have ae:a=⟨2,by decide⟩:=Fin.ext ha
      have te:t=⟨2,by decide⟩:=Fin.ext ht
      subst a;subst t
      cases done <;> exact ⟨0,by omega,Path.nil _ room⟩
    · obtain ⟨code⟩:=restore_code_one k done a t (Or.inl ⟨ha,ht⟩)
      obtain ⟨ps,ph,src⟩:=tableFacts ht
      have path:=restore_one ps sl lh room ph ts tl th (by
        intro i lo hi;exact src i lo hi (Or.inl ha)) reg beta code
      refine ⟨2*(H-p)+6,by omega,?_⟩
      simpa only [restored,if_pos ha,if_neg ht] using path
  · by_cases ht:t.val=2
    · obtain ⟨code⟩:=restore_code_one k done a t (Or.inr ⟨ht,ha⟩)
      obtain ⟨as,ah,src⟩:=anchorFacts ha
      have path:=restore_one as sl lh room ah ts tl th src reg beta code
      refine ⟨2*(H-anchor)+6,by omega,?_⟩
      simpa only [restored,if_neg ha,if_pos ht] using path
    · obtain ⟨code⟩:=restore_code_two k done a t ha ht
      obtain ⟨as,ah,_⟩:=anchorFacts ha
      obtain ⟨ps,ph,src⟩:=tableFacts ht
      have path:=restore_two (order ha ht) as sl lh room ph ah ts tl th (by intro i lo hi ne;exact src i lo hi (Or.inr ne)) reg beta code
      refine ⟨2*(H-p)+7,by omega,?_⟩
      simpa only [restored,if_neg ha,if_neg ht] using path
private theorem front_rise : ∀ {D T},FrontGrid D T → ∀ j,j < 12 → D j < D (j+1) := by
  run_tac select `PhysicalCallerClosure.WriteMeta "FrontGrid.rise" "theorem"
private theorem front_mono : ∀ {D T},FrontGrid D T → ∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b := by
  run_tac select `PhysicalCallerClosure.WriteMeta "FrontGrid.mono" "theorem"
private theorem front_blank : ∀ {D T},FrontGrid D T → ∀ j,j ≤ 12 → T (D j)=none := by
  run_tac select `PhysicalCallerClosure.WriteMeta "FrontGrid.blank" "theorem"
private theorem front_cells : ∀ {D T},FrontGrid D T → ∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b := by
  run_tac select `PhysicalCallerClosure.WriteMeta "FrontGrid.cells" "theorem"
private abbrev frontMk : {D : Nat → Nat} → {T : Nat → Option Bool} →
    (∀ j,j < 12 → D j < D (j+1)) → (∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b) →
    (∀ j,j ≤ 12 → T (D j)=none) →
    (∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b) → FrontGrid D T := by
  run_tac select `PhysicalCallerClosure.WriteMeta "FrontGrid.mk" "constructor"
private theorem cleanup_path (k : Nat) (done : Bool) (a t : Fin 3) (D : Nat → Nat) (T : Nat → Option Bool)
    (p anchor S L H Q F P : Nat) (grid:FrontGrid D T) (d0:D 0=F+1) (width:D 13=D 12+6)
    (endBlank:T (D 13)=none) (room:D 13 ≤ P) (positive:0 < Q) (arena:H+Q < F)
    (sl:S < L) (lh:L < H) (ts:T S=none) (tl:T L=none) (th:T H=none)
    (anchorFacts:a.val≠2 → anchor < S ∧ T anchor=none ∧ ∀ i,anchor < i → i < S → ∃ b,T i=some b)
    (tableFacts:t.val≠2 → p < S ∧ T p=none ∧ ∀ i,p < i → i < S → (a.val=2 ∨ i≠anchor) → ∃ b,T i=some b)
    (order:a.val≠2 → t.val≠2 → p < anchor)
    (reg:∀ i,S < i → i < L → ∃ b,T i=some b) (beta:∀ i,L < i → i < H → ∃ b,T i=some b)
    (tf:T F=some false) (marks:∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap:∀ i,H+Q < i → i < F → T i=none) :
    ∃ price,price ≤ 64*(P+1) ∧ Path (callerMachine k) (NativeSafe k) P price
      (node (cleanupEntry k done a t) H T)
      (node (finishState k done) H (written (restored T p anchor a t) (D 12) (fun _=>false) 5)) := by
  have ord:=front_mono grid 0 12 (by decide) le_rfl
  have hp:H ≤ P:=by omega
  obtain ⟨c,cp,path⟩:=cleanup_source k done a t T p anchor S L H P sl lh hp ts tl th anchorFacts tableFacts order reg beta
  let U:=restored T p anchor a t
  have high (i) (hi:H ≤ i) : U i=T i:=by
    unfold U restored
    by_cases ha:a.val=2
    · rw [if_pos ha]
      by_cases ht:t.val=2
      · rw [if_pos ht]
      · have bound:=(tableFacts ht).1
        rw [if_neg ht,put,if_neg (by omega)]
    · have bound:=(anchorFacts ha).1
      rw [if_neg ha]
      by_cases ht:t.val=2
      · rw [if_pos ht,put,if_neg (by omega)]
      · have pb:=(tableFacts ht).1
        rw [if_neg ht,put,if_neg (by omega),put,if_neg (by omega)]
  have gu:FrontGrid D U:=frontMk (front_rise grid) (front_mono grid) (by
    intro j hj
    rw [high _ (by have h:=front_mono grid 0 j (by omega) hj;omega)]
    exact front_blank grid j hj) (by
    intro j i hj lo hi
    rw [high i (by have h:=front_mono grid 0 j (by omega) (by omega);omega)]
    exact front_cells grid j i hj lo hi)
  obtain ⟨code⟩:=finish_code k done
  have w:=write_metadata gu d0 width (by rw [high _ (by omega)];exact endBlank) room positive arena
    (by rw [high H le_rfl];exact th) (by rw [high F (by omega)];exact tf)
    (by intro i lo hi;rw [high i (by omega)];exact marks i lo hi)
    (by intro i lo hi;rw [high i (by omega)];exact gap i lo hi) code
  refine ⟨c+(2*(D 12-H)+38),by omega,?_⟩
  exact path.append w
end PhysicalCallerClosure
