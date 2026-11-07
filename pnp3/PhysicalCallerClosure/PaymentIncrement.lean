import PhysicalCallerClosure.WriteMetaRows
import PhysicalCallerClosure.PaymentRows
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
  for (owner,leaves) in [(`PhysicalCallerClosure.Engine,["Node","Path","Grid","ns","NativeSafe","put"]),
      (`PhysicalCallerClosure.Compare,["flags","payEntry","rejectEntry"]),
      (`PhysicalCallerClosure.WriteMeta,["FrontGrid","WriteMetaRows","write_metadata"]),
      (`PhysicalCallerClosure.WriteBits,["written","written_outside"]),
      (`PhysicalCallerClosure.Payment,["PayRows","payment_path"]),
      (`PhysicalCallerClosure.Assignment,["IncrementRows","increment_path"])] do
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
private theorem grid_rise : ∀ {D T},Grid D T → ∀ j,j < 13 → D j < D (j+1) := by
  run_tac select `PhysicalCallerClosure.Engine "Grid.rise" "theorem"
private theorem grid_mono : ∀ {D T},Grid D T → ∀ a b,a ≤ b → b ≤ 13 → D a ≤ D b := by
  run_tac select `PhysicalCallerClosure.Engine "Grid.mono" "theorem"
private theorem grid_blank : ∀ {D T},Grid D T → ∀ j,j ≤ 13 → T (D j)=none := by
  run_tac select `PhysicalCallerClosure.Engine "Grid.blank" "theorem"
private theorem grid_cells : ∀ {D T},Grid D T → ∀ j i,j < 13 → D j < i → i < D (j+1) → ∃ b,T i=some b := by
  run_tac select `PhysicalCallerClosure.Engine "Grid.cells" "theorem"
private abbrev frontMk : {D : Nat → Nat} → {T : Nat → Option Bool} →
    (∀ j,j < 12 → D j < D (j+1)) → (∀ a b,a ≤ b → b ≤ 12 → D a ≤ D b) →
    (∀ j,j ≤ 12 → T (D j)=none) →
    (∀ j i,j < 12 → D j < i → i < D (j+1) → ∃ b,T i=some b) → FrontGrid D T := by
  run_tac select `PhysicalCallerClosure.WriteMeta "FrontGrid.mk" "constructor"
private theorem front_grid {D T} (g:Grid D T) : FrontGrid D T:=
  frontMk (by intro j hj;exact grid_rise g j (by omega))
    (by intro a b ab hb;exact grid_mono g a b ab (by omega))
    (by intro j hj;exact grid_blank g j (by omega))
    (by intro j i hj lo hi;exact grid_cells g j i (by omega) lo hi)
private abbrev pay_0_0 : ∀ k : Nat,PayRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 1435) (ns k 1606) (ns k 1675) := by
  run_tac select `PhysicalCallerClosure.PaymentRows "code_0_0" "definition"
private abbrev pay_0_1 : ∀ k : Nat,PayRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2743) (ns k 2769) (ns k 2838) := by
  run_tac select `PhysicalCallerClosure.PaymentRows "code_0_1" "definition"
private abbrev pay_0_2 : ∀ k : Nat,PayRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2210) (ns k 2231) (ns k 2300) := by
  run_tac select `PhysicalCallerClosure.PaymentRows "code_0_2" "definition"
private abbrev pay_1_0 : ∀ k : Nat,PayRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 1740) (ns k 1775) (ns k 1844) := by
  run_tac select `PhysicalCallerClosure.PaymentRows "code_1_0" "definition"
private abbrev pay_1_1 : ∀ k : Nat,PayRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2875) (ns k 2901) (ns k 2970) := by
  run_tac select `PhysicalCallerClosure.PaymentRows "code_1_1" "definition"
private abbrev pay_1_2 : ∀ k : Nat,PayRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2365) (ns k 2386) (ns k 2455) := by
  run_tac select `PhysicalCallerClosure.PaymentRows "code_1_2" "definition"
private abbrev pay_2_0 : ∀ k : Nat,PayRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 1909) (ns k 1938) (ns k 2007) := by
  run_tac select `PhysicalCallerClosure.PaymentRows "code_2_0" "definition"
private abbrev pay_2_1 : ∀ k : Nat,PayRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 3007) (ns k 3029) (ns k 3098) := by
  run_tac select `PhysicalCallerClosure.PaymentRows "code_2_1" "definition"
private abbrev pay_2_2 : ∀ k : Nat,PayRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2520) (ns k 2527) (ns k 2596) := by
  run_tac select `PhysicalCallerClosure.PaymentRows "code_2_2" "definition"
private abbrev inc_1606 : ∀ k : Nat,IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 1606) (ns k 1527) (ns k 1604) := by
  run_tac select `PhysicalCallerClosure.AssignmentRows "code_1606" "definition"
private abbrev inc_1611 : ∀ k : Nat,IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 1611) (ns k 1514) (ns k 1604) := by
  run_tac select `PhysicalCallerClosure.AssignmentRows "code_1611" "definition"
private abbrev inc_1775 : ∀ k : Nat,IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 1775) (ns k 1764) (ns k 1773) := by
  run_tac select `PhysicalCallerClosure.AssignmentRows "code_1775" "definition"
private abbrev inc_1780 : ∀ k : Nat,IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 1780) (ns k 1751) (ns k 1773) := by
  run_tac select `PhysicalCallerClosure.AssignmentRows "code_1780" "definition"
private abbrev inc_1938 : ∀ k : Nat,IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 1938) (ns k 1929) (ns k 1936) := by
  run_tac select `PhysicalCallerClosure.AssignmentRows "code_1938" "definition"
private abbrev inc_1943 : ∀ k : Nat,IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 1943) (ns k 1918) (ns k 1936) := by
  run_tac select `PhysicalCallerClosure.AssignmentRows "code_1943" "definition"
private abbrev inc_2231 : ∀ k : Nat,IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2231) (ns k 481) (ns k 2229) := by
  run_tac select `PhysicalCallerClosure.AssignmentRows "code_2231" "definition"
private abbrev inc_2236 : ∀ k : Nat,IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2236) (ns k 2219) (ns k 2229) := by
  run_tac select `PhysicalCallerClosure.AssignmentRows "code_2236" "definition"
private abbrev inc_2386 : ∀ k : Nat,IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2386) (ns k 950) (ns k 2384) := by
  run_tac select `PhysicalCallerClosure.AssignmentRows "code_2386" "definition"
private abbrev inc_2391 : ∀ k : Nat,IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2391) (ns k 2374) (ns k 2384) := by
  run_tac select `PhysicalCallerClosure.AssignmentRows "code_2391" "definition"
private abbrev inc_2527 : ∀ k : Nat,IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2527) (ns k 1425) (ns k 1589) := by
  run_tac select `PhysicalCallerClosure.AssignmentRows "code_2527" "definition"
private abbrev inc_2532 : ∀ k : Nat,IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2532) (ns k 1499) (ns k 1589) := by
  run_tac select `PhysicalCallerClosure.AssignmentRows "code_2532" "definition"
private abbrev inc_2769 : ∀ k : Nat,IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2769) (ns k 2758) (ns k 2767) := by
  run_tac select `PhysicalCallerClosure.AssignmentRows "code_2769" "definition"
private abbrev inc_2774 : ∀ k : Nat,IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2774) (ns k 2085) (ns k 2767) := by
  run_tac select `PhysicalCallerClosure.AssignmentRows "code_2774" "definition"
private abbrev inc_2901 : ∀ k : Nat,IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2901) (ns k 2890) (ns k 2899) := by
  run_tac select `PhysicalCallerClosure.AssignmentRows "code_2901" "definition"
private abbrev inc_2906 : ∀ k : Nat,IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 2906) (ns k 2128) (ns k 2899) := by
  run_tac select `PhysicalCallerClosure.AssignmentRows "code_2906" "definition"
private abbrev inc_3029 : ∀ k : Nat,IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 3029) (ns k 3020) (ns k 3027) := by
  run_tac select `PhysicalCallerClosure.AssignmentRows "code_3029" "definition"
private abbrev inc_3034 : ∀ k : Nat,IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (ns k 3034) (ns k 2169) (ns k 3027) := by
  run_tac select `PhysicalCallerClosure.AssignmentRows "code_3034" "definition"
private abbrev write_1619 : ∀ k : Nat,WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,false,true][j.val]!) (ns k 1675) (ns k 1611) := by
  run_tac select `PhysicalCallerClosure.WriteMetaRows "code_1619" "definition"
private abbrev write_1788 : ∀ k : Nat,WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,false,true,true][j.val]!) (ns k 1844) (ns k 1780) := by
  run_tac select `PhysicalCallerClosure.WriteMetaRows "code_1788" "definition"
private abbrev write_1951 : ∀ k : Nat,WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,false,true,false,true][j.val]!) (ns k 2007) (ns k 1943) := by
  run_tac select `PhysicalCallerClosure.WriteMetaRows "code_1951" "definition"
private abbrev write_2244 : ∀ k : Nat,WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,false,true][j.val]!) (ns k 2300) (ns k 2236) := by
  run_tac select `PhysicalCallerClosure.WriteMetaRows "code_2244" "definition"
private abbrev write_2399 : ∀ k : Nat,WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,false,true,true][j.val]!) (ns k 2455) (ns k 2391) := by
  run_tac select `PhysicalCallerClosure.WriteMetaRows "code_2399" "definition"
private abbrev write_2540 : ∀ k : Nat,WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[true,false,true,false,true][j.val]!) (ns k 2596) (ns k 2532) := by
  run_tac select `PhysicalCallerClosure.WriteMetaRows "code_2540" "definition"
private abbrev write_2782 : ∀ k : Nat,WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,false,true][j.val]!) (ns k 2838) (ns k 2774) := by
  run_tac select `PhysicalCallerClosure.WriteMetaRows "code_2782" "definition"
private abbrev write_2914 : ∀ k : Nat,WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,false,true,true][j.val]!) (ns k 2970) (ns k 2906) := by
  run_tac select `PhysicalCallerClosure.WriteMetaRows "code_2914" "definition"
private abbrev write_3042 : ∀ k : Nat,WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (fun j:Fin 5=>#[false,true,true,false,true][j.val]!) (ns k 3098) (ns k 3034) := by
  run_tac select `PhysicalCallerClosure.WriteMetaRows "code_3042" "definition"
private def incrementEntry (k : Nat) (a t : Fin 3) (last : Bool) : Fin (callerMachine k).stateCount :=
  ns k ((if last then #[1611,2774,2236,1780,2906,2391,1943,3034,2532]
    else #[1606,2769,2231,1775,2901,2386,1938,3029,2527])[3*a.val+t.val]!)
private def lastWriter (k : Nat) (a t : Fin 3) : Fin (callerMachine k).stateCount :=
  ns k (#[1675,2838,2300,1844,2970,2455,2007,3098,2596][3*a.val+t.val]!)
private def nextRow (k : Nat) (a t : Fin 3) : Fin (callerMachine k).stateCount :=
  ns k (#[1527,2758,481,1764,2890,950,1929,3020,1425][3*a.val+t.val]!)
private def overflowRow (k : Nat) (a t : Fin 3) : Fin (callerMachine k).stateCount :=
  ns k (#[1604,2767,2229,1773,2899,2384,1936,3027,1589][3*a.val+t.val]!)
private theorem pay_code (k : Nat) (a t : Fin 3) :
    Nonempty (PayRows (M:=callerMachine k) (Safe:=NativeSafe k) (payEntry k a t) (incrementEntry k a t false) (lastWriter k a t)) := by
  fin_cases a <;> fin_cases t
  · exact ⟨pay_0_0 k⟩
  · exact ⟨pay_0_1 k⟩
  · exact ⟨pay_0_2 k⟩
  · exact ⟨pay_1_0 k⟩
  · exact ⟨pay_1_1 k⟩
  · exact ⟨pay_1_2 k⟩
  · exact ⟨pay_2_0 k⟩
  · exact ⟨pay_2_1 k⟩
  · exact ⟨pay_2_2 k⟩
private theorem inc_code (k : Nat) (a t : Fin 3) (last : Bool) :
    Nonempty (IncrementRows (M:=callerMachine k) (Safe:=NativeSafe k) (incrementEntry k a t last)
      (if last then rejectEntry k a t else nextRow k a t) (overflowRow k a t)) := by
  fin_cases a <;> fin_cases t <;> cases last
  · exact ⟨inc_1606 k⟩
  · exact ⟨inc_1611 k⟩
  · exact ⟨inc_2769 k⟩
  · exact ⟨inc_2774 k⟩
  · exact ⟨inc_2231 k⟩
  · exact ⟨inc_2236 k⟩
  · exact ⟨inc_1775 k⟩
  · exact ⟨inc_1780 k⟩
  · exact ⟨inc_2901 k⟩
  · exact ⟨inc_2906 k⟩
  · exact ⟨inc_2386 k⟩
  · exact ⟨inc_2391 k⟩
  · exact ⟨inc_1938 k⟩
  · exact ⟨inc_1943 k⟩
  · exact ⟨inc_3029 k⟩
  · exact ⟨inc_3034 k⟩
  · exact ⟨inc_2527 k⟩
  · exact ⟨inc_2532 k⟩
private theorem writer_code (k : Nat) (a t : Fin 3) :
    Nonempty (WriteMetaRows (M:=callerMachine k) (Safe:=NativeSafe k) (flags a t true)
      (lastWriter k a t) (incrementEntry k a t true)) := by
  fin_cases a <;> fin_cases t
  · exact ⟨write_1619 k⟩
  · exact ⟨write_2782 k⟩
  · exact ⟨write_2244 k⟩
  · exact ⟨write_1788 k⟩
  · exact ⟨write_2914 k⟩
  · exact ⟨write_2399 k⟩
  · exact ⟨write_1951 k⟩
  · exact ⟨write_3042 k⟩
  · exact ⟨write_2540 k⟩
private theorem pay_increment (k : Nat) (a t : Fin 3) (D : Nat → Nat) (T : Nat → Option Bool)
    (H L Q F P : Nat) (bs : List Bool) (grid:Grid D T)
    (anchor:D 0=F+1) (width:D 13=D 12+6) (room:D 13 ≤ P)
    (positive:0 < Q) (arena:H+Q < F) (lh:L+bs.length+1=H)
    (tl:T L=none) (th:T H=none) (tf:T F=some false) (digits:Body.Reads T L bs)
    (marks:∀ i,H < i → i ≤ H+Q → T i=some true)
    (gap:∀ i,H+Q < i → i < F → T i=none) :
    let U:=if Q=1 then written T (D 12) (flags a t true) 5 else put T (H+Q) none
    ∃ price,price ≤ 2*Q+2*bs.length+2*(D 12-H)+46 ∧
      Path (callerMachine k) (NativeSafe k) P price (node (payEntry k a t) H T)
        (node (if (Body.inc bs).2 then overflowRow k a t else if Q=1 then rejectEntry k a t else nextRow k a t)
          H (Body.carryTape U L bs)) := by
  dsimp only
  have d0:=grid_mono grid 0 13 (by decide) le_rfl
  have ord:=grid_mono grid 0 12 (by decide) (by decide)
  obtain ⟨pc⟩:=pay_code k a t
  have pay:=payment_path T H Q F P _ _ _ pc positive arena (by omega) th tf marks gap
  by_cases one:Q=1
  · simp only [if_pos one] at pay ⊢
    obtain ⟨wc⟩:=writer_code k a t
    have w:=write_metadata (front_grid grid) anchor width (grid_blank grid 13 le_rfl) room positive arena th tf marks gap wc
    let V:=written T (D 12) (flags a t true) 5
    have low (i) (hi:i ≤ H) : V i=T i:=written_outside (Or.inl (by omega))
    have vl:V L=none:=by rw [low L (by omega)];exact tl
    have vh:V H=none:=by rw [low H le_rfl];exact th
    have vd:Body.Reads V L bs:=by
      intro j hj
      have eq:=digits j hj
      rw [low _ (by omega)];exact eq
    obtain ⟨ic⟩:=inc_code k a t true
    obtain ⟨c,cp,ip⟩:=increment_path V L P bs _ _ _ ic (by omega) vl (by rwa [lh]) vd
    rw [lh] at ip
    have whole:=pay.append (w.append ip)
    refine ⟨2*Q+5+(2*(D 12-H)+38+c),?_,?_⟩
    · omega
    · simpa only [if_true,V] using whole
  · simp only [if_neg one] at pay ⊢
    let V:=put T (H+Q) none
    have low (i) (hi:i ≤ H) : V i=T i:=by simp only [V,put,if_neg (show i≠H+Q by omega)]
    have vl:V L=none:=by rw [low L (by omega)];exact tl
    have vh:V H=none:=by rw [low H le_rfl];exact th
    have vd:Body.Reads V L bs:=by
      intro j hj
      rw [low _ (by omega)];exact digits j hj
    obtain ⟨ic⟩:=inc_code k a t false
    obtain ⟨c,cp,ip⟩:=increment_path V L P bs _ _ _ ic (by omega) vl (by rwa [lh]) vd
    rw [lh] at ip
    have whole:=pay.append ip
    refine ⟨2*Q+5+c,?_,?_⟩
    · omega
    · simpa only [if_false,V] using whole
end PhysicalCallerClosure
