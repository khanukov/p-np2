import PhysicalCallerClosure.RoundGrid
import PhysicalCallerClosure.PaymentIncrement
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
  for (owner,leaves) in [(`PhysicalCallerClosure.Engine,["Node","Path","Grid","NativeSafe","put"]),
      (`PhysicalCallerClosure.RoundFrame,["Exterior","carry_image"]),
      (`PhysicalCallerClosure.CallerMemory,["update","image_update","written_image"]),
      (`PhysicalCallerClosure.Compare,["flags","payEntry","rejectEntry"]),
      (`PhysicalCallerClosure.WriteBits,["written"]),
      (`PhysicalCallerClosure.PaymentIncrement,["pay_increment","nextRow","overflowRow"]),
      (`PhysicalCallerClosure.RoundGrid,["image_facts"]),(`PhysicalCallerClosure.AssignmentSemantics,["canonical_increment"]),(`PhysicalCallerClosure.ResetImage,["extD"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing paid-row term {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong owner"
      logInfo m!"paid-row-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev node : {M : UniformTM} → Fin M.stateCount → Nat → (Nat → Option Bool) → Node M := by
  run_tac select `PhysicalCallerClosure.Engine "Node.mk" "constructor"
private theorem frame_write : ∀ {T E : Nat → Option Bool} {S z n F r M p q : Nat}
    {beta : Fin n → Bool} {old : Fin 5 → Bool} {th ah : Bool},
    Exterior T E S z n F r M p q beta old th ah → S+z+n+3 < F → ∀ bits : Fin 5 → Bool,
    Exterior T (written E (SerializedBody.delimiter F r n 12) bits 5) S z n F r M p q beta bits th ah := by
  run_tac select `PhysicalCallerClosure.RoundFrame "Exterior.write" "theorem"
private theorem frame_pay : ∀ {T E : Nat → Option Bool} {S z n F r M p q : Nat}
    {beta : Fin n → Bool} {bits : Fin 5 → Bool} {th ah : Bool}
    (_frame:Exterior T E S z n F r M p q beta bits th ah) (_multiple:1 < q)
    (_arena:S+z+n+3+q < F),
    Exterior T (update E (S+z+n+3+q) none) S z n F r M p (q-1) beta bits th ah := by run_tac select `PhysicalCallerClosure.RoundFrame "Exterior.pay" "theorem"
private theorem frame_carry : ∀ {T E : Nat → Option Bool} {S z n F r M p q : Nat}
    {beta beta' : Fin n → Bool} {bits : Fin 5 → Bool} {th ah : Bool}
    (_frame:Exterior T E S z n F r M p q beta bits th ah) (_arena:S+z+n+3 < F)
    (_next:∀ j:Fin n,(Body.inc (List.ofFn beta)).1[j.val]! = beta' j),
    Exterior T (Body.carryTape E (S+z+2) (List.ofFn beta)) S z n F r M p q beta' bits th ah := by run_tac select `PhysicalCallerClosure.RoundFrame "Exterior.carry" "theorem"
private theorem pay_frame (k : Nat) (a t : Fin 3) (T E : Nat → Option Bool)
    (S z n F r g W M p q row nodes used rem quota : Nat)
    (frame:Exterior T E S z n F r M p q (Pnp3.Core.vecOfNat n row) (flags a t false)
      (decide (p < S)) (decide (M < S)))
    (rowBound:row < 2^n) (positive:0 < q) (arena:S+z+n+3+q < F)
    (eof:T S=none) (reg:∀ i,S < i → i < S+z+2 → T i=some false)
    (left:T (S+z+2)=none) (right:T (S+z+n+3)=none) (fence:T F=some false)
    (endBlank:T (SerializedBody.delimiter F r n 12+6)=none) :
    ∃ E' price,price ≤ 2*q+2*n+2*SerializedBody.delimiter F r n 12+46 ∧
      Exterior T E' S z n F r M p (max 1 (q-1))
        (Pnp3.Core.vecOfNat n ((row+1)%(2^n))) (flags a t (decide (q=1)))
        (decide (p < S)) (decide (M < S)) ∧
      Path (callerMachine k) (NativeSafe k) (SerializedBody.delimiter F r n 12+6) price
        (node (payEntry k a t) (S+z+n+3)
          (SerializedBody.image E F r n g W (S-min M S) nodes used rem quota))
        (node (if row+1=2^n then overflowRow k a t else if q=1 then rejectEntry k a t else nextRow k a t)
          (S+z+n+3) (SerializedBody.image E' F r n g W (S-min M S) nodes used rem quota)) := by
  let H:=S+z+n+3
  let L:=S+z+2
  let bs:=List.ofFn (Pnp3.Core.vecOfNat n row)
  let I:=SerializedBody.image E F r n g W (S-min M S) nodes used rem quota
  obtain ⟨grid,_ts,_reg,tl,th,beta,marks,gap,tf,_metadata,_end⟩:=image_facts T E S z n F r g W M p q nodes used rem quota
    _ _ _ _ frame arena eof reg left right fence endBlank
  have digits:Body.Reads I L bs:=by
    intro j hj
    have hn:j < n:=by simpa only [bs,List.length_ofFn] using hj
    have be:=beta ⟨j,hn⟩
    change I (L+bs.length-j)=some (bs[j]!)
    rw [show L+bs.length-j=S+z+n+2-j by simp only [L,bs,List.length_ofFn];omega]
    change I (S+z+n+2-j)=some (Pnp3.Core.vecOfNat n row ⟨j,hn⟩) at be
    rw [be]
    congr 1
    change Pnp3.Core.vecOfNat n row ⟨j,hn⟩=(List.ofFn (Pnp3.Core.vecOfNat n row))[j]!
    rw [getElem!_pos (List.ofFn (Pnp3.Core.vecOfNat n row)) j (by simpa only [List.length_ofFn] using hn),List.getElem_ofFn]
  obtain ⟨price,bound,path⟩:=pay_increment k a t (extD F r n) I H L q F
    (SerializedBody.delimiter F r n 12+6) bs grid rfl rfl le_rfl positive arena
    (by simp only [L,H,bs,List.length_ofFn];omega) tl th tf digits marks gap
  have law : (Body.inc bs).2=decide (row+1=2^n) ∧
      ∀ j:Fin n,(Body.inc bs).1[j.val]! =Pnp3.Core.vecOfNat n ((row+1)%(2^n)) j := by
    exact canonical_increment n row rowBound
  rw [law.1] at path
  dsimp only [I] at path
  have d12:extD F r n 12=SerializedBody.delimiter F r n 12:=rfl
  rw [d12] at bound
  simp only [d12,decide_eq_true_eq] at path
  -- The physical branch decides whether the last token survives; it does not install an operand.
  by_cases one:q=1
  · simp only [if_pos one] at path
    simp only [if_pos one]
    let U:=written E (SerializedBody.delimiter F r n 12) (flags a t true) 5
    have fu:=frame_write frame (by omega) (flags a t true)
    have fc:=frame_carry fu (by omega) law.2
    have count:max 1 (q-1)=q:=by omega
    have bits:flags a t (decide (q=1))=flags a t true:=by simp [one]
    rw [count,bits]
    refine ⟨Body.carryTape U L bs,price,by simp only [bs,List.length_ofFn] at bound;omega,fc,?_⟩
    rw [written_image,carry_image _ F r n g W (S-min M S) nodes used rem quota L bs
      (by simp only [L,bs,List.length_ofFn];omega)] at path
    exact path
  · simp only [if_neg one] at path
    simp only [if_neg one]
    have multiple:1 < q:=by omega
    let U:=update E (H+q) none
    have fu:=frame_pay frame multiple arena
    have fc:=frame_carry fu (by omega) law.2
    have count:max 1 (q-1)=q-1:=by omega
    have bits:flags a t (decide (q=1))=flags a t false:=by simp [one]
    rw [count,bits]
    refine ⟨Body.carryTape U L bs,price,by simp only [bs,List.length_ofFn] at bound;omega,fc,?_⟩
    rw [show put I (H+q) none=SerializedBody.image U F r n g W (S-min M S) nodes used rem quota by
      exact image_update E F r n g W (S-min M S) nodes used rem quota (H+q) none (Or.inl (by change H+q < F+1;omega))] at path
    rw [carry_image _ F r n g W (S-min M S) nodes used rem quota L bs
      (by simp only [L,bs,List.length_ofFn];omega)] at path
    exact path
end PhysicalCallerClosure
