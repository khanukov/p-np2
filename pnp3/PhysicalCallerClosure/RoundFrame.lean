import PhysicalCallerClosure.RowTape
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
  for (owner,leaves) in [(`PhysicalCallerClosure.CallerMemory,["frameBase","update","image_inside","caller_image","image_update","written_image"]),
      (`PhysicalCallerClosure.WriteBits,["written","written_outside","written_value"]),
      (`PhysicalCallerClosure.RowTape,["d12_lower","base_low","base_beta","base_outside"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing paid-row term {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong paid-row owner"
      logInfo m!"paid-row-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
-- Only exterior cells are constrained. BODY workspace interiors are supplied by its
-- proved image, not by a new initializer or a prophecy/run field.
private structure Exterior (T E : Nat → Option Bool) (S z n F r M p q : Nat)
    (beta : Fin n → Bool) (bits : Fin 5 → Bool) (tableHole anchorHole : Bool) : Prop where
  source : ∀ i,i < S → E i=if (tableHole=true ∧ i=p) ∨ (anchorHole=true ∧ i=M-1) then none else T i
  eof : E S=T S
  registers : ∀ i,S < i → i < S+z+2 → E i=T i
  left : E (S+z+2)=T (S+z+2)
  right : E (S+z+n+3)=T (S+z+n+3)
  beta : ∀ j:Fin n,E (S+z+n+2-j.val)=some (beta j)
  marks : ∀ i,S+z+n+3 < i → i < F → E i=if i ≤ S+z+n+3+q then some true else none
  fence : E F=T F
  metadata : ∀ j:Fin 5,E (SerializedBody.delimiter F r n 12+1+j.val)=some (bits j)
  high : ∀ i,SerializedBody.delimiter F r n 12+6 ≤ i → E i=T i
private theorem image_outside (T : Nat → Option Bool) (F r n g W a nodes used rem quota i : Nat)
    (out:i < SerializedBody.delimiter F r n 0 ∨ SerializedBody.delimiter F r n 12 < i) :
    SerializedBody.image T F r n g W a nodes used rem quota i=T i := by
  unfold SerializedBody.image
  rw [if_pos out]
private theorem exterior_cleared (T E : Nat → Option Bool) (S z n F r M p q : Nat) (beta : Fin n → Bool)
    (arena:S+z+n+3 < F) (frame:Exterior T E S z n F r M p q beta (fun _=>false) false false) :
    ∀ i,(i < SerializedBody.delimiter F r n 0 ∨ SerializedBody.delimiter F r n 12 < i) →
      E i=frameBase T S z n F r q beta i := by
  intro i out
  have dl:=d12_lower F r n
  rcases out with low|high
  · have leF:i ≤ F:=by change i < F+1 at low;omega
    by_cases isrc:i < S
    · have e:E i=T i:=by simpa using frame.source i isrc
      rw [e,base_low T S z n F r q beta arena i (by omega)]
    · by_cases ieof:i=S
      · subst i
        rw [frame.eof,base_low T S z n F r q beta arena S le_rfl]
      · by_cases ireg:i < (S+z+2)
        · rw [frame.registers i (by omega) ireg,base_outside T S z n F r q beta i (by omega) (by omega) (by omega)]
        · by_cases ileft:i=(S+z+2)
          · subst i
            rw [frame.left,base_outside T S z n F r q beta (S+z+2) (by omega) (by omega) (by omega)]
          · by_cases ibeta:i < (S+z+n+3)
            · let j:=(S+z+n+3)-1-i
              have hj:j < n:=by omega
              have pos:S+z+n+2-j=i:=by omega
              have b:=base_beta T S z n F r q beta ⟨j,hj⟩
              have e:=frame.beta ⟨j,hj⟩
              rw [pos] at b e
              exact e.trans b.symm
            · by_cases iright:i=(S+z+n+3)
              · subst i
                rw [frame.right,base_outside T S z n F r q beta (S+z+n+3) (by omega) (by omega) (by omega)]
              · by_cases ifence:i=F
                · subst i
                  rw [frame.fence,base_outside T S z n F r q beta F (by omega) (by omega) (by omega)]
                · have im:(S+z+n+3) < i ∧ i < F:=by omega
                  rw [frame.marks i im.1 im.2]
                  unfold frameBase
                  rw [dif_neg (show ¬(S+z+2 < i ∧ i < S+z+2+n+1) by omega),if_pos (show S+z+2+n+1 < i ∧ i < F by omega)]
                  rw [show S+z+2+n+1=S+z+n+3 by omega]
  · have dh:(SerializedBody.delimiter F r n 12) < i:=high
    by_cases metaRange:i < (SerializedBody.delimiter F r n 12)+6
    · let j:=i-(SerializedBody.delimiter F r n 12)-1
      have hj:j < 5:=by omega
      have pos:(SerializedBody.delimiter F r n 12)+1+j=i:=by omega
      have e:=frame.metadata ⟨j,hj⟩
      rw [pos] at e
      rw [e]
      unfold frameBase
      rw [dif_neg (by omega),if_neg (by omega),if_pos ⟨dh,metaRange⟩]
    · have hi:(SerializedBody.delimiter F r n 12)+6 ≤ i:=by omega
      rw [frame.high i hi,base_outside T S z n F r q beta i (by omega) (by omega) (by omega)]
private theorem final_image (T E : Nat → Option Bool) (S z n F r g W M p q nodes used rem quota : Nat)
    (beta : Fin n → Bool) (arena:S+z+n+3 < F)
    (frame:Exterior T E S z n F r M p q beta (fun _=>false) false false) :
    SerializedBody.image E F r n g W (S-min M S) nodes used rem quota=
      callerImage T S z n F r g W M q beta nodes used rem quota := by
  rw [caller_image T S z n F r g W M q nodes used rem quota beta arena]
  funext i
  by_cases out:i < SerializedBody.delimiter F r n 0 ∨ SerializedBody.delimiter F r n 12 < i
  · rw [image_outside _ F r n g W (S-min M S) nodes used rem quota i out,
      image_outside _ F r n g W (S-min M S) nodes used rem quota i out]
    exact exterior_cleared T E S z n F r M p q beta arena frame i out
  · exact image_inside _ _ F r n g W (S-min M S) nodes used rem quota i out
private theorem Exterior.write {T E : Nat → Option Bool} {S z n F r M p q : Nat}
    {beta : Fin n → Bool} {old : Fin 5 → Bool} {th ah : Bool}
    (frame:Exterior T E S z n F r M p q beta old th ah) (arena:S+z+n+3 < F) (bits : Fin 5 → Bool) :
    Exterior T (written E (SerializedBody.delimiter F r n 12) bits 5) S z n F r M p q beta bits th ah := by
  have dl:=d12_lower F r n
  have low (i) (hi:i ≤ SerializedBody.delimiter F r n 12) :
      written E (SerializedBody.delimiter F r n 12) bits 5 i=E i:=written_outside (Or.inl hi)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi;rw [low i (by omega)];exact frame.source i hi
  · rw [low S (by omega)];exact frame.eof
  · intro i lo hi;rw [low i (by omega)];exact frame.registers i lo hi
  · rw [low (S+z+2) (by omega)];exact frame.left
  · rw [low (S+z+n+3) (by omega)];exact frame.right
  · intro j
    have hj:=j.isLt
    rw [low (S+z+n+2-j.val) (by omega)];exact frame.beta j
  · intro i lo hi;rw [low i (by omega)];exact frame.marks i lo hi
  · rw [low F (by omega)];exact frame.fence
  · intro j;exact written_value E _ bits j
  · intro i hi;rw [written_outside (Or.inr hi)];exact frame.high i hi
private def clearSource (T E : Nat → Option Bool) (S M p : Nat) : Nat → Option Bool:=
  let U:=if M < S then update E (M-1) (T (M-1)) else E
  if p < S then update U p (T p) else U
private theorem clearSource_high (T E : Nat → Option Bool) (S M p i : Nat) (hi:S ≤ i) :
    clearSource T E S M p i=E i := by
  unfold clearSource
  by_cases hp:p < S
  · rw [if_pos hp,update,if_neg (by omega)]
    by_cases hm:M < S
    · rw [if_pos hm,update,if_neg (by omega)]
    · rw [if_neg hm]
  · rw [if_neg hp]
    by_cases hm:M < S
    · rw [if_pos hm,update,if_neg (by omega)]
    · rw [if_neg hm]
private theorem Exterior.restore {T E : Nat → Option Bool} {S z n F r M p q : Nat}
    {beta : Fin n → Bool} {bits : Fin 5 → Bool}
    (frame:Exterior T E S z n F r M p q beta bits (decide (p < S)) (decide (M < S)))
    (arena:S+z+n+3 < F) :
    Exterior T (clearSource T E S M p) S z n F r M p q beta bits false false := by
  have dl:=d12_lower F r n
  have high (i) (hi:S ≤ i) : clearSource T E S M p i=E i:=clearSource_high T E S M p i hi
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi
    have goal:(if (false=true ∧ i=p) ∨ (false=true ∧ i=M-1) then none else T i)=T i:=by simp
    rw [goal]
    unfold clearSource
    by_cases hp:p < S
    · rw [if_pos hp]
      by_cases ip:i=p
      · subst i;simp [update]
      · rw [update,if_neg ip]
        by_cases hm:M < S
        · rw [if_pos hm]
          by_cases ia:i=M-1
          · subst i;simp [update]
          · rw [update,if_neg ia,frame.source i hi]
            simp [hp,hm,ip,ia]
        · rw [if_neg hm,frame.source i hi]
          simp [hp,hm,ip]
    · rw [if_neg hp]
      by_cases hm:M < S
      · rw [if_pos hm]
        by_cases ia:i=M-1
        · subst i;simp [update]
        · rw [update,if_neg ia,frame.source i hi]
          simp [hp,hm,ia]
      · rw [if_neg hm,frame.source i hi]
        simp [hp,hm]
  · rw [high S le_rfl];exact frame.eof
  · intro i lo hi;rw [high i (by omega)];exact frame.registers i lo hi
  · rw [high (S+z+2) (by omega)];exact frame.left
  · rw [high (S+z+n+3) (by omega)];exact frame.right
  · intro j;have hj:=j.isLt;rw [high (S+z+n+2-j.val) (by omega)];exact frame.beta j
  · intro i lo hi;rw [high i (by omega)];exact frame.marks i lo hi
  · rw [high F (by omega)];exact frame.fence
  · intro j;rw [high _ (by omega)];exact frame.metadata j
  · intro i hi;rw [high i (by omega)];exact frame.high i hi
private theorem Exterior.pay {T E : Nat → Option Bool} {S z n F r M p q : Nat}
    {beta : Fin n → Bool} {bits : Fin 5 → Bool} {th ah : Bool}
    (frame:Exterior T E S z n F r M p q beta bits th ah) (multiple:1 < q)
    (arena:S+z+n+3+q < F) :
    Exterior T (update E (S+z+n+3+q) none) S z n F r M p (q-1) beta bits th ah := by
  let H:=S+z+n+3
  have dl:=d12_lower F r n
  have same (i) (hi:i≠H+q) : update E (H+q) none i=E i:=by simp only [update,if_neg hi]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi;rw [same i (by dsimp only [H];omega)];exact frame.source i hi
  · rw [same S (by dsimp only [H];omega)];exact frame.eof
  · intro i lo hi;rw [same i (by dsimp only [H];omega)];exact frame.registers i lo hi
  · rw [same (S+z+2) (by dsimp only [H];omega)];exact frame.left
  · rw [same (S+z+n+3) (by dsimp only [H];omega)];exact frame.right
  · intro j;have hj:=j.isLt;rw [same _ (by dsimp only [H];omega)];exact frame.beta j
  · intro i lo hi
    by_cases eq:i=H+q
    · subst i
      rw [update,if_pos (show H+q=S+z+n+3+q by rfl)]
      rw [if_neg (show ¬H+q ≤ S+z+n+3+(q-1) by dsimp only [H];omega)]
    · rw [same i eq,frame.marks i lo hi]
      by_cases inside:i ≤ S+z+n+3+(q-1)
      · rw [if_pos (show i ≤ S+z+n+3+q by omega),if_pos inside]
      · rw [if_neg (show ¬i ≤ S+z+n+3+q by dsimp only [H] at eq;omega),if_neg inside]
  · rw [same F (by dsimp only [H];omega)];exact frame.fence
  · intro j;rw [same _ (by dsimp only [H];omega)];exact frame.metadata j
  · intro i hi;rw [same i (by dsimp only [H];omega)];exact frame.high i hi
private theorem Exterior.reads {T E : Nat → Option Bool} {S z n F r M p q : Nat}
    {beta : Fin n → Bool} {bits : Fin 5 → Bool} {th ah : Bool}
    (frame:Exterior T E S z n F r M p q beta bits th ah) : Body.Reads E (S+z+2) (List.ofFn beta) := by
  intro j hj
  have hn:j < n:=by simpa only [List.length_ofFn] using hj
  have pos:S+z+2+(List.ofFn beta).length-j=S+z+n+2-j:=by rw [List.length_ofFn];omega
  rw [pos,frame.beta ⟨j,hn⟩]
  congr 1
  rw [getElem!_pos (List.ofFn beta) j hj,List.getElem_ofFn]
private theorem Exterior.carry {T E : Nat → Option Bool} {S z n F r M p q : Nat}
    {beta beta' : Fin n → Bool} {bits : Fin 5 → Bool} {th ah : Bool}
    (frame:Exterior T E S z n F r M p q beta bits th ah) (arena:S+z+n+3 < F)
    (next:∀ j:Fin n,(Body.inc (List.ofFn beta)).1[j.val]! = beta' j) :
    Exterior T (Body.carryTape E (S+z+2) (List.ofFn beta)) S z n F r M p q beta' bits th ah := by
  let L:=S+z+2
  let H:=S+z+n+3
  have dl:=d12_lower F r n
  have same (i) (hi:i ≤ L ∨ H ≤ i) : Body.carryTape E (S+z+2) (List.ofFn beta) i=E i:=by
    apply Body.carry_frame
    rcases hi with lo|hi
    · exact Or.inl lo
    · right
      rw [List.length_ofFn]
      dsimp only [L,H] at *
      omega
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi;rw [same i (Or.inl (by dsimp only [L];omega))];exact frame.source i hi
  · rw [same S (Or.inl (by dsimp only [L];omega))];exact frame.eof
  · intro i lo hi;rw [same i (Or.inl (by dsimp only [L];omega))];exact frame.registers i lo hi
  · rw [same (S+z+2) (Or.inl le_rfl)];exact frame.left
  · rw [same (S+z+n+3) (Or.inr le_rfl)];exact frame.right
  · intro j
    have hj:j.val < (Body.inc (List.ofFn beta)).1.length:=by rw [Body.inc_length,List.length_ofFn];exact j.isLt
    have value:=Body.carry_reads E L (List.ofFn beta) frame.reads j.val hj
    rw [Body.inc_length,List.length_ofFn] at value
    have pos:L+n-j.val=S+z+n+2-j.val:=by dsimp only [L];omega
    rw [pos] at value
    exact value.trans (congrArg some (next j))
  · intro i lo hi;rw [same i (Or.inr (by dsimp only [H];omega))];exact frame.marks i lo hi
  · rw [same F (Or.inr (by dsimp only [H];omega))];exact frame.fence
  · intro j;rw [same _ (Or.inr (by dsimp only [H];omega))];exact frame.metadata j
  · intro i hi;rw [same i (Or.inr (by dsimp only [H];omega))];exact frame.high i hi
private theorem carry_image (E : Nat → Option Bool) (F r n g W a nodes used rem quota L : Nat) (bs : List Bool)
    (room:L+bs.length < F+1) :
    Body.carryTape (SerializedBody.image E F r n g W a nodes used rem quota) L bs=
      SerializedBody.image (Body.carryTape E L bs) F r n g W a nodes used rem quota := by
  induction bs generalizing E with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | false =>
      change update (SerializedBody.image E F r n g W a nodes used rem quota) (L+bs.length+1) (some true)=
        SerializedBody.image (update E (L+bs.length+1) (some true)) F r n g W a nodes used rem quota
      exact image_update _ F r n g W a nodes used rem quota _ _ (Or.inl (by change L+bs.length+1 < F+1;simp only [List.length_cons] at room;omega))
    | true =>
      change Body.carryTape (update (SerializedBody.image E F r n g W a nodes used rem quota) (L+bs.length+1) (some false)) L bs=
        SerializedBody.image (Body.carryTape (update E (L+bs.length+1) (some false)) L bs) F r n g W a nodes used rem quota
      rw [image_update _ F r n g W a nodes used rem quota _ _ (Or.inl (by change L+bs.length+1 < F+1;simp only [List.length_cons] at room;omega))]
      exact ih _ (by simp only [List.length_cons] at room;omega)
private def shiftSource (T E : Nat → Option Bool) (S p : Nat) : Nat → Option Bool:=
  let U:=if p < S then update E p (T p) else E
  if p+1 < S then update U (p+1) none else U
private theorem shiftSource_high (T E : Nat → Option Bool) (S p i : Nat) (hi:S ≤ i) :
    shiftSource T E S p i=E i := by
  unfold shiftSource
  by_cases hn:p+1 < S
  · rw [if_pos hn,update,if_neg (by omega),if_pos (show p < S by omega),update,if_neg (by omega)]
  · rw [if_neg hn]
    by_cases hp:p < S
    · rw [if_pos hp,update,if_neg (by omega)]
    · rw [if_neg hp]
private theorem Exterior.shift {T E : Nat → Option Bool} {S z n F r M p q : Nat}
    {beta : Fin n → Bool} {bits : Fin 5 → Bool}
    (frame:Exterior T E S z n F r M p q beta bits (decide (p < S)) (decide (M < S)))
    (arena:S+z+n+3 < F) (before:M < S → p+1 < M-1) :
    Exterior T (shiftSource T E S p) S z n F r M (p+1) q beta bits (decide (p+1 < S)) (decide (M < S)) := by
  have dl:=d12_lower F r n
  have high (i) (hi:S ≤ i) : shiftSource T E S p i=E i:=shiftSource_high T E S p i hi
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi
    unfold shiftSource
    by_cases hn:p+1 < S
    · have hp:p < S:=by omega
      rw [if_pos hn]
      by_cases ip:i=p+1
      · subst i
        simp [update,hn]
      · rw [update,if_neg ip,if_pos hp]
        by_cases old:i=p
        · subst i
          rw [update,if_pos rfl]
          simp [hn]
          intro hm eq
          have b:=before hm
          omega
        · rw [update,if_neg old,frame.source i hi]
          simp [hp,hn,ip,old]
    · rw [if_neg hn]
      by_cases hp:p < S
      · rw [if_pos hp]
        by_cases old:i=p
        · subst i
          rw [update,if_pos rfl]
          simp [hn]
          intro hm eq
          have b:=before hm
          omega
        · rw [update,if_neg old,frame.source i hi]
          simp [hp,hn,old]
      · rw [if_neg hp,frame.source i hi]
        simp [hp,hn]
  · rw [high S le_rfl];exact frame.eof
  · intro i lo hi;rw [high i (by omega)];exact frame.registers i lo hi
  · rw [high (S+z+2) (by omega)];exact frame.left
  · rw [high (S+z+n+3) (by omega)];exact frame.right
  · intro j;have hj:=j.isLt;rw [high (S+z+n+2-j.val) (by omega)];exact frame.beta j
  · intro i lo hi;rw [high i (by omega)];exact frame.marks i lo hi
  · rw [high F (by omega)];exact frame.fence
  · intro j;rw [high _ (by omega)];exact frame.metadata j
  · intro i hi;rw [high i (by omega)];exact frame.high i hi
end PhysicalCallerClosure
