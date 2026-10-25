import PhysicalCallerClosure.RoundFrame
import PhysicalCallerClosure.ResetEval
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
  for (owner,leaves) in [(`PhysicalCallerClosure.RoundFrame,["Exterior"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing paid-row term {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong paid-row owner"
      logInfo m!"paid-row-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private abbrev frameType : (T E : Nat → Option Bool) → (S z n F r M p q : Nat) →
    (Fin n → Bool) → (Fin 5 → Bool) → Bool → Bool → Prop := by
  run_tac select `PhysicalCallerClosure.RoundFrame "Exterior" "inductive"
private theorem reset_prepared : ∀ (k : Nat) (a : Fin 3) (N B S z n r g W M Q F : Nat)
    (source : Fin S → Bool) (beta : Fin n → Bool) (T : Nat → Option Bool) (nodes used rem quota : Nat)
    (_hg:g ≤ r) (_hw:W ≤ r) (_positive:0 < Q) (_arena:S+z+n+3+Q < F)
    (_src:∀ i,M ≤ i → ∀ hi:i < S,T i=some (source ⟨i,hi⟩))
    (_eof:T S=none) (_reg:∀ i,S < i → i < S+z+2 → T i=some false) (_left:T (S+z+2)=none)
    (_betaCells:∀ j:Fin n,T (S+z+n+2-j.val)=some (beta j)) (_right:T (S+z+n+3)=none)
    (_marks:∀ i,S+z+n+3 < i → i ≤ S+z+n+3+Q → T i=some true)
    (_gap:∀ i,S+z+n+3+Q < i → i < F → T i=none) (_fence:T F=some false)
    (_endBlank:T (SerializedBody.delimiter F r n 12+6)=none)
    (_metadata:∀ i,SerializedBody.delimiter F r n 12 < i → i < SerializedBody.delimiter F r n 12+6 → ∃ b,T i=some b)
    (_tag:a.val=2 ↔ S ≤ M) (_anchor:M < S → 0 < M ∧ T (M-1)=none)
    (_fit:SerializedBody.delimiter F r n 12+6 < tapeLength N B) (hH:S+z+n+3 < tapeLength N B),
    let U:=SerializedBody.image T F r n g W (S-min M S) nodes used rem quota
    let initial : Config (callerMachine k).stateCount N B:=⟨resetEntry k a,⟨S+z+n+3,hH⟩,fun i=>U i.val⟩
    ∃ t,t ≤ 1024*(r+1)*(SerializedBody.delimiter F r n 12+7) ∧
      (callerMachine k).run t initial=⟨evalState k (SerializedBody.entry (SerializedBody.sourceMode source M)),
        ⟨S+z+n+3,hH⟩,fun i=>SerializedBody.prepared T S M F r n g W i.val⟩ ∧
      (∀ u,u < t → (BodyIngress.machine k).stateCount+7500 ≤ ((callerMachine k).run u initial).state.val) := by run_tac select `PhysicalCallerClosure.ResetFrame "reset_prepared" "theorem"
private theorem native_not_eval (k : Nat) (q : Fin (callerMachine k).stateCount) (s : Fin 7500)
    (bound:(BodyIngress.machine k).stateCount+7500 ≤ q.val) : q≠evalState k s := by
  intro bad
  have values:=congrArg Fin.val bad
  change q.val=(BodyIngress.machine k).stateCount+s.val at values
  have small:=s.isLt
  omega
private theorem row_body (k : Nat) (a : Fin 3) (B R S z n r g W M p q : Nat)
    (source : Fin S → Bool) (beta : Fin n → Bool) (bits : Fin 5 → Bool) (T E : Nat → Option Bool)
    (frame:Exterior T E S z n (FixedRawLengthFence.fencePos R) r M p q beta bits (decide (p < S)) (decide (M < S)))
    (hr:r ≤ S) (hs:S ≤ R) (hg:g ≤ r) (hw:W ≤ r) (he:bitLength n ≤ r) (ha:S-min M S ≤ r)
    (positive:0 < q) (arena:S+z+n+3+q < FixedRawLengthFence.fencePos R) (mp:0 < M)
    (before:M < S → p < M)
    (src:∀ i,M ≤ i → ∀ hi:i < S,T i=some (source ⟨i,hi⟩))
    (eof:T S=none) (reg:∀ i,S < i → i < S+z+2 → T i=some false)
    (left:T (S+z+2)=none) (right:T (S+z+n+3)=none) (fence:T (FixedRawLengthFence.fencePos R)=some false)
    (endBlank:T (SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+6)=none)
    (tag:a.val=2 ↔ S ≤ M)
    (fit:SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+6 < tapeLength R B)
    (hH:S+z+n+3 < tapeLength R B) (nodes used rem quota : Nat) :
    let F:=FixedRawLengthFence.fencePos R
    let c : Config (callerMachine k).stateCount R B:=⟨resetEntry k a,⟨S+z+n+3,hH⟩,
      fun i=>SerializedBody.image E F r n g W (S-min M S) nodes used rem quota i.val⟩
    let word:=SerializedBody.window source M W
    let sem:=do
      let (circuit,tail) ← decodeCircuitFull n (bitLength n) word
      if circuit.size ≤ g then some ((circuit.size,Pnp3.Models.Circuit.eval circuit beta),tail) else none
    ∃ h t,h ≤ 1024*(r+1)*(SerializedBody.delimiter F r n 12+7) ∧ t ≤ 1073741824*(R+1)^6 ∧
      (callerMachine k).run h c=⟨evalState k (SerializedBody.entry (SerializedBody.sourceMode source M)),
        ⟨S+z+n+3,hH⟩,fun i=>SerializedBody.prepared E S M F r n g W i.val⟩ ∧
      (∀ u,u < h+t → ∀ v:Fin 7500,v.val < 4 → ((callerMachine k).run u c).state≠evalState k v) ∧
      match sem with
      | none=>(callerMachine k).run (h+t) c=⟨evalState k SerializedBody.machine.reject,⟨S+z+n+3,hH⟩,
          fun i=>SerializedBody.image E F r n g W (S-min M S) 0 0 0 0 i.val⟩
      | some ((size,b),tail)=>∃ consumed,consumed ≤ W ∧ tail=word.drop consumed ∧
          (callerMachine k).run (h+t) c=⟨evalState k (SerializedBody.done b),⟨S+z+n+3,hH⟩,
            fun i=>SerializedBody.image E F r n g W (S-min M S) size consumed (W-consumed) 0 i.val⟩ := by
  dsimp only
  let F:=FixedRawLengthFence.fencePos R
  let c : Config (callerMachine k).stateCount R B:=⟨resetEntry k a,⟨S+z+n+3,hH⟩,
    fun i=>SerializedBody.image E F r n g W (S-min M S) nodes used rem quota i.val⟩
  rcases frame with ⟨es,ee,er,el,eh,eb,em,ef,metadata,high⟩
  have srcE:∀ i,M ≤ i → ∀ hi:i < S,E i=some (source ⟨i,hi⟩):=by
    intro i lo hi
    rw [es i hi]
    have no:¬((decide (p < S)=true ∧ i=p) ∨ (decide (M < S)=true ∧ i=M-1)):=by
      intro h
      rcases h with ⟨_,eq⟩|⟨_,eq⟩
      · have h:=before (by omega);omega
      · omega
    rw [if_neg no];exact src i lo hi
  have eofE:E S=none:=ee.trans eof
  have regE:∀ i,S < i → i < S+z+2 → E i=some false:=by intro i lo hi;rw [er i lo hi];exact reg i lo hi
  have marksE:∀ i,S+z+n+3 < i → i ≤ S+z+n+3+q → E i=some true:=by
    intro i lo hi
    rw [em i lo (by omega),if_pos hi]
  have gapE:∀ i,S+z+n+3+q < i → i < F → E i=none:=by
    intro i lo hi
    rw [em i (by omega) hi,if_neg (by omega)]
  have metaE:∀ i,SerializedBody.delimiter F r n 12 < i → i < SerializedBody.delimiter F r n 12+6 → ∃ b,E i=some b:=by
    intro i lo hi
    let j:=i-SerializedBody.delimiter F r n 12-1
    have hj:j < 5:=by dsimp only [j];omega
    have pos:SerializedBody.delimiter F r n 12+1+j=i:=by dsimp only [j];omega
    have value:=metadata ⟨j,hj⟩
    rw [pos] at value
    exact ⟨_,value⟩
  have anchorE:M < S → 0 < M ∧ E (M-1)=none:=by
    intro phy
    refine ⟨mp,?_⟩
    rw [es (M-1) (by omega)]
    simp [phy]
  obtain ⟨h,hp,ready,range⟩:=reset_prepared k a R B S z n r g W M q F source beta E nodes used rem quota hg hw
    positive arena srcE eofE regE (el.trans left) eb (eh.trans right) marksE gapE (ef.trans fence)
    ((high _ le_rfl).trans endBlank) metaE tag anchorE fit hH
  have eqH:S+z+2+n+1=S+z+n+3:=by omega
  have hb:S+z+2+n+1 < tapeLength R B:=by rw [eqH];exact hH
  obtain ⟨t,tp,na,first,result⟩:=copied_body k B R S z n r g W M q source beta E hr hs hg hw he ha positive
    (by simpa only [eqH] using arena) srcE eofE regE (el.trans left)
    (by intro j;simpa only [show S+z+2+n+1-1-j.val=S+z+n+2-j.val by omega] using eb j)
    (by simpa only [eqH] using eh.trans right) (by simpa only [eqH] using marksE)
    (by simpa only [eqH] using gapE) (ef.trans fence) (by omega) hb
  simp only [eqH] at na first result
  have transport (v) : (callerMachine k).run (h+v) c=(callerMachine k).run v
      ⟨evalState k (SerializedBody.entry (SerializedBody.sourceMode source M)),⟨S+z+n+3,hH⟩,
        fun i=>SerializedBody.prepared E S M F r n g W i.val⟩:=by rw [UniformTM.run_add,ready]
  refine ⟨h,t,hp,tp,ready,?_,?_⟩
  · intro u hu v hv
    by_cases early:u < h
    · exact native_not_eval k _ v (range u early)
    · rw [show u=h+(u-h) by omega,transport]
      rcases (show v.val=0 ∨ v.val=1 ∨ v.val=2 ∨ v.val=3 by omega) with h0|h1|h2|h3
      · have eq:v=SerializedBody.machine.accept:=Fin.ext h0
        rw [eq];exact na (u-h) (by omega)
      · have eq:v=SerializedBody.machine.reject:=Fin.ext h1
        rw [eq];exact (first (u-h) (by omega)).1
      · have eq:v=SerializedBody.done false:=Fin.ext h2
        rw [eq];exact (first (u-h) (by omega)).2.1
      · have eq:v=SerializedBody.done true:=Fin.ext h3
        rw [eq];exact (first (u-h) (by omega)).2.2
  · rw [transport];exact result
end PhysicalCallerClosure
