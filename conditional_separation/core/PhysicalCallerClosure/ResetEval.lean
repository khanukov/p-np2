import PhysicalCallerClosure.ResetFrame
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion Pnp4.AlgorithmsToLowerBounds Lean Elab Tactic
private def checkedFrame : TacticM Unit := do
  let e←getEnv
  let n:=Name.str (Name.str (Name.num `_private.PhysicalCallerClosure.ResetFrame 0) "PhysicalCallerClosure") "reset_prepared"
  let some (.thmInfo ci):=e.find? n | throwError "Missing exact reset→prepared proof"
  let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
  unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
  unless e.header.moduleNames[i]! == `PhysicalCallerClosure.ResetFrame do throwError "Wrong reset proof owner"
  logInfo m!"reset-eval-adapter|{n}|{ci.type}"
  closeMainGoal `checkedFrame (mkConst n (ci.levelParams.map Level.param))
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
      (∀ u,u < t → (BodyIngress.machine k).stateCount+7500 ≤ ((callerMachine k).run u initial).state.val) := by run_tac checkedFrame
private theorem native_not_eval (k : Nat) (q : Fin (callerMachine k).stateCount) (s : Fin 7500)
    (bound:(BodyIngress.machine k).stateCount+7500 ≤ q.val) : q≠evalState k s := by
  intro bad
  have values:=congrArg Fin.val bad
  change q.val=(BodyIngress.machine k).stateCount+s.val at values
  have small:=s.isLt
  omega
private theorem no_verdict {M : UniformTM} {N B t : Nat} (c : Config M.stateCount N B)
    (na:(M.run t c).state≠M.accept) (nr:(M.run t c).state≠M.reject) :
    ∀ u,u ≤ t → (M.run u c).state≠M.accept ∧ (M.run u c).state≠M.reject := by
  intro u hu
  constructor
  · intro bad
    have fixed:=M.run_accept (M.run u c) bad (t-u)
    rw [←UniformTM.run_add,show u+(t-u)=t by omega] at fixed
    exact na ((congrArg Config.state fixed).trans bad)
  · intro bad
    have fixed:=M.run_reject (M.run u c) bad (t-u)
    rw [←UniformTM.run_add,show u+(t-u)=t by omega] at fixed
    exact nr ((congrArg Config.state fixed).trans bad)
theorem reset_then_body (k : Nat) (a : Fin 3) (B R S z n r g W M Q : Nat)
    (source : Fin S → Bool) (beta : Fin n → Bool) (T : Nat → Option Bool) (nodes used rem quota : Nat)
    (hr:r ≤ S) (hs:S ≤ R) (hg:g ≤ r) (hw:W ≤ r) (he:bitLength n ≤ r) (ha:S-min M S ≤ r)
    (positive:0 < Q) (arena:S+z+n+3+Q < FixedRawLengthFence.fencePos R)
    (src:∀ i,M ≤ i → ∀ hi:i < S,T i=some (source ⟨i,hi⟩))
    (eof:T S=none) (reg:∀ i,S < i → i < S+z+2 → T i=some false) (left:T (S+z+2)=none)
    (betaCells:∀ j:Fin n,T (S+z+n+2-j.val)=some (beta j)) (right:T (S+z+n+3)=none)
    (marks:∀ i,S+z+n+3 < i → i ≤ S+z+n+3+Q → T i=some true)
    (gap:∀ i,S+z+n+3+Q < i → i < FixedRawLengthFence.fencePos R → T i=none)
    (fence:T (FixedRawLengthFence.fencePos R)=some false)
    (endBlank:T (SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+6)=none)
    (metadata:∀ i,SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12 < i →
      i < SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+6 → ∃ b,T i=some b)
    (tag:a.val=2 ↔ S ≤ M) (anchor:M < S → 0 < M ∧ T (M-1)=none)
    (fit:SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+6 < tapeLength R B)
    (hH:S+z+n+3 < tapeLength R B) :
    let F:=FixedRawLengthFence.fencePos R
    let U:=SerializedBody.image T F r n g W (S-min M S) nodes used rem quota
    let initial : Config (callerMachine k).stateCount R B:=⟨resetEntry k a,⟨S+z+n+3,hH⟩,fun i=>U i.val⟩
    let bits:=SerializedBody.window source M W
    let semantics:=do
      let (c,tail) ← decodeCircuitFull n (bitLength n) bits
      if c.size ≤ g then some ((c.size,Pnp3.Models.Circuit.eval c beta),tail) else none
    ∃ h t,h ≤ 1024*(r+1)*(SerializedBody.delimiter F r n 12+7) ∧ t ≤ 1073741824*(R+1)^6 ∧
      (∀ u,u < h+t → ∀ q:Fin 7500,q.val < 4 →
        ((callerMachine k).run u initial).state≠evalState k q) ∧
      match semantics with
      | none=>(callerMachine k).run (h+t) initial=⟨evalState k SerializedBody.machine.reject,⟨S+z+n+3,hH⟩,
          fun i=>SerializedBody.image T F r n g W (S-min M S) 0 0 0 0 i.val⟩
      | some ((size,b),tail)=>∃ consumed,consumed ≤ W ∧ tail=bits.drop consumed ∧
          (callerMachine k).run (h+t) initial=⟨evalState k (SerializedBody.done b),⟨S+z+n+3,hH⟩,
            fun i=>SerializedBody.image T F r n g W (S-min M S) size consumed (W-consumed) 0 i.val⟩ := by
  dsimp only
  let F:=FixedRawLengthFence.fencePos R
  let U:=SerializedBody.image T F r n g W (S-min M S) nodes used rem quota
  let initial : Config (callerMachine k).stateCount R B:=⟨resetEntry k a,⟨S+z+n+3,hH⟩,fun i=>U i.val⟩
  obtain ⟨h,ph,reset,range⟩:=reset_prepared k a R B S z n r g W M Q F source beta T nodes used rem quota
    hg hw positive arena src eof reg left betaCells right marks gap fence endBlank metadata tag anchor fit hH
  have eqH:S+z+2+n+1=S+z+n+3:=by omega
  have hHb:S+z+2+n+1 < tapeLength R B:=by rw [eqH];exact hH
  obtain ⟨t,pt,noAccept,first,result⟩:=copied_body k B R S z n r g W M Q source beta T hr hs hg hw he ha
    positive (by simpa only [eqH] using arena) src eof reg left
    (by intro j;simpa only [show S+z+2+n+1-1-j.val=S+z+n+2-j.val by omega] using betaCells j)
    (by simpa only [eqH] using right) (by simpa only [eqH] using marks) (by simpa only [eqH] using gap)
    fence (by omega) hHb
  simp only [eqH] at noAccept first result
  have transport (v : Nat) : (callerMachine k).run (h+v) initial=
      (callerMachine k).run v ⟨evalState k (SerializedBody.entry (SerializedBody.sourceMode source M)),
        ⟨S+z+n+3,hH⟩,fun i=>SerializedBody.prepared T S M F r n g W i.val⟩ := by
    rw [UniformTM.run_add,reset]
  refine ⟨h,t,ph,pt,?_,?_⟩
  · intro u hu q hq
    by_cases early:u < h
    · exact native_not_eval k _ q (range u early)
    · have eq:u=h+(u-h):=by omega
      rw [eq,transport]
      have vlt:u-h < t:=by omega
      have casesQ:q.val=0 ∨ q.val=1 ∨ q.val=2 ∨ q.val=3:=by omega
      rcases casesQ with hq|hq|hq|hq
      · have qeq:q=SerializedBody.machine.accept:=Fin.ext hq
        rw [qeq];exact noAccept (u-h) (by omega)
      · have qeq:q=SerializedBody.machine.reject:=Fin.ext hq
        rw [qeq];exact (first (u-h) vlt).1
      · have qeq:q=SerializedBody.done false:=Fin.ext hq
        rw [qeq];exact (first (u-h) vlt).2.1
      · have qeq:q=SerializedBody.done true:=Fin.ext hq
        rw [qeq];exact (first (u-h) vlt).2.2
  · rw [transport]
    exact result
#print axioms reset_then_body
end PhysicalCallerClosure
