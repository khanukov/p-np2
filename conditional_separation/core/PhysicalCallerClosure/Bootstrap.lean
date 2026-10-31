import PhysicalCallerClosure.BootstrapCut
import PhysicalCallerClosure.InitialWrite
import PhysicalCallerClosure.InitialFrame
import PhysicalCallerClosure.RoundCost
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
  for (owner,leaves) in [(`PhysicalCallerClosure.Engine,["Node","Path","NativeSafe","embed","put"]),
      (`PhysicalCallerClosure.SourceInitialize,["initial_source","startControl","anchorMode","initialTape","sourceHoles"]),
      (`PhysicalCallerClosure.BootstrapCut,["cut_step"]),(`PhysicalCallerClosure.InitialWrite,["front_image","holes_image"]),
      (`PhysicalCallerClosure.InitialFrame,["initial_frame"]),(`PhysicalCallerClosure.RoundFrame,["Exterior"]),
      (`PhysicalCallerClosure.CallerMemory,["written_image"]),(`PhysicalCallerClosure.WriteBits,["written"]),
      (`PhysicalCallerClosure.WriteMeta,["write_metadata"]),(`PhysicalCallerClosure.WriteReset,["writerEntry","writer_code"]),
      (`PhysicalCallerClosure.Compare,["flags"]),(`PhysicalCallerClosure.ResetFrame,["extD"]),
      (`PhysicalCallerClosure.RowTape,["d12_lower"]),(`PhysicalCallerClosure.RoundCost,["extent_price"])] do
    for leaf in leaves do
      let n:=Name.str (Name.str (Name.num (Name.append `_private owner) 0) "PhysicalCallerClosure") leaf
      let some ci:=e.find? n | throwError "Missing paid-row term {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing owner"
      unless i.toNat < e.header.moduleNames.size do throwError "Owner outside header"
      unless e.header.moduleNames[i]! == owner do throwError "Wrong owner"
      logInfo m!"paid-row-open|{n}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private theorem initial_price (R H A d : Nat) (hd:H ≤ d) (extent:d+7 ≤ 32*(R+1)) :
    1+(2*(H-A)+11+(2*(d-H)+38)) ≤ 4096*(R+1)^2 := by
  have linear:1+(2*(H-A)+11+(2*(d-H)+38)) ≤ 64*(R+1)+50:=by omega
  nlinarith
private theorem bootstrap (k B R S z n r g W M A Q : Nat) (source : Fin S → Bool) (T : Nat → Option Bool)
    (rr:r ≤ R) (a2:2 ≤ A) (aS:A ≤ S) (margin:A+2 ≤ M)
    (positive:0 < Q) (arena:S+z+n+3+Q < FixedRawLengthFence.fencePos R)
    (gamma:T (A-2)=none) (marker:T (A-1)=some true)
    (src:∀ i,A ≤ i → ∀ hi:i < S,T i=some (source ⟨i,hi⟩))
    (eof:T S=none) (reg:∀ i,S < i → i < S+z+2 → T i=some false)
    (left:T (S+z+2)=none) (right:T (S+z+n+3)=none)
    (beta:∀ j:Fin n,T (S+z+n+2-j.val)=some false)
    (marks:∀ i,S+z+n+3 < i → i ≤ S+z+n+3+Q → T i=some true)
    (gap:∀ i,S+z+n+3+Q < i → i < FixedRawLengthFence.fencePos R → T i=none)
    (fence:T (FixedRawLengthFence.fencePos R)=some false)
    (endBlank:T (SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+6)=none)
    (fit:SerializedBody.delimiter (FixedRawLengthFence.fencePos R) r n 12+6 < tapeLength R B)
    (hH:S+z+n+3 < tapeLength R B) :
    let F:=FixedRawLengthFence.fencePos R
    let c : Config (callerMachine k).stateCount R B:=
      ⟨oldState k (BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode source M))),⟨S+z+n+3,hH⟩,
        fun i=>SerializedBody.prepared T S M F r n g W i.val⟩
    ∃ initial E,initial ≤ 4096*(R+1)^2 ∧
      Exterior T E S z n F r M A Q (Pnp3.Core.vecOfNat n 0)
        (flags (anchorMode source M) (SerializedBody.sourceMode source A) false) (decide (A < S)) (decide (M < S)) ∧
      (callerMachine k).run initial c=⟨resetEntry k (anchorMode source M),⟨S+z+n+3,hH⟩,
        fun i=>SerializedBody.image E F r n g W (S-min M S) 0 0 W g i.val⟩ := by
  dsimp only
  let F:=FixedRawLengthFence.fencePos R
  let H:=S+z+n+3
  let L:=S+z+2
  let d:=SerializedBody.delimiter F r n 12
  let P:=d+6
  let I:=SerializedBody.image T F r n g W (S-min M S) 0 0 W g
  let c : Config (callerMachine k).stateCount R B:=
    ⟨oldState k (BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode source M))),⟨H,hH⟩,
      fun i=>SerializedBody.prepared T S M F r n g W i.val⟩
  have dl:=d12_lower F r n
  have low (i) (hi:i ≤ F) : I i=T i:=by
    unfold I SerializedBody.image
    rw [if_pos (Or.inl (show i < SerializedBody.delimiter F r n 0 by change i < F+1;omega))]
  have betaI:∀ i,L < i → i < H → ∃ b,I i=some b:=by
    intro i lo hi
    let j:=S+z+n+2-i
    have hj:j < n:=by dsimp only [L,H,j] at *;omega
    have pos:S+z+n+2-j=i:=by dsimp only [L,H,j] at *;omega
    have b:=beta ⟨j,hj⟩
    rw [pos] at b
    rw [low i (by dsimp only [H] at hi;omega)]
    exact ⟨false,b⟩
  have path:=initial_source k S L H M A P I source a2 margin aS (by dsimp only [L];omega)
    (by dsimp only [L,H];omega) (by dsimp only [P,d,H];omega)
    (by rw [low _ (by omega)];exact gamma) (by rw [low _ (by omega)];exact marker)
    (by intro i lo hi;rw [low i (by omega)];exact src i lo hi)
    (by rw [low S (by omega)];exact eof) (by rw [low L (by dsimp only [L];omega)];exact left)
    (by rw [low H (by dsimp only [H];omega)];exact right)
    (by intro i lo hi;rw [low i (by dsimp only [L] at hi;omega)];exact ⟨false,reg i lo hi⟩) betaI
  have holesEq:=holes_image T S z n F r g W M A (by omega) aS
  let J:=sourceHoles I S M A
  have high (i) (hi:S < i) : J i=I i:=by
    unfold J sourceHoles
    rw [put,if_neg (by omega)]
    by_cases hm:M < S
    · rw [if_pos hm,put,if_neg (by omega)]
    · rw [if_neg hm]
  have grid:=front_image (sourceHoles T S M A) F r n g W (S-min M S) 0 0 W g
  rw [←holesEq] at grid
  obtain ⟨code⟩:=writer_code k (anchorMode source M) (SerializedBody.sourceMode source A)
  have write:=write_metadata grid rfl rfl
    (show J (extD F r n 13)=none from by
      change J (d+6)=none
      rw [high _ (by dsimp only [d];omega)]
      change SerializedBody.image T F r n g W (S-min M S) 0 0 W g (d+6)=none
      unfold SerializedBody.image
      rw [if_pos (Or.inr (show SerializedBody.delimiter F r n 12 < d+6 by dsimp only [d];omega))]
      exact endBlank)
    (show extD F r n 13 ≤ P from le_rfl) positive arena
    (show J H=none from by rw [high H (by dsimp only [H];omega),low H (by dsimp only [H];omega)];exact right)
    (show J F=some false from by rw [high F (by omega),low F le_rfl];exact fence)
    (show ∀ i,H < i → i ≤ H+Q → J i=some true from by intro i lo hi;rw [high i (by dsimp only [H] at lo;omega),low i (by omega)];exact marks i lo hi)
    (show ∀ i,H+Q < i → i < F → J i=none from by intro i lo hi;rw [high i (by dsimp only [H] at lo;omega),low i (by omega)];exact gap i lo hi) code
  have d12:extD F r n 12=d:=rfl
  rw [d12] at write
  have whole:=path.append write
  let E:=written (sourceHoles T S M A) d (flags (anchorMode source M) (SerializedBody.sourceMode source A) false) 5
  have finalTape:written J d (flags (anchorMode source M) (SerializedBody.sourceMode source A) false) 5=
      SerializedBody.image E F r n g W (S-min M S) 0 0 W g:=by
    change written (sourceHoles (SerializedBody.image T F r n g W (S-min M S) 0 0 W g) S M A)
      (SerializedBody.delimiter F r n 12) (flags (anchorMode source M) (SerializedBody.sourceMode source A) false) 5=_
    rw [holesEq,written_image]
  rw [finalTape] at whole
  have inputEq:initialTape I S M=SerializedBody.prepared T S M F r n g W:=by
    unfold initialTape SerializedBody.prepared
    by_cases hm:M < S
    · rw [if_pos hm]
      funext i
      unfold put
      by_cases eq:i=M
      · subst i;simp [hm]
      · rw [if_neg eq,if_neg (by omega)]
    · rw [if_neg hm]
      funext i
      rw [if_neg (by omega)]
  rw [inputEq] at whole
  have nativeRun:=whole.execute fit
  have actual:(callerMachine k).run (2*(H-A)+11+(2*(d-H)+38))
      ⟨startControl k (SerializedBody.sourceMode source M),⟨H,hH⟩,
        fun i=>SerializedBody.prepared T S M F r n g W i.val⟩=
      ⟨resetEntry k (anchorMode source M),⟨H,hH⟩,
        fun i=>SerializedBody.image E F r n g W (S-min M S) 0 0 W g i.val⟩:=by
    simpa only [embed] using nativeRun
  have first:=cut_step k R B (SerializedBody.sourceMode source M) ⟨H,hH⟩
    (fun i=>SerializedBody.prepared T S M F r n g W i.val)
  refine ⟨1+(2*(H-A)+11+(2*(d-H)+38)),E,?_,?_,?_⟩
  · exact initial_price R H A d (by dsimp only [H,d];omega) (extent_price R S z n r Q rr arena)
  · exact initial_frame T S z n F r M A Q _ _ arena aS eof beta marks gap
  · rw [UniformTM.run_add,first,actual]
end PhysicalCallerClosure
