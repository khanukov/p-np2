import PhysicalCallerClosure.RawTarget
import PhysicalCallerClosure.Round
namespace PhysicalCallerClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
open Lean Elab Tactic in
private def checkedA (leaf expected : String) : TacticM Unit := do
  let env ← getEnv
  let n:=(leaf.splitOn ".").foldl Name.str (Name.str (Name.num `_private.FullIngressClosure.Frame 0) "FullIngressClosure")
  let some ci:=env.find? n | throwError "Missing immutable frame constant {n}"
  let actual:=match ci with | .thmInfo _=>"theorem" | .defnInfo _=>"definition" | .inductInfo _=>"inductive" | _=>"other"
  unless actual==expected do throwError "Wrong frame constant kind {n}: {actual}"
  let some i:=env.getModuleIdxFor? n | throwError "No frame owner"
  unless i.toNat<env.header.moduleNames.size do throwError "Frame owner index out of range"
  unless env.header.moduleNames[i]! == `FullIngressClosure.Frame do throwError "Wrong frame owner"
  logInfo m!"ordinary-frame|FullIngressClosure.Frame|{actual}|{n}|{ci.type}"
  closeMainGoal `checkedA (mkConst n (ci.levelParams.map Level.param))
private abbrev InstallerFrame : (R S z n p g W Q : Nat) → (Fin S → Bool) → (Nat → Option Bool) → Prop := by
  run_tac checkedA "InstallerFrame" "inductive"
private def seed (V : Nat → Option Bool) (L n F r : Nat) : Nat → Option Bool :=
  AllArityBitLength.Target.seedImage (RuntimeBitLength.Target.fullImage
    (CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r) L n F r) F r n
private def ready (V : Nat → Option Bool) (L n F r g W : Nat) : Nat → Option Bool :=
  CarryWindow.Target.image (CappedWeight.Target.image (seed V L n F r) L n F r 0 g W 0 0)
    F r n g (bitLength W) 0 0 W
private theorem accepted_frame : ∀ (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true →
    ∀ pr : AcceptedBody.Parsed k,
    contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr →
    ∀ z : Nat,FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z →
    let S:=a+m; let R:=pairLength a m; let B:=FixedRawLengthFence.allocation R
    let n:=pr.2.n; let L:=S+z+2; let F:=FixedRawLengthFence.fencePos R
    let p:=min (9+2*z+2^n) S; let r:=S-p
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let I:=ready V L n F r (n^k+k) (Cursor.Target.W k n)
    p < S → bitLength n ≤ r → Cursor.Target.W k n ≤ r →
    InstallerFrame R S z n p (n^k+k) (Cursor.Target.W k n) (2^n) (Fin.append x w) I ∧
    Cursor.Target.M k n z=p+bitLength (Cursor.Target.W k n)+Cursor.Target.W k n ∧
    SerializedBody.sourceMode (Fin.append x w) (Cursor.Target.M k n z)=
      SerializedBody.sourceMode (Fin.append x w) (p+bitLength (Cursor.Target.W k n)+Cursor.Target.W k n) := by
  run_tac checkedA "accepted_frame" "theorem"
open Lean Elab Tactic in
private def checkedClosure (owner ns : Name) (leaf : String) : TacticM Unit := do
  let env ← getEnv
  let n:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
  let some (.thmInfo ci):=env.find? n | throwError "Missing exact theorem {n}"
  let some i:=env.getModuleIdxFor? n | throwError "Missing owner {n}"
  unless i.toNat<env.header.moduleNames.size do throwError "Owner index out of range"
  unless env.header.moduleNames[i]! == owner do throwError "Wrong owner {n}"
  logInfo m!"ordinary-closure|{owner}|theorem|{n}|{ci.type}"
  closeMainGoal `checkedClosure (mkConst n (ci.levelParams.map Level.param))
private theorem cap_weight : ∀ k n r v2 v3 v4 v5 d,
    CappedWeight.Target.Cap k n r v2 v3 v4 v5 d → r<Cursor.Target.W k n := by
  run_tac checkedClosure `FullWeight.Raw `FullWeight "cap_weight"
private theorem body_injective : ∀ k,Function.Injective (BodyIngress.body k) := by
  run_tac checkedClosure `PhysicalCallerClosure.Embedding `PhysicalCallerClosure "body_injective"
private theorem before_entry_no_done : ∀ {k N B e : Nat} (c : Config (BodyIngress.machine k).stateCount N B)
    (mode : Fin 3),((BodyIngress.machine k).run e c).state=BodyIngress.body k (SerializedBody.entry mode) →
    ∀ u,u ≤ e → ∀ b,((BodyIngress.machine k).run u c).state≠BodyIngress.body k (SerializedBody.done b) := by
  run_tac checkedClosure `PhysicalCallerClosure.Stability `PhysicalCallerClosure "before_entry_no_done"
private theorem raw_clock (k R h t : Nat) (hp:h ≤ 17179869184*(k+1)*(R+1)^6)
    (tp:t ≤ 1073741824*(R+1)^6) : h+t ≤ 34359738368*(k+1)*(R+1)^6 := by
  have units : (R+1)^6 ≤ (k+1)*(R+1)^6:=Nat.le_mul_of_pos_left _ (by omega)
  nlinarith
/-- Actual accepted RAW normal arm through the complete first BODY terminal. -/
theorem raw_first (k : Nat) : RawFirst k := by
  intro a m x w accepted
  obtain ⟨pr,parsed,z,hH,gamma,eofCase,physicalCase⟩:=FullIngressClosure.raw k x w accepted
  refine ⟨pr,parsed,z,hH,gamma,?_⟩
  dsimp only
  intro physical ellFits wFits
  obtain ⟨_fit6,normal⟩:=physicalCase physical
  rcases normal with bad | ⟨ell,normal⟩
  · exact False.elim (by omega)
  rcases normal with normal | cap
  · obtain ⟨_wFits,t,d,e,_tprice,_dprice,_tdprice,_atW,_firstW,_atReady,_firstReady,
      fit,_eprice,total,_src,entry,first,safe⟩:=normal
    let S:=a+m
    let R:=pairLength a m
    let B:=FixedRawLengthFence.allocation R
    let n:=pr.2.n
    let L:=S+z+2
    let F:=FixedRawLengthFence.fencePos R
    let p:=min (9+2*z+2^n) S
    let r:=S-p
    let W:=Cursor.Target.W k n
    let M:=Cursor.Target.M k n z
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let I:=ready V L n F r (n^k+k) W
    let c:=initialConfig (BodyIngress.machine k) B (encodePair x w)
    let handoff:=t+d+e
    have ff:=accepted_frame k x w accepted pr parsed z gamma physical ellFits wFits
    rcases ff with ⟨frame,mExact,_modeExact⟩
    change M=p+bitLength W+W at mExact
    change p<S at physical
    change InstallerFrame R S z n p (n^k+k) W (2^n) (Fin.append x w) I at frame
    rcases frame with ⟨_Rpos,sr,_nr,_pp,gf,wf,ef,positive,arena,sourceCells,eof,reg,sep,
      right,betaCells,marks,gap,fence,_delims,_bank0,_bank1,_bank2,_bank34,_bank5,_fresh⟩
    have eqH : S+z+2+n+1=S+z+n+3:=by omega
    have hh:S+z+2+n+1<tapeLength R B:=by rw [eqH];exact hH
    let initial : Config SerializedBody.machine.stateCount R B:=
      ⟨SerializedBody.entry (SerializedBody.sourceMode (Fin.append x w) M),⟨S+z+2+n+1,hh⟩,
        fun i=>SerializedBody.prepared I S M F r n (n^k+k) W i.val⟩
    change (BodyIngress.machine k).run handoff c=
      ⟨BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode (Fin.append x w) M)),
        ⟨S+z+n+3,hH⟩,fun i=>SerializedBody.prepared I S M F r n (n^k+k) W i.val⟩ at entry
    have handoffRun : (BodyIngress.machine k).run handoff c=BodyIngress.bodyConfig k initial := by
      rw [entry]
      apply Config.ext_parts
      · rfl
      · exact Fin.ext eqH.symm
      · rfl
    have before:=before_entry_no_done c (SerializedBody.sourceMode (Fin.append x w) M)
      (congrArg Config.state handoffRun)
    have physicalSource (i : Nat) (lo : M ≤ i) (hi : i < S) : I i=some ((Fin.append x w) ⟨i,hi⟩):=sourceCells i (by rw [mExact] at lo;omega) hi
    obtain ⟨tt,price,noAccept,early,result⟩:=ambient_body B R S z n r (n^k+k) W M (2^n)
      (Fin.append x w) (fun _=>false) I (Nat.sub_le _ _) sr gf wf ef
      (by change S-min M S≤S-p;rw [mExact];omega)
      positive (by rw [eqH];exact arena) physicalSource eof reg sep
      (by intro j;rw [eqH];exact betaCells j) (by rw [eqH];exact right)
      (by intro i lo hi;rw [eqH] at lo hi;exact marks i lo hi)
      (by intro i lo hi;rw [eqH] at lo;exact gap i lo hi) fence fit hh
    change (∀ u,u ≤ tt → (SerializedBody.machine.run u initial).state≠SerializedBody.machine.accept) at noAccept
    change (∀ u,u<tt → (SerializedBody.machine.run u initial).state≠SerializedBody.machine.reject ∧
      (SerializedBody.machine.run u initial).state≠SerializedBody.done false ∧
      (SerializedBody.machine.run u initial).state≠SerializedBody.done true) at early
    have after (u : Nat) : (BodyIngress.machine k).run (handoff+u) c=
        BodyIngress.bodyConfig k (SerializedBody.machine.run u initial) := by
      rw [UniformTM.run_add,handoffRun,body_run]
    refine ⟨handoff,tt,total,price,raw_clock k R handoff tt total price,entry,first,?_,?_,?_⟩
    · intro u hu bad
      by_cases pre:u<handoff
      · exact (safe u (by omega)).1 bad
      · rw [show u=handoff+(u-handoff) by omega,after] at bad
        exact noAccept (u-handoff) (by omega) (body_injective k bad)
    · intro u hu
      by_cases pre:u<handoff
      · exact ⟨(safe u (by omega)).2,before u (by omega) false,before u (by omega) true⟩
      · have prior:=early (u-handoff) (by omega)
        rw [show u=handoff+(u-handoff) by omega,after]
        exact ⟨fun bad=>prior.1 (body_injective k bad),
          fun bad=>prior.2.1 (body_injective k bad),fun bad=>prior.2.2 (body_injective k bad)⟩
    · dsimp only at result ⊢
      generalize hs : (do
        let (circuit,tail) ← decodeCircuitFull n (bitLength n) (SerializedBody.window (Fin.append x w) M W)
        if circuit.size ≤ n^k+k then some ((circuit.size,Pnp3.Models.Circuit.eval circuit (fun _=>false)),tail) else none)=spec at result ⊢
      cases spec with
      | none=>
        rw [after,result]
        apply Config.ext_parts
        · rfl
        · exact Fin.ext eqH
        · rfl
      | some pair=>
        rcases pair with ⟨⟨size,b⟩,tail⟩
        obtain ⟨consumed,hw,tail,done⟩:=result
        refine ⟨consumed,hw,tail,?_⟩
        rw [after,done]
        apply Config.ext_parts
        · rfl
        · exact Fin.ext eqH
        · rfl
  · obtain ⟨v2,v3,v4,v5,dd,cap,_logical,_leaf⟩:=cap
    have tooLarge:=cap_weight k pr.2.n _ v2 v3 v4 v5 dd cap
    exact False.elim (by omega)
end PhysicalCallerClosure
