import IngressAllocation.RawSeed
import IngressAllocation.WeightTrace
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  let specs := [("IngressAllocation.RawSeed","IngressAllocation","physical_seed_heads","rawSeed"),
    ("IngressAllocation.WeightTrace","IngressAllocation","weight_heads","weightHeads"),
    ("PowerDriver.Raw","PowerDriver","prepared_seed","preparedSeed"),
    ("AllArityWorkspace.Runtime","AllArityWorkspace","actual_cells","actualCells"),
    ("VirtualLeaf.Raw","VirtualLeaf","width","acceptedWidth")]
  let fields := ["arena","source","eof","reg","sep","assn","right","marks","gap","fence"]
  let specs := specs ++ fields.map fun f => ("AllArityWorkspace.Runtime","AllArityWorkspace","Cells."++f,"cell_"++f)
  for (mod,ns,key,aliasName) in specs do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique exact workspace raw interface {mod}/{key}: {found.map Prod.fst}"
set_option maxRecDepth 4000 in
private theorem physical_weight_heads (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true)
    {pr : AcceptedBody.Parsed k}
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (z : Nat) (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (physical : min (9+2*z+2^pr.2.n) (a+m) < a+m)
    (ellFits : bitLength pr.2.n ≤ a+m-min (9+2*z+2^pr.2.n) (a+m)) :
    let S:=a+m;let n:=pr.2.n;let L:=S+z+2;let F:=3*pairLength a m+2
    let r:=S-min (9+2*z+2^n) S
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared (FixedRawLengthFence.allocation (pairLength a m)) x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
    let Y:=RuntimeBitLength.Target.fullImage X L n F r
    let Z:=AllArityBitLength.Target.seedImage Y F r n
    let c:=initialConfig (AllArityCursor.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
    ∃ t,Footprint (AllArityCursor.machine k) (C:=FixedRawLengthFence.allocation (pairLength a m))
        (encodePair x w) t (12*(pairLength a m+1)^2) ∧
      (∀ u,u < t → ((AllArityCursor.machine k).run u c).state.val < 288+430+93*k) ∧
      ((Cursor.Target.W k n ≤ r ∧ ∃ h : F+r+n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)),
        (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
          ⟨Cursor.q k (430+93*k),⟨F+r+n+3,h⟩,
            fun i=>CappedWeight.Target.image Z L n F r 0 (n^k+k) (Cursor.Target.W k n) 0 0 i.val⟩) ∨
       ∃ v2 v3 v4 v5 d,CappedWeight.Target.Cap k n r v2 v3 v4 v5 d ∧
        ∃ h : F+1 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)),
        (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
          ⟨Cursor.q k (798+93*k),⟨F+1,h⟩,
            fun i=>CappedWeight.Target.image Z L n F r v2 v3 v4 v5 d i.val⟩) := by
  let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
  let S:=a+m;let n:=pr.2.n;let L:=S+z+2;let F:=3*R+2
  let p:=min (9+2*z+2^n) S;let r:=S-p
  let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
  let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
  let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
  let Y:=RuntimeBitLength.Target.fullImage X L n F r
  let Z:=AllArityBitLength.Target.seedImage Y F r n
  let c:=initialConfig (AllArityCursor.machine k) B (encodePair x w)
  obtain ⟨t,h,atSeed,seedHeads,seedControl⟩:=rawSeed k x w accepted parsed z gamma physical
  have fits : bitLength n ≤ r:=ellFits
  change (if bitLength n ≤ r then F+2*r+n+4 else F+r+n+3) < tapeLength R B at h
  change (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
    ⟨Cursor.q k (if bitLength n ≤ r then 329 else if (r+1)%2=1 then 250 else 304),
      ⟨if bitLength n ≤ r then F+2*r+n+4 else F+r+n+3,h⟩,
      fun i=>(if bitLength n ≤ r then Z else Y) i.val⟩ at atSeed
  have seed : (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
      ⟨Cursor.q k 329,⟨F+2*r+n+4,by simpa only [if_pos fits] using h⟩,fun i=>Z i.val⟩:=by
    simpa only [if_pos fits] using atSeed
  have width:=acceptedWidth x w accepted parsed
  have cap:=AcceptedBody.strict_capacity x w gamma width
  have rows:=Stream.accepted_rows_fit k x w accepted parsed gamma
  obtain ⟨cf,_short,fresh⟩:=actualCells x w gamma cap rows
  obtain ⟨_legacy,fit⟩:=Cursor.raw_tail_blank x w gamma cap rows
  change F+5*r+n+7 < tapeLength R B at fit
  change ∀ i : Fin (tapeLength R B),F < i.val → V i.val=none at fresh
  have arena : L+n+1+2^n < F:=by
    have h:=cell_arena cf
    change S+z+n+3+2^n < F at h
    dsimp only [L];omega
  have rp : 0 < r:=by change p < S at physical;dsimp only [r];omega
  have frame:=preparedSeed L n (2^n) F r V rp fits (by positivity) arena
    (cell_sep cf) (by rw [show L+n+1=S+z+n+3 by dsimp only [L];omega];exact cell_right cf)
    (by
      intro i lo hi
      exact cell_marks cf i (by change S+z+n+3 < i;dsimp only [L] at lo;omega)
        (by change i ≤ S+z+n+3+2^n;dsimp only [L] at hi;omega))
    (by intro i lo hi;exact cell_gap cf i (by change S+z+n+3+2^n < i;dsimp only [L] at lo;omega) hi)
    (cell_fence cf) (by intro i lo hi;exact fresh ⟨i,lt_of_le_of_lt hi fit⟩ lo)
  obtain ⟨d,phaseHeads,phaseBefore,outcome⟩:=weightHeads k R B L n (2^n) F r Z frame rp fits fit
  have replay (s : Nat) (config : Config (Cursor.machine k).stateCount R B) :
      (AllArityCursor.machine k).run s (SmallIngress.producer.seqEmbedRight (Cursor.machine k) config)=
      SmallIngress.producer.seqEmbedRight (Cursor.machine k) ((Cursor.machine k).run s config):=by
    change (SmallIngress.producer.seq (Cursor.machine k)).run s _=_
    rw [UniformTM.seq_run_right]
  have pair : S ≤ R:=by dsimp only [S,R,pairLength];omega
  have nr : n ≤ R:=width.trans pair
  have rr : r ≤ R:=(Nat.sub_le _ _).trans pair
  have envelope : F+5*r+n+7 ≤ 12*(R+1)^2:=by
    dsimp only [F];nlinarith only [nr,rr,Nat.zero_le R,Nat.zero_le (R^2)]
  refine ⟨t+d,?_,?_,?_⟩
  · intro u hu
    by_cases early : u ≤ t
    · exact seedHeads u early
    · rw [show u=t+(u-t) by omega,UniformTM.run_add,seed,replay]
      exact (phaseHeads (u-t) (by omega)).trans envelope
  · intro u hu
    by_cases early : u ≤ t
    · exact (seedControl u early).trans_lt (by omega)
    · rw [show u=t+(u-t) by omega,UniformTM.run_add,seed,replay]
      change 288+_ < 288+430+93*k
      exact (Nat.add_lt_add_left (phaseBefore (u-t) (by omega)) 288).trans_le (by omega)
  · rcases outcome with ⟨wr,run⟩|⟨v2,v3,v4,v5,d0,fullCap,run⟩
    · refine Or.inl ⟨wr,by change F+r+n+3 < tapeLength R B;omega,?_⟩
      rw [UniformTM.run_add,seed,replay,run]
    · refine Or.inr ⟨v2,v3,v4,v5,d0,fullCap,by change F+1 < tapeLength R B;omega,?_⟩
      rw [UniformTM.run_add,seed,replay,run]
end IngressAllocation
