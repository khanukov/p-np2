import RawPrelude.Body
import Complexity.PrivateInterfaceLookupResolvedCarry
namespace RawPrelude
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
set_option maxRecDepth 10000
attribute [local irreducible] UniformTM.run
run_cmd do
  let rows := [("Kernel","Frame"),("Body","computed"),("Body","clear_D2"),("Body","clear_D0"),
      ("Body","clock"),("Body","cleanup_price"),("Body","right_run"),("Body","no_verdict")]
  let validated ← ofExcept (PartAPrivateCarry.batch (← getEnv) (rows.map fun (mod,s) => (PartAPrivateCarry.key ("RawPrelude."++mod), PartAPrivateCarry.key ("RawPrelude."++s))))
  for ((mod,s),target) in rows.zip validated do
    let _ := mod

    let ns := [target]
    logInfo m!"private-term|{ns.head!}"
    modifyScope fun st => {st with openDecls := .explicit ((s.splitOn ".").foldl Name.str Name.anonymous) ns.head! :: st.openDecls}
/-- Same accepted raw run: normal field boundary or actually executed virtual
cleanup. The old EOF tape is retained without six-bank normalization. -/
theorem accepted_prelude (k : Nat) : Target.Raw k := by
  intro a m x w accepted
  obtain ⟨pr,parsed,z,hH,gamma,eof,physical⟩:=FullWeight.accepted_full k x w accepted
  let S:=a+m; let R:=pairLength a m; let B:=FixedRawLengthFence.allocation R
  let n:=pr.2.n; let L:=S+z+2; let F:=FixedRawLengthFence.fencePos R
  let p:=min (9+2*z+2^n) S; let r:=S-p
  let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
  let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
  let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
  let Y:=RuntimeBitLength.Target.fullImage X L n F r
  let Z:=AllArityBitLength.Target.seedImage Y F r n
  let c:=initialConfig (AllArityCursor.machine k) B (encodePair x w)
  refine ⟨pr,parsed,z,hH,gamma,?_,?_⟩
  · intro virtual
    obtain ⟨t,price,logical,done⟩:=eof virtual
    refine ⟨t,clock R k t 0 price (by positivity),logical,done,?_⟩
    exact no_verdict k c t (Or.inr (congrArg Config.state done))
  · intro phys
    change p < S at phys
    obtain ⟨fit,t,price,outcome⟩:=physical phys
    change F+5*r+n+7 < tapeLength R B at fit
    have semantic : contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=true := by
      have h:=accepted
      unfold PartAEndpoint.thresholdContentWitnessRelation PartAEndpoint.contentWitnessRelation at h
      split at h
      · rename_i shape; cases shape; simpa only [AcceptedBody.concat_eq_append] using h
      · contradiction
    have table:=AcceptedBody.table_support k (Fin.append x w) parsed semantic
    have width : n ≤ S := by have lt:=Nat.lt_two_pow_self (n:=n); change 2^n ≤ S at table; omega
    have sr : S ≤ R := by dsimp only [S,R,pairLength]; omega
    have nr : n ≤ R := width.trans sr
    have rr : r ≤ R := (Nat.sub_le S p).trans sr
    have Hval : S+z+2+n+1=S+z+n+3 := by omega
    fromDonor "VirtualReady.Raw" "VirtualReady" "actual_base" =>
      obtain ⟨base,fresh⟩:=OLD x w gamma (AcceptedBody.strict_capacity x w gamma width)
        (Stream.accepted_rows_fit k x w accepted parsed gamma)
    fromDonor "VirtualReady.Raw" "VirtualReady" "Base.arena" => have arena:=OLD base
    change S+z+n+3+2^n < F at arena
    change ∀ i : Fin (tapeLength R B), F < i.val → V i.val=none at fresh
    have room : S+z+n+3 < F := (Nat.le_add_right _ _).trans_lt arena
    have frame : Frame Y L n (2^n) F r := by
      fromDonor "VirtualReady.Raw" "VirtualReady" "computed_frame" =>
        exact OLD V S z n F r base (by
          intro i lo hi
          exact fresh ⟨i,by change i ≤ F+5*r+n+7 at hi; omega⟩ lo)
    have originalFalse (i : Nat) (lo : S+z+2 < i) (hi : i < S+z+n+3) : V i=some false := by
      dsimp only [V,Stream.Target.image]
      rw [if_pos (by change L < i ∧ i < L+n+1; dsimp only [L]; omega),CappedWorkspace.overflow_bits]
      simp [List.getElem!_eq_getElem?_getD,List.getElem?_replicate]
      split_ifs <;> rfl
    have clearPrice:=cleanup_price R n r F (L+n+1) nr rr rfl
    refine ⟨fit,?_⟩
    rcases outcome with ⟨over,logical,start⟩ | ⟨fits,tail⟩
    · have body:=clear_D2 k R B S z n (2^n) F r V frame room originalFalse phys rfl logical fit hH
      have run : (AllArityCursor.machine k).run (t+(F-(L+n+1)+19*r+7*n+48)) c=
          SmallIngress.producer.seqEmbedRight (Cursor.machine k)
            ⟨Cursor.mReady k ⟨2,by decide⟩,⟨S+z+n+3,hH⟩,fun i => Cursor.Target.image V k S n z F i.val⟩ := by
        rw [UniformTM.run_add,start,right_run]
        exact congrArg (SmallIngress.producer.seqEmbedRight (Cursor.machine k)) body
      exact Or.inl ⟨over,logical,t,price,start,clock R k t _ price clearPrice,run,
        no_verdict k c _ (Or.inr (congrArg Config.state run))⟩
    · refine Or.inr ⟨fits,?_⟩
      rcases tail with ⟨wr,start,first⟩ | ⟨v2,v3,v4,v5,d,cap,logical,start,first⟩
      · obtain ⟨dt,hd,dtPrice,body,_localNoVerdict⟩:=PostWeight.prepared_length k x w accepted pr parsed z gamma phys fits wr fit
        have run : (AllArityCursor.machine k).run (t+dt) c=
            SmallIngress.producer.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.q k (613+93*k),⟨F+1,hd⟩,
                fun i => CappedWeight.Target.image Z L n F r (bitLength (Cursor.Target.W k n)) 0 0 (Cursor.Target.W k n) 0 i.val⟩ := by
          rw [UniformTM.run_add,start,right_run]
          exact congrArg (SmallIngress.producer.seqEmbedRight (Cursor.machine k)) body
        exact Or.inl ⟨wr,t,dt,price,dtPrice,start,first,clock R k t dt price dtPrice,run,
          no_verdict k c _ (Or.inl (congrArg Config.state run))⟩
      · have body:=clear_D0 k R B S z n (2^n) F r v2 v3 v4 v5 d V frame room originalFalse phys rfl logical fit hH
        have run : (AllArityCursor.machine k).run (t+(F-(L+n+1)+18*r+6*n+44)) c=
            SmallIngress.producer.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.mReady k ⟨2,by decide⟩,⟨S+z+n+3,hH⟩,fun i => Cursor.Target.image V k S n z F i.val⟩ := by
          rw [UniformTM.run_add,start,right_run]
          exact congrArg (SmallIngress.producer.seqEmbedRight (Cursor.machine k)) body
        have smaller : F-(L+n+1)+18*r+6*n+44 ≤ 524288*(R+1)^3 := by omega
        exact Or.inr ⟨v2,v3,v4,v5,d,cap,logical,t,price,start,first,clock R k t _ price smaller,run,
          no_verdict k c _ (Or.inr (congrArg Config.state run))⟩
end RawPrelude
