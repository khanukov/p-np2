import IngressAllocation.RawWeight
import IngressAllocation.GuardedLift
import IngressAllocation.InstallerTrace
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
attribute [local irreducible] UniformTM.run
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("IngressAllocation.RawWeight","IngressAllocation","physical_weight_heads","rawWeight"),
      ("IngressAllocation.GuardedLift","IngressAllocation","lift_guarded_prefix","guardedPrefix"),
      ("IngressAllocation.InstallerTrace","IngressAllocation","installer_heads","installerHeads"),
      ("IngressAllocation.Geometry","IngressAllocation","twelve_fields_bound","twelveBound"),
      ("FullIngressClosure.Frame","FullIngressClosure","accepted_frame","acceptedFrame"),
      ("CarryReadyCompletion.Native","CarryReadyCompletion","complete_frame","completeCarry"),
      ("CarryWindow.Raw","CarryWindow","normalFrame","normalFrame"),
      ("CarryWindow.Geometry","CarryWindow","Banks.blank","bankBlank"),
      ("CarryWindow.Geometry","CarryWindow","Banks.bank1","bankOne"),
      ("FullWeight.Raw","FullWeight","cap_weight","capWeight"),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","actual_cells","actualCells"),
      ("AllArityWorkspace.Runtime","AllArityWorkspace","Cells.arena","arenaCell"),
      ("VirtualLeaf.Raw","VirtualLeaf","width","acceptedWidth"),
      ("VirtualLeaf.Transport","VirtualLeaf","entry_val","entryVal")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique actual ready/installer footprint {mod}/{key}: {found.map Prod.fst}"
private theorem operand_le_weight (k n : Nat) : n^k+k ≤ Cursor.Target.W k n:=by
  have h:=Nat.mul_le_mul_right (n^k+k) (show 1 ≤ bitLength n+4 by omega)
  simpa only [Nat.one_mul,Cursor.Target.W] using h
set_option maxRecDepth 4000 in
private theorem normal_consumer_heads (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true)
    {pr : AcceptedBody.Parsed k}
    (parsed : contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr)
    (z : Nat) (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (physical : min (9+2*z+2^pr.2.n) (a+m) < a+m)
    (ellFits : bitLength pr.2.n ≤ a+m-min (9+2*z+2^pr.2.n) (a+m))
    (wFits : Cursor.Target.W k pr.2.n ≤ a+m-min (9+2*z+2^pr.2.n) (a+m)) :
    ∃ t,Footprint (BodyIngress.machine k) (C:=FixedRawLengthFence.allocation (pairLength a m))
        (encodePair x w) t (12*(pairLength a m+1)^2) ∧
      ∃ mode:Fin 3,((BodyIngress.machine k).run t
        (initialConfig (BodyIngress.machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=
          BodyIngress.body k (SerializedBody.entry mode) := by
  let R:=pairLength a m;let B:=FixedRawLengthFence.allocation R
  let S:=a+m;let n:=pr.2.n;let L:=S+z+2;let F:=3*R+2
  let p:=min (9+2*z+2^n) S;let r:=S-p
  let g:=n^k+k;let W:=Cursor.Target.W k n
  let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
  let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
  let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
  let Y:=RuntimeBitLength.Target.fullImage X L n F r
  let Z:=AllArityBitLength.Target.seedImage Y F r n
  let T:=CappedWeight.Target.image Z L n F r 0 g W 0 0
  let I:=CarryWindow.Target.image T F r n g (bitLength W) 0 0 W
  let c:=initialConfig (BodyIngress.machine k) B (encodePair x w)
  let old:=initialConfig (AllArityCursor.machine k) B (encodePair x w)
  obtain ⟨t,oldHeads,before,outcome⟩:=rawWeight k x w accepted parsed z gamma physical ellFits
  rcases outcome with ⟨_fits,hD2,atW⟩|⟨v2,v3,v4,v5,d0,cap,_⟩
  · have safeReady (u : Nat) (hu : u < t) : ((AllArityCursor.machine k).run u old).state ≠ VirtualLeaf.entry k:=by
      intro bad
      have upper:=before u hu
      rw [bad,entryVal] at upper
      omega
    have safeCuts (u : Nat) (hu : u < t) (j : Nat) (hj : j=430 ∨ j=613) :
        ((AllArityCursor.machine k).run u old).state ≠ IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k (j+93*k)):=by
      intro bad
      have upper:=before u hu
      rw [bad] at upper
      change 288+(j+93*k)%Cursor.stateCount k < 288+430+93*k at upper
      have jbound : j+93*k < Cursor.stateCount k:=by rcases hj with rfl|rfl <;> unfold Cursor.stateCount <;> omega
      rw [Nat.mod_eq_of_lt jbound] at upper
      rcases hj with rfl|rfl <;> omega
    have tx:=guardedPrefix k x w accepted t safeReady safeCuts
    have prefixHeads (u : Nat) (hu : u ≤ t) : ((BodyIngress.machine k).run u c).head.val ≤ 12*(R+1)^2:=by
      rw [tx u hu]
      exact oldHeads u hu
    have width:=acceptedWidth x w accepted parsed
    have cap:=AcceptedBody.strict_capacity x w gamma width
    have rows:=Stream.accepted_rows_fit k x w accepted parsed gamma
    obtain ⟨cells,_short,fresh⟩:=actualCells x w gamma cap rows
    obtain ⟨_legacy,fit⟩:=Cursor.raw_tail_blank x w gamma cap rows
    change F+5*r+n+7 < tapeLength R B at fit
    change ∀ i : Fin (tapeLength R B),F < i.val → V i.val=none at fresh
    have arena : L+n+1+2^n < F:=by
      have h:=arenaCell cells
      change S+z+n+3+2^n < F at h
      dsimp only [L];omega
    have room : L+n+1 < F:=lt_of_le_of_lt (Nat.le_add_right _ _) arena
    have rp : 0 < r:=by change p < S at physical;dsimp only [r];omega
    have gr : g ≤ r:=(operand_le_weight k n).trans wFits
    obtain ⟨banks,whole⟩:=normalFrame V L n F r g W room rp
      (by intro i lo hi;exact fresh ⟨i,lt_of_le_of_lt hi fit⟩ lo)
    obtain ⟨d,_price,atReady,carryHeads,_safe,carryFirst⟩:=completeCarry k R B L n F r g W T room gr wFits
      (bankBlank banks) (bankOne banks) whole fit
    let carry : Config (CarryWindow.machine k).stateCount R B:=
      ⟨CarryWindow.embed k (VirtualLeaf.embed k (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k (430+93*k)))),
        ⟨F+r+n+3,hD2⟩,fun i=>T i.val⟩
    change (CarryWindow.machine k).run d carry=
      ⟨CarryWindow.ready k,⟨F+1,by omega⟩,fun i=>I i.val⟩ at atReady
    have enter : (BodyIngress.machine k).run t c=BodyIngress.config k carry:=by
      rw [tx t le_rfl,atW]
      rfl
    have ct:=BodyIngress.transport carry carryFirst
    have ready : (BodyIngress.machine k).run (t+d) c=
        ⟨BodyIngress.old k (CarryWindow.ready k),⟨F+1,by change F+1 < tapeLength R B;omega⟩,fun i=>I i.val⟩:=by
      rw [UniformTM.run_add,enter,ct d le_rfl,atReady]
      rfl
    have pair : S ≤ R:=by dsimp only [S,R,pairLength];omega
    have nr : n ≤ R:=width.trans pair
    have rr : r ≤ R:=(Nat.sub_le _ _).trans pair
    have envelope : F+5*r+n+7 ≤ 12*(R+1)^2:=by
      dsimp only [F];nlinarith only [nr,rr,Nat.zero_le R,Nat.zero_le (R^2)]
    have toReady (u : Nat) (hu : u ≤ t+d) : ((BodyIngress.machine k).run u c).head.val ≤ 12*(R+1)^2:=by
      by_cases early : u ≤ t
      · exact prefixHeads u early
      · rw [show u=t+(u-t) by omega,UniformTM.run_add,enter,ct (u-t) (by omega)]
        exact (carryHeads (u-t) (by omega)).2.trans envelope
    obtain ⟨frame,_mExact,_modeEq⟩:=acceptedFrame k x w accepted pr parsed z gamma physical ellFits wFits
    have hH : S+z+n+3 < tapeLength R B:=by dsimp only [L] at room;omega
    have hF : F+1 < tapeLength R B:=by omega
    obtain ⟨e,_price,endRun,installHeads,_safe,_first⟩:=installerHeads k (FullIngressClosure.body k)
      R S z n p g W (2^n) (Fin.append x w) I frame hF hH
    have total : (BodyIngress.machine k).run (t+d+e) c=
        ⟨BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode (Fin.append x w) (p+bitLength W+W))),
          ⟨S+z+n+3,hH⟩,fun i=>SerializedBody.prepared I S (p+bitLength W+W) F r n g W i.val⟩:=by
      rw [UniformTM.run_add,ready]
      exact endRun
    refine ⟨t+d+e,?_,SerializedBody.sourceMode (Fin.append x w) (p+bitLength W+W),?_⟩
    · intro u hu
      by_cases early : u ≤ t+d
      · exact toReady u early
      · rw [show u=(t+d)+(u-(t+d)) by omega,UniformTM.run_add,ready]
        have twelve:=twelveBound R r n rr nr (by dsimp only [R,pairLength];omega)
        exact (installHeads (u-(t+d)) (by omega)).2.trans twelve
    · rw [total]
  · exact False.elim (Nat.not_lt_of_ge wFits (capWeight k n r v2 v3 v4 v5 d0 cap))
end IngressAllocation
