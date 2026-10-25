import FullFinalClosure.Control
namespace FullFinalClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
set_option autoImplicit false
set_option maxRecDepth 512
set_option maxHeartbeats 200000
run_cmd do
  let e←getEnv
  for (owner,ns,leaf,aliasName,kind) in [
    (`PhysicalCallerClosure.AllRows,`PhysicalCallerClosure,"Layout","Layout","inductive"),
    (`PhysicalCallerClosure.AllRows,`PhysicalCallerClosure,"Layout.mk","layoutMk","constructor"),
    (`RawCallerClosure.Frame,`RawCallerClosure,"normal_layout","normalLayout","theorem"),
    (`RawCallerClosure.RowsRun,`RawCallerClosure,"rows_run","rowsRun","theorem"),
    (`RawCallerClosure.Work,`RawCallerClosure,"caller_injective","callerInj","theorem"),
    (`RawCallerClosure.Work,`RawCallerClosure,"caller_accept","callerAccept","theorem"),
    (`PhysicalCallerClosure.BootstrapCut,`PhysicalCallerClosure,"cut_ne","cutSafe","theorem"),
    (`NormalFinalClosure.Prefix,`NormalFinalClosure,"map_run","mapRun","theorem"),
    (`NormalFinalClosure.Prefix2,`NormalFinalClosure,"rowsOld","rowsOld","theorem"),
    (`NormalFinalClosure.Driver2,`NormalFinalClosure,"old_injective","oldInj","theorem"),
    (`NormalFinalClosure.Driver2,`NormalFinalClosure,"accept_map","acceptMap","theorem"),
    (`NormalFinalClosure.Driver2,`NormalFinalClosure,"reject_map","rejectMap","theorem"),
    (`NormalFinalClosure.Driver2,`NormalFinalClosure,"normalReject","normalReject","theorem"),
    (`NormalFinalClosure.Driver2,`NormalFinalClosure,"doneResult","doneResult","theorem"),
    (`NormalFinalClosure.Driver2,`NormalFinalClosure,"safe_not_old","safeNotOld","theorem"),
    (`NormalFinalClosure.Driver2,`NormalFinalClosure,"raw_room","rawRoom","theorem"),
    (`NormalFinalClosure.RawFrameN2,`NormalFinalClosure,"normalImage","normalImage","definition"),
    (`NormalFinalClosure.RawFrameN2,`NormalFinalClosure,"frame_at_N","frameAtN","theorem"),
    (`NormalFinalClosure.RawComposition2,`NormalFinalClosure,"compose_guard","composeGuard","theorem"),
    (`NormalFinalClosure.RawComposition2,`NormalFinalClosure,"min_lt_implies","minLt","theorem"),
    (`NormalFinalClosure.RawComposition2,`NormalFinalClosure,"recovered_position","recovered","theorem"),
    (`NormalFinalClosure.Arithmetic,`NormalFinalClosure,"guard_price","guardPrice","theorem"),
    (`NormalFinalClosure.Arithmetic,`NormalFinalClosure,"delimiter_bound","delimiterBound","theorem"),
    (`NormalFinalClosure.Frame2,`NormalFinalClosure,"D","D","definition")] do
    let n:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
    let some ci:=e.find? n | throwError "Missing exact prepared NORMAL interface {n}"
    let actual:=match ci with | .thmInfo _=>"theorem"|.defnInfo _=>"definition"|.inductInfo _=>"inductive"|.ctorInfo _=>"constructor"|_=>"other"
    unless actual==kind do throwError "Wrong prepared NORMAL kind {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing prepared NORMAL owner"
    unless e.header.moduleNames[i]! == owner do throwError "Wrong prepared NORMAL owner"
    logInfo m!"registered-interface|{owner}|{n}|{actual}|{(repr ci.type).pretty 1000000000}"
    modifyScope fun s=>{s with openDecls:=.explicit (Name.str .anonymous aliasName) n::s.openDecls}
/-- Generic ambient prepared execution. This consumes the actual ABI and runs
all rows, including every malformed BODY and final prefix/padding rejection. -/
private theorem prepared_final (k N B a m n z : Nat) (x : Bitstring a) (w : Bitstring m)
    (same:pairLength a m=N) (length:m=a+1)
    (tag:FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (header:contentHeader? (Fin.append x w)=some (n,2*z+1))
    (capacity:n < FixedRawLengthFence.capacity a m z)
    (arena:a+m+z+n+3+2^n < FixedRawLengthFence.fencePos N)
    (physical:min (9+2*z+2^n) (a+m) < a+m)
    (ell:bitLength n ≤ a+m-min (9+2*z+2^n) (a+m))
    (window:Cursor.Target.W k n ≤ a+m-min (9+2*z+2^n) (a+m))
    (budget:RawCallerClosure.allocation k N ≤ B)
    (hH:a+m+z+n+3 < tapeLength N B) :
    let S:=a+m;let F:=FixedRawLengthFence.fencePos N;let r:=S-min (9+2*z+2^n) S
    let W:=Cursor.Target.W k n;let address:=Cursor.Target.M k n z
    let I:=normalBase k N x w z n
    let body:Config (NormalFinalClosure.machine2 k).stateCount N B:=
      ⟨entryB k (SerializedBody.sourceMode (Fin.append x w) address),⟨S+z+n+3,hH⟩,
        fun i=>SerializedBody.prepared I S address F r n (n^k+k) W i.val⟩
    ∃ t,t ≤ 17592186044416*(k+1)*(N+1)^8 ∧
      (∀ u,u<t → ((NormalFinalClosure.machine2 k).run u body).state≠(NormalFinalClosure.machine2 k).accept ∧
        ((NormalFinalClosure.machine2 k).run u body).state≠(NormalFinalClosure.machine2 k).reject) ∧
      ((NormalFinalClosure.machine2 k).run t body).state=
        (if PartAEndpoint.thresholdContentWitnessRelation k a m x w then
          (NormalFinalClosure.machine2 k).accept else (NormalFinalClosure.machine2 k).reject) := by
  intro S F r W address I body
  let O:=RawCallerClosure.machine k
  let c:Config O.stateCount N B:=
    ⟨RawCallerClosure.callerState k (PhysicalCallerClosure.oldState k
      (BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode (Fin.append x w) address)))),
      ⟨S+z+2+n+1,by omega⟩,fun i=>SerializedBody.prepared I S address F r n (n^k+k) W i.val⟩
  have bodyEq:body=NormalFinalClosure.config2 k c:=by
    apply Config.ext_parts
    · rfl
    · apply Fin.ext;dsimp only [body,c,NormalFinalClosure.config2];omega
    · rfl
  have layout:Layout (RawCallerClosure.allocation k N) N S z n r (n^k+k) W address (9+2*z) (2^n) (Fin.append x w) I:=by
    subst N
    exact normalLayout k x w gamma header capacity arena physical ell window
  rcases layout with ⟨rp,rs,sr,gf,wp,wf,ef,af,ap,asrc,margin,qp,paid,hole,marker,src,eof,reg,left,right,beta,marks,gap,fence,metadataEmpty,fit,room⟩
  have fitB:SerializedBody.delimiter F r n 12+6 < tapeLength N B:=by
    have mono:tapeLength N (RawCallerClosure.allocation k N)≤tapeLength N B:=by
      unfold tapeLength
      omega
    exact fit.trans_le mono
  have layoutB:Layout B N S z n r (n^k+k) W address (9+2*z) (2^n) (Fin.append x w) I:=
    layoutMk rp rs sr gf wp wf ef af ap asrc margin qp paid hole marker src eof reg left right beta marks gap fence metadataEmpty fitB hH
  have safe0:c.state≠O.accept:=by
    intro bad
    exact (cutSafe k _).1 (callerInj k (bad.trans (callerAccept k).symm))
  obtain ⟨d,dp,allRows⟩:=rowsRun k B N S z n r (n^k+k) W address (9+2*z) (2^n)
    (Fin.append x w) I layoutB (show S+z+2+n+1 < tapeLength N B by omega) c 0 rfl
    (fun u hu=>by
      have e:u=0:=by omega
      subst u
      simpa only [UniformTM.run] using safe0)
    (fun u hu=>by omega)
  simp only [Nat.zero_add] at allRows
  have hist:∀ u,u≤d → (NormalFinalClosure.machine2 k).run u body=NormalFinalClosure.config2 k (O.run u c):=by
    rw [bodyEq]
    exact mapRun (A:=O) (B:=NormalFinalClosure.machine2 k) (NormalFinalClosure.old2 k) c (fun u hu b=>rowsOld k _ ((allRows.2.1 u hu).2) b)
  have prior:∀ u,u<d → ((NormalFinalClosure.machine2 k).run u body).state≠(NormalFinalClosure.machine2 k).accept ∧
      ((NormalFinalClosure.machine2 k).run u body).state≠(NormalFinalClosure.machine2 k).reject:=by
    intro u hu
    rw [hist u hu.le]
    refine ⟨?_,?_⟩
    · intro bad;exact allRows.1 u hu.le (oldInj k (bad.trans (acceptMap k).symm))
    · intro bad;exact (allRows.2.1 u hu).1 (oldInj k (bad.trans (rejectMap k).symm))
  have coarse:d ≤ 4398046511104*(k+1)*(N+1)^8:=dp.trans (Nat.mul_le_mul_right _ (by omega))
  by_cases rejected:(O.run d c).state=O.reject
  · have no:=normalReject k B N a m z n r x w I _ c d length header allRows rejected
    refine ⟨d,coarse.trans (Nat.mul_le_mul_right _ (by omega)),prior,?_⟩
    rw [hist d le_rfl]
    change NormalFinalClosure.old2 k (O.run d c).state=_
    rw [rejected,no]
    exact rejectMap k
  · obtain ⟨circuit,tail,decoded,size,_used,_tail,tableGood,atDone⟩:=
      doneResult k B N S z n r (n^k+k) W address (9+2*z) (Fin.append x w) I _ c d allRows rejected
    have rho:=NormalFinalClosure.rows_prefix_rho k a m n z x w length header tag circuit tail decoded size tableGood
    have rN:r≤N:=(Nat.sub_le S _).trans sr
    have bound:D F r n 13+1 ≤ 64*(N+1):=delimiterBound N S z n r sr (by
      have pos:=minLt _ S physical;dsimp only [S] at pos;omega) rN arena
    have fitGuard:D F r n 13 < tapeLength N B:=by
      have small:=rawRoom k N (D F r n 13) bound
      dsimp only [tapeLength] at small ⊢;omega
    let actualTape:=normalImage k N x w z n circuit.size (W-tail.length) (W-(W-tail.length))
    have frame:=frameAtN k N x w same gamma header capacity arena physical ell window
      circuit.size (W-tail.length) (W-(W-tail.length))
    obtain ⟨u,answer,_positive,up,correct,guardPrefix,_footprint,finish⟩:=composeGuard k N B S z n F r W
      (Fin.append x w) actualTape frame fitGuard _ d body c (hist d le_rfl) atDone
    have original:answer=PartAEndpoint.thresholdContentWitnessRelation k a m x w:=by
      apply Bool.eq_iff_iff.mpr
      have peq:S-r=9+2*z+2^n:=recovered _ S physical
      change (answer=true ↔ _) at correct
      rw [peq] at correct
      exact correct.trans rho.symm
    have priorAll:∀ v,v<d+u → ((NormalFinalClosure.machine2 k).run v body).state≠(NormalFinalClosure.machine2 k).accept ∧
        ((NormalFinalClosure.machine2 k).run v body).state≠(NormalFinalClosure.machine2 k).reject:=by
      intro v hv
      by_cases early:v<d
      · exact prior v early
      rcases guardPrefix (v-d) (by omega) with zero|native
      · have eq:v=d:=by omega
        subst v
        rw [hist d le_rfl]
        refine ⟨?_,?_⟩
        · intro bad;exact allRows.1 d le_rfl (oldInj k (bad.trans (acceptMap k).symm))
        · intro bad;exact rejected (oldInj k (bad.trans (rejectMap k).symm))
      · rw [show d+(v-d)=v by omega] at native
        refine ⟨?_,?_⟩
        · intro bad;exact safeNotOld k O.accept _ native (bad.trans (acceptMap k).symm)
        · intro bad;exact safeNotOld k O.reject _ native (bad.trans (rejectMap k).symm)
    refine ⟨d+u,guardPrice k N r (D F r n 13) u d rN bound coarse up,priorAll,?_⟩
    have state:=congrArg Config.state finish
    rw [original] at state
    exact state
end FullFinalClosure
