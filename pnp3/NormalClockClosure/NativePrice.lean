import NormalClockClosure.FrontierPrice
import NormalFinalClosure.Driver2
namespace NormalClockClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion PairEncoding Lean Elab Command
run_cmd do
  let e←getEnv
  for (owner,ns,leaves) in [
      (`NormalClockClosure.FrontierPrice,`NormalClockClosure,["OldBoundary","first_frontier_price"]),
      (`NormalClockClosure.Arithmetic,`NormalClockClosure,["normal_price","source_room_price"]),
      (`NormalFinalClosure.Driver2,`NormalFinalClosure,["doneResult","raw_room","inherited_raw_reject","reject_map"]),
      (`NormalFinalClosure.RawFrameN2,`NormalFinalClosure,["normalImage","frame_at_N"]),
      (`NormalFinalClosure.RawComposition2,`NormalFinalClosure,["compose_guard","min_lt_implies","zero_bound"]),
      (`NormalFinalClosure.Arithmetic,`NormalFinalClosure,["delimiter_bound"]),
      (`NormalFinalClosure.Frame2,`NormalFinalClosure,["D"])] do
    for leaf in leaves do
      let n:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
      let some ci:=e.find? n | throwError "Missing exact NORMAL resource interface {n}"
      let actual:=match ci with|.thmInfo _=>"theorem"|.defnInfo _=>"definition"|_=>"other"
      let expected:=if ["OldBoundary","normalImage","D"].contains leaf then "definition" else "theorem"
      unless actual==expected do throwError "Wrong NORMAL resource kind {n}"
      let some i:=e.getModuleIdxFor? n | throwError "Missing NORMAL resource owner"
      unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong NORMAL resource owner"
      logInfo m!"normal-resource-interface|{owner}|{n}|kind={actual}|{ci.type}"
      modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
private def Boundary (k : Nat) (q : Fin (NormalFinalClosure.machine2 k).stateCount) : Prop :=
    q=(NormalFinalClosure.machine2 k).accept ∨ q=(NormalFinalClosure.machine2 k).reject ∨
    ∃ b,q=NormalFinalClosure.old2 k (RawCallerClosure.old k (CertificateGuardClosure.old k (TotalIngressClosure.old k
      (BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b))))))
/-- Physical SAME-table execution with a sharp price, using sealed native row
prices. This is an existence of an executed frontier, not an observer bound. -/
private theorem cheap_normal (k N : Nat) (y : Bitstring N) :
    ∃ T,T ≤ 549755813888*(k+1)*(N+1)^7 ∧ Boundary k
      ((NormalFinalClosure.machine2 k).run T
        (initialConfig (NormalFinalClosure.machine2 k) (RawCallerClosure.allocation k N) y)).state := by
  let B:=RawCallerClosure.allocation k N
  let M:=NormalFinalClosure.machine2 k
  let O:=RawCallerClosure.machine k
  let C:=initialConfig M B y
  let oldC:=initialConfig O B y
  obtain ⟨_pre,d,_front,_order,_oldPrice,_oldHistory,_safe,first,outcome⟩:=RawCallerClosure.raw k N y
  have first':∀ u,u < d → ¬OldBoundary k (O.run u oldC).state:=by
    intro u hu hit
    rcases hit with bad|bad|⟨b,bad⟩
    · exact (first u hu).1 bad
    · exact (first u hu).2.1 bad
    · exact (first u hu).2.2 b bad
  have dp:=first_frontier_price k N y d first'
  have hist:∀ u,u ≤ d → M.run u C=NormalFinalClosure.config2 k (O.run u oldC):=
    NormalFinalClosure.raw_prefix2 k N B d y (fun u hu=>(first u hu).2.1)
  have oldPrice:d ≤ 549755813888*(k+1)*(N+1)^7:=dp.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide)))
  have oldReject (hit:(O.run d oldC).state=O.reject) : Boundary k (M.run d C).state:=by
    right;left
    have state:=congrArg Config.state (hist d le_rfl)
    change (M.run d C).state=NormalFinalClosure.old2 k (O.run d oldC).state at state
    rw [hit,reject_map] at state
    exact state
  rcases outcome with ⟨_same,reject,ending,_false⟩|⟨_same,⟨b,work⟩,ending⟩|normal
  · refine ⟨d,oldPrice,oldReject ?_⟩
    have state:=congrArg Config.state ending
    change (O.run d oldC).state=RawCallerClosure.old k _ at state
    rw [reject,inherited_raw_reject] at state
    exact state
  · refine ⟨d,oldPrice,Or.inr (Or.inr ⟨b,?_⟩)⟩
    have state:=congrArg Config.state ending
    change (O.run d oldC).state=RawCallerClosure.old k _ at state
    rw [work] at state
    have mapped:=congrArg Config.state (hist d le_rfl)
    change (M.run d C).state=NormalFinalClosure.old2 k (O.run d oldC).state at mapped
    exact mapped.trans (congrArg (NormalFinalClosure.old2 k) state)
  · rcases normal with ⟨a,m,x,w,hN,_decoded,_word,_length,n,z,_tag,gamma,header,
        physical,ell,window,capacity,arena,hH,_bodyEntry,rows⟩
    by_cases rejected:(O.run d oldC).state=O.reject
    · exact ⟨d,oldPrice,oldReject rejected⟩
    · obtain ⟨circuit,tail,_decoded,_size,_used,_tailEq,_good,endpoint⟩:=doneResult k B N (a+m) z n _
        (n^k+k) (Cursor.Target.W k n) (Cursor.Target.M k n z) (9+2*z) (Fin.append x w) _ hH oldC d rows rejected
      let S:=a+m
      let F:=FixedRawLengthFence.fencePos N
      let r:=S-min (9+2*z+2^n) S
      let W:=Cursor.Target.W k n
      have pairSize:2*a+1+m=N:=hN
      have sn:S ≤ N:=by dsimp only [S];omega
      have rn:r ≤ N:=(Nat.sub_le S _).trans sn
      have zp:z ≤ N:=(zero_bound S z (2^n) (min_lt_implies _ _ physical)).trans sn
      have pn:D F r n 13+1 ≤ 64*(N+1):=by
        change SerializedBody.delimiter (3*N+2) r n 12+6+1 ≤ 64*(N+1)
        exact delimiter_bound N S z n r sn zp rn arena
      have fit:D F r n 13 < tapeLength N B:=raw_room k N _ pn
      let T:=normalImage k N x w z n circuit.size (W-tail.length) (W-(W-tail.length))
      have actual:(O.run d oldC)=⟨RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k),
        ⟨S+z+2+n+1,hH⟩,fun i=>T i.val⟩:=endpoint
      have frame:=frame_at_N k N x w hN gamma header capacity arena physical ell window
        circuit.size (W-tail.length) (W-(W-tail.length))
      obtain ⟨u,answer,_pos,up,_correct,_native,_footprint,finish⟩:=compose_guard k N B S z n F r W
        (Fin.append x w) T frame fit hH d C oldC (hist d le_rfl) actual
      refine ⟨d+u,normal_price k N r (D F r n 13) d u rn pn dp up,?_⟩
      have state:=congrArg Config.state finish
      cases answer with
      | false=>exact Or.inr (Or.inl state)
      | true=>exact Or.inl state
/-- Strong elapsed bound for the SAME FIRST endpoint of the sealed all-raw
NORMAL partition. This supplies actual right-room on the original allocation. -/
private theorem first_run_small (k N : Nat) (y : Bitstring N) (t : Nat)
    (first:∀ u,u < t → ((NormalFinalClosure.machine2 k).run u
      (initialConfig (NormalFinalClosure.machine2 k) (RawCallerClosure.allocation k N) y)).state≠(NormalFinalClosure.machine2 k).accept ∧
      ((NormalFinalClosure.machine2 k).run u
      (initialConfig (NormalFinalClosure.machine2 k) (RawCallerClosure.allocation k N) y)).state≠(NormalFinalClosure.machine2 k).reject ∧
      ∀ b,((NormalFinalClosure.machine2 k).run u
      (initialConfig (NormalFinalClosure.machine2 k) (RawCallerClosure.allocation k N) y)).state≠
        NormalFinalClosure.old2 k (RawCallerClosure.old k (CertificateGuardClosure.old k (TotalIngressClosure.old k
          (BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b))))))) :
    t+1 ≤ RawCallerClosure.allocation k N := by
  obtain ⟨T,tp,last⟩:=cheap_normal k N y
  have before:t ≤ T:=by
    by_contra bad
    have safe:=first T (by omega)
    rcases last with hit|hit|⟨b,hit⟩
    · exact safe.1 hit
    · exact safe.2.1 hit
    · exact safe.2.2 b hit
  exact source_room_price k N t (before.trans tp)
end NormalClockClosure
