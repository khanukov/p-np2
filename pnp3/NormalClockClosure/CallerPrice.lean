import NormalClockClosure.Arithmetic
import RawCallerClosure.RowsRun
namespace NormalClockClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
run_cmd do
  let e←getEnv
  for (owner,ns,leaf,kind) in [
      (`PhysicalCallerClosure.AllRows,`PhysicalCallerClosure,"Layout","inductive"),
      (`PhysicalCallerClosure.AllRows,`PhysicalCallerClosure,"iterate","theorem"),
      (`PhysicalCallerClosure.Bootstrap,`PhysicalCallerClosure,"bootstrap","theorem"),
      (`PhysicalCallerClosure.RowFailure,`PhysicalCallerClosure,"failure_round","theorem"),
      (`PhysicalCallerClosure.SourceInitialize,`PhysicalCallerClosure,"anchorMode","definition"),
      (`PhysicalCallerClosure.RowSource,`PhysicalCallerClosure,"mode_virtual","theorem"),
      (`PhysicalCallerClosure.RowSource,`PhysicalCallerClosure,"source_cell","theorem"),
      (`NormalClockClosure.Arithmetic,`NormalClockClosure,"caller_price","theorem")] do
    let n:=(leaf.splitOn ".").foldl Name.str (Name.append (Name.num (Name.append `_private owner) 0) ns)
    let some ci:=e.find? n | throwError "Missing exact physical-price interface {n}"
    let actual:=match ci with | .thmInfo _=>"theorem"|.defnInfo _=>"definition"|.inductInfo _=>"inductive"|_=>"other"
    unless actual==kind do throwError "Wrong physical-price interface kind {n}"
    let some i:=e.getModuleIdxFor? n | throwError "Missing physical-price owner"
    unless i.toNat<e.header.moduleNames.size && e.header.moduleNames[i]! == owner do throwError "Wrong physical-price owner"
    logInfo m!"physical-price-interface|{owner}|{n}|kind={kind}|{ci.type}"
    modifyScope fun st=>{st with openDecls:=.explicit (Name.str .anonymous leaf) n::st.openDecls}
/-- Tight price extracted from the SAME literal bootstrap/paid recursion. The
possibly enormous 2^n is never a loop-bound premise; actual Q is physically paid. -/
private theorem cheap_caller (k B R S z n r g W M A Q : Nat) (source : Fin S → Bool) (T : Nat → Option Bool)
    (layout:Layout B R S z n r g W M A Q source T) (hH:S+z+n+3 < tapeLength R B) :
    let c : Config (PhysicalCallerClosure.callerMachine k).stateCount R B:=
      ⟨PhysicalCallerClosure.oldState k (BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode source M))),
        ⟨S+z+n+3,hH⟩,fun i=>SerializedBody.prepared T S M (FixedRawLengthFence.fencePos R) r n g W i.val⟩
    (∃ t,t ≤ 17179869184*(R+1)^7 ∧
      ((PhysicalCallerClosure.callerMachine k).run t c).state=(PhysicalCallerClosure.callerMachine k).reject) ∨
    ∃ t,t ≤ 17179869184*(R+1)^7 ∧
      ((PhysicalCallerClosure.callerMachine k).run t c).state=PhysicalCallerClosure.rowsDone k := by
  intro c
  have kept:=layout
  rcases layout with ⟨_rp,rs,sr,gf,_wp,wf,ef,af,ap,asrc,margin,qp,arena,hole,marker,src,eof,reg,left,right,beta,marks,gap,fence,metadata,fit,_room⟩
  have power:0 < 2^n:=Nat.pow_pos (by decide)
  have qb:Q ≤ 3*R+2:=by change S+z+n+3+Q < 3*R+2 at arena;omega
  obtain ⟨initial,E,ip,frame,entry⟩:=bootstrap k B R S z n r g W M A Q source T (rs.trans sr) ap asrc
    (by omega) qp arena hole marker src eof reg left right beta marks gap fence
    (metadata _ (by omega) le_rfl) fit hH
  let start : Config (PhysicalCallerClosure.callerMachine k).stateCount R B:=
    ⟨PhysicalCallerClosure.resetEntry k (anchorMode source M),⟨S+z+n+3,hH⟩,
      fun i=>SerializedBody.image E (FixedRawLengthFence.fencePos R) r n g W (S-min M S) 0 0 W g i.val⟩
  have after (t : Nat) : (PhysicalCallerClosure.callerMachine k).run (initial+t) c=
      (PhysicalCallerClosure.callerMachine k).run t start:=by
    rw [UniformTM.run_add,entry]
  have bad (failed:(do
      let (circuit,tail) ← decodeCircuitFull n (bitLength n) (SerializedBody.window source M W)
      if circuit.size ≤ g then some ((circuit.size,Pnp3.Models.Circuit.eval circuit (Pnp3.Core.vecOfNat n 0)),tail) else none)=none) :
      ∃ t,t ≤ 17179869184*(R+1)^7 ∧
        ((PhysicalCallerClosure.callerMachine k).run t c).state=(PhysicalCallerClosure.callerMachine k).reject := by
    have tag:(anchorMode source M).val=2 ↔ S ≤ M:=by
      unfold anchorMode
      by_cases hm:M < S
      · rw [if_pos hm,mode_virtual];omega
      · rw [if_neg hm];change 2=2 ↔ S ≤ M;omega
    have av:M < S → T (M-1)=some (decide ((anchorMode source M).val=1)):=by
      intro hm
      unfold anchorMode
      rw [if_pos hm]
      exact source_cell source T A (M-1) src (by omega) (by omega)
    obtain ⟨elapsed,ep,finish⟩:=failure_round k B R S z n r g W M A Q (anchorMode source M)
      (SerializedBody.sourceMode source A) source T E frame failed rs sr gf wf ef af margin ap qp arena src eof reg left right
      fence (metadata _ (by omega) le_rfl) tag (mode_virtual source A) av (source_cell source T A A src le_rfl) fit hH
    have ep':elapsed ≤ Q*(2147483648*(R+1)^6):=ep.trans (Nat.le_mul_of_pos_left _ qp)
    refine ⟨initial+elapsed,caller_price R Q initial elapsed qb ip ep',?_⟩
    rw [after,finish]
  cases parsed:decodeCircuitFull n (bitLength n) (SerializedBody.window source M W) with
  | none=>
    left
    apply bad
    rw [parsed];rfl
  | some pair=>
    rcases pair with ⟨circuit,tail⟩
    by_cases cap:circuit.size ≤ g
    · obtain ⟨_ub,_tailEq,elapsed,_starts,ep,_paid,_order,ending⟩:=iterate k B R S z n r g W M A Q source T kept circuit tail parsed cap
        Q 0 0 0 W g E (by omega) qp power frame
      have price:=caller_price R Q initial elapsed qb ip ep
      rcases ending with ⟨_enough,_good,eq⟩|⟨_row,_lower,_upper,_prior,_wrong,eq⟩|⟨_few,_prior,eq⟩
      · right
        refine ⟨initial+elapsed,price,?_⟩
        rw [after,eq]
      · left
        refine ⟨initial+elapsed,price,?_⟩
        rw [after,eq]
      · left
        refine ⟨initial+elapsed,price,?_⟩
        rw [after,eq]
    · left
      apply bad
      rw [parsed]
      change (if circuit.size ≤ g then some _ else none)=none
      rw [if_neg cap]
end NormalClockClosure
