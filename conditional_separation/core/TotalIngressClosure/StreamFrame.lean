import TotalIngressClosure.ProducerSuccess
import TotalIngressClosure.StreamOrbitAll
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding Lean Elab Command
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("SmallOrbit.Runtime","SmallOrbit","Frame","SourceFrame"),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.mk","frameMk"),
      ("SmallOrbit.Runtime","SmallOrbit","prepared_frame","fullFrame")] do
    let found:=env.constants.toList.filter fun (n,_)=>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun s=>{s with openDecls:=.explicit (Name.str .anonymous aliasName) n::s.openDecls}
    | _=>throwError "Nonunique physical source frame {mod}/{key}: {found.map Prod.fst}"
/-- Actual partial-gamma source frame. A clipped source cursor is derived from
literal consumed gamma cells, not installed as a caller scratch premise. -/
private theorem source_frame {a m z n consumed : Nat} (x : Bitstring a) (w : Bitstring m)
    (header:contentHeader? (Fin.append x w)=some (n,consumed))
    (gamma:FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z)
    (physical:z=0 ∨ 9+z < a+m) (cap:n < FixedRawLengthFence.capacity a m z) :
    SourceFrame (Body.extend (SmallIngress.prepared (FixedRawLengthFence.allocation (pairLength a m)) x w z n))
      (a+m) z n (min (9+2*z) (a+m)) (FixedRawLengthFence.fencePos (pairLength a m)) := by
  obtain ⟨z',other,_len,lower,upper,_borrow,_digits,_high⟩:=decremented_register_digits x w header
  have equal:z'=z:=Option.some.inj (other.symm.trans gamma)
  subst z'
  have gammaBound:=((FixedContentGammaTerminator.gamma_contract (Fin.append x w)).1 z gamma).1
  by_cases full:9+2*z ≤ a+m
  · rw [Nat.min_eq_left full]
    apply fullFrame x w gamma cap full
    intro hz
    subst z
    norm_num at upper
    omega
  have support:9+z < a+m:=by rcases physical with h | h <;> omega
  have wide:2 ≤ z:=by omega
  have positive:0 < n:=by
    have pw:4 ≤ 2^z:=Nat.pow_le_pow_right (by decide :0 < (2:Nat)) wide
    omega
  let R:=pairLength a m
  let B:=FixedRawLengthFence.allocation R
  let S:=a+m
  let H:=S+z+n+3
  let F:=FixedRawLengthFence.fencePos R
  let A:=8+z+FixedGammaTargetPayloadExhaustion.termWalk S z+1
  let U:=Body.extend (SmallIngress.prepared B x w z n)
  have resource:=(FixedRawLengthFence.resource_bounds R).1
  have cells:=FixedRawLengthFence.countdown_success_cells x w gamma resource (Nat.le_of_lt cap)
  obtain ⟨room,_scratch,hF,_fence⟩:=Stream.raw_budget_cells x w gamma cap
  change H < F at room
  change F < tapeLength R B at hF
  have sourceSize:S < F:=by dsimp only [H] at room;omega
  have clipped:A=min (9+2*z) S:=by
    dsimp only [A,FixedGammaTargetPayloadExhaustion.termWalk,FixedGammaTargetPayloadLoopFoundation.walk]
    rw [Nat.min_eq_right (by dsimp only [S];omega),Nat.min_eq_right (by dsimp only [S];omega)]
    dsimp only [S]
    omega
  have aS:A=S:=by rw [clipped,Nat.min_eq_right (by dsimp only [S];omega)]
  have walk:1 ≤ FixedGammaTargetPayloadExhaustion.termWalk S z:=by
    unfold FixedGammaTargetPayloadExhaustion.termWalk FixedGammaTargetPayloadLoopFoundation.walk
    dsimp only [S]
    omega
  have read (i : Nat) (hi:i < tapeLength R B):
      U i=FixedRawLengthFence.countdownTape B x w z 0 n ⟨i,hi⟩:=by
    have hi':i < tapeLength (pairLength a m) B:=hi
    simp only [U,Body.extend,dif_pos hi',SmallIngress.prepared,if_neg (by omega :¬(n=0 ∧ i=7))]
  have low (i : Nat) (hi:i < S):
      U i=FixedGammaTargetPayloadExhaustion.finishTape B x w z ⟨i,by
        change i < tapeLength R B
        omega⟩:=by
    rw [read i (by omega)]
    exact cells.1 _ hi
  have src (i : Nat) (lo:A ≤ i) (hi:i < S):∃ b,U i=some b:=by omega
  have eof:U S=none:=by
    rw [read S (sourceSize.trans hF)]
    unfold FixedRawLengthFence.countdownTape
    rw [if_neg (by omega : S≠F)]
    simp [FixedGammaTargetUnaryCountdown.loopTape,S]
  have reg (i : Nat) (lo:S < i) (hi:i < S+z+2):U i=some false:=by
    rw [read i (by omega)]
    exact cells.2.1 (i-S-1) (by omega) _ (by dsimp only [S];omega)
  have sep:U (S+z+2)=none:=by
    rw [read _ (by omega)]
    exact cells.2.2.1 _ (by dsimp only [S];omega)
  have marks (i : Nat) (lo:S+z+2 < i) (hi:i < H):U i=some true:=by
    rw [read i (by omega)]
    exact cells.2.2.2.1 _ (by dsimp only [S];omega) (by change i < a+m+3+z+n;dsimp only [H,S] at hi;omega)
  have right:U H=none:=by
    rw [read H (room.trans hF)]
    exact cells.2.2.2.2.1 _ (by dsimp only [H,S];omega) room
  have scratch (i : Nat) (lo:H < i) (hi:i < F):U i=none:=by
    rw [read i (hi.trans hF)]
    exact cells.2.2.2.2.1 _ (by dsimp only [H,S] at lo ⊢;omega) hi
  have fence:U F=some false:=by rw [read F hF];exact cells.2.2.2.2.2 _ rfl
  have hole:U (A-2)=none:=by
    rw [low _ (by omega)]
    unfold FixedGammaTargetPayloadExhaustion.finishTape
    rw [if_pos (by change 8+z ≤ A-2 ∧ A-2 < 8+z+FixedGammaTargetPayloadExhaustion.termWalk S z;dsimp only [A];omega)]
  have marker:U (A-1)=some true:=by
    rw [low _ (by omega)]
    unfold FixedGammaTargetPayloadExhaustion.finishTape
    rw [if_neg (by change ¬(8+z ≤ A-1 ∧ A-1 < 8+z+FixedGammaTargetPayloadExhaustion.termWalk S z);dsimp only [A];omega),
      if_pos (by change A-1=8+z+FixedGammaTargetPayloadExhaustion.termWalk S z;dsimp only [A];omega)]
  rw [←clipped]
  exact frameMk ⟨by omega,by omega⟩ room src eof reg sep marks right scratch fence hole marker
end TotalIngressClosure
