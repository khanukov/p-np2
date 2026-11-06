import NormalFinalClosure.Consequences
namespace NormalFinalClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
/-- Invert the CLOSED actual all-row result at its nonreject endpoint. This
extracts the SAME decoder/tail and entire physical Config, not a chosen parser. -/
private theorem rows_done (k B R S z n r g W M A : Nat) (source : Fin S → Bool)
    (T : Nat → Option Bool) (hH:S+z+2+n+1 < tapeLength R B)
    (c : Config (RawCallerClosure.machine k).stateCount R B) (t : Nat)
    (rows:RawCallerClosure.Target.RowsResult k B R S z n r g W M A (2^n) source T hH c t)
    (nonreject:((RawCallerClosure.machine k).run t c).state≠(RawCallerClosure.machine k).reject) :
    ∃ (circuit:Pnp3.Models.Circuit n) (tail:List Bool),
      decodeCircuitFull n (bitLength n) (SerializedBody.window source M W)=some (circuit,tail) ∧
      circuit.size ≤ g ∧ W-tail.length ≤ W ∧ tail=(SerializedBody.window source M W).drop (W-tail.length) ∧
      (∀ j,j < 2^n → padRead source (A+j)=circuit.eval (Pnp3.Core.vecOfNat n j)) ∧
      (RawCallerClosure.machine k).run t c=
        ⟨RawCallerClosure.callerState k (PhysicalCallerClosure.rowsDone k),⟨S+z+2+n+1,hH⟩,
          fun i=>PhysicalCallerClosure.callerImage T S z n (FixedRawLengthFence.fencePos R) r g W M 1
            (Pnp3.Core.vecOfNat n 0) circuit.size (W-tail.length) (W-(W-tail.length)) 0 i.val⟩ := by
  rcases rows with ⟨_safe,_first,result⟩
  dsimp only at result
  cases hd:decodeCircuitFull n (bitLength n) (SerializedBody.window source M W) with
  | none=>
    rw [hd] at result
    exact (nonreject (congrArg Config.state result)).elim
  | some pair=>
    rcases pair with ⟨circuit,tail⟩
    rw [hd] at result
    rcases result with ⟨_large,finish⟩|⟨small,used,tailEq,_starts,outcome⟩
    · exact (nonreject (congrArg Config.state finish)).elim
    · rcases outcome with ⟨_paid,good,finish⟩|⟨_row,_before,_prior,_mismatch,finish⟩|⟨overflow,_good,_finish⟩
      · refine ⟨circuit,tail,rfl,small,used,tailEq,good,?_⟩
        simpa only [Nat.sub_self,Nat.max_eq_left (Nat.zero_le 1)] using finish
      · exact (nonreject (congrArg Config.state finish)).elim
      · exact (Nat.lt_irrefl _ overflow).elim
end NormalFinalClosure
