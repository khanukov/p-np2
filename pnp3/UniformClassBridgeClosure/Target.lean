import UniformClassBridgeClosure.Model
namespace UniformClassBridgeClosure.Target
open Pnp3.Complexity.Uniform.V1 Turing
/-- General transfer, including the SAME actual finite full Config, every
source macro prefix, every elementary prefix, and first literal library halt. -/
def Transfer : Prop :=
  ∀ (M : UniformTM) (c N : Nat) (y : Bitstring N) (answer : Bool),
    DecidesWithin M (polyClock c N) y answer →
    Ordinary.Decides (StandardTMBridgeClosure.compile M) (some (M.accept,0)) (some (M.reject,0))
      (N^(4*c+4)+(4*c+4)) y answer ∧
    ∃ (t : Nat) (last : TM0.Cfg (Bool × Option Bool) (Option (Fin M.stateCount × Fin 4))),
      t ≤ polyClock c N ∧ 1+2*t ≤ N^(4*c+4)+(4*c+4) ∧
      (M.run t (initialConfig M (polyClock c N) y)).state=(if answer then M.accept else M.reject) ∧
      Ordinary.trace (StandardTMBridgeClosure.compile M) (1+2*t)
        (TM0.init (StandardTMBridgeClosure.encode (List.ofFn y)))=some last ∧
      StandardTMBridgeClosure.Represents M (M.run t (initialConfig M (polyClock c N) y)) last ∧
      (∀ u,u ≤ t → ∃ v,Ordinary.trace (StandardTMBridgeClosure.compile M) (1+2*u)
        (TM0.init (StandardTMBridgeClosure.encode (List.ofFn y)))=some v ∧
        StandardTMBridgeClosure.Represents M (M.run u (initialConfig M (polyClock c N) y)) v) ∧
      (∀ u,u < t →
        let s:=M.run u (initialConfig M (polyClock c N) y)
        let a:=M.step s.state (s.tape s.head)
        ∃ v,Ordinary.trace (StandardTMBridgeClosure.compile M) (2+2*u)
          (TM0.init (StandardTMBridgeClosure.encode (List.ofFn y)))=some v ∧
          v.q=some (a.1,match a.2.2 with | .left=>1 | .stay=>2 | .right=>3) ∧
          ∀ i : Int,v.Tape.nth i=
            if i=0 then (decide (s.head.val=0),a.2.1)
            else if h:0 ≤ (s.head.val : Int)+i ∧ (s.head.val : Int)+i < (tapeLength N (polyClock c N) : Int)
            then (decide ((s.head.val : Int)+i=0),s.tape ⟨((s.head.val : Int)+i).toNat,by omega⟩)
            else (false,none)) ∧
      (∀ j,j ≤ 1+2*t → ∃ v,Ordinary.trace (StandardTMBridgeClosure.compile M) j
        (TM0.init (StandardTMBridgeClosure.encode (List.ofFn y)))=some v)
/-- All class machines/exponents precede all inputs; relation lift keeps R. -/
def Lifts : Prop :=
  (∀ (M : UniformTM) (c : Nat) (R : WitnessRelation),VerifiesRelation M c R →
    Ordinary.Verifies (StandardTMBridgeClosure.compile M) (some (M.accept,0)) (some (M.reject,0)) (4*c+4) R) ∧
  (∀ L,UniformP L → Ordinary.UniformP L) ∧
  (∀ L,UniformNP L → Ordinary.UniformNP L)
end UniformClassBridgeClosure.Target
