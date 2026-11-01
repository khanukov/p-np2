import UniformClassBridgeClosure.Joint
namespace UniformClassBridgeClosure
open Pnp3.Complexity.Uniform.V1 Turing
namespace Ordinary
/-- Exact iteration of ANY actual TM0 table on the fixed six-symbol alphabet.
No halt padding; no source V1 machine or simulation assumption occurs here. -/
def trace {Λ : Type} [Inhabited Λ] (T : TM0.Machine (Bool × Option Bool) Λ) :
    Nat → TM0.Cfg (Bool × Option Bool) Λ → Option (TM0.Cfg (Bool × Option Bool) Λ)
  | 0,s=>some s
  | t+1,s=>(TM0.step T s).bind (trace T t)
/-- Literal, first-arrival halting-control decision convention on real TM0.
The input symbol encoding is fixed and length-preserving. No tape-output claim. -/
def Decides {Λ : Type} [Inhabited Λ] (T : TM0.Machine (Bool × Option Bool) Λ)
    (accept reject : Λ) (bound : Nat) {N : Nat} (y : Bitstring N) (answer : Bool) : Prop :=
  accept≠reject ∧ ∃ (t : Nat) (last : TM0.Cfg (Bool × Option Bool) Λ),
    t ≤ bound ∧ trace T t (TM0.init (StandardTMBridgeClosure.encode (List.ofFn y)))=some last ∧
    last.q=(if answer then accept else reject) ∧ TM0.step T last=none ∧
    ∀ j,j < t → ∀ v,trace T j (TM0.init (StandardTMBridgeClosure.encode (List.ofFn y)))=some v →
      v.q≠accept ∧ v.q≠reject
/-- Total raw-word verifier; malformed pair encodings literally reject. -/
def Verifies {Λ : Type} [Inhabited Λ] (T : TM0.Machine (Bool × Option Bool) Λ)
    (accept reject : Λ) (c : Nat) (R : WitnessRelation) : Prop :=
  ∀ N (y : Bitstring N),Decides T accept reject (N^c+c) y
    (match PairEncoding.decodePair y with
     | none=>false | some p=>R p.1.1 p.2.1 p.1.2 p.2.2)
/-- An arbitrary finite label type and arbitrary fixed TM0 table, chosen BEFORE
all inputs. This definition contains no V1 decision or class predicate. -/
def UniformP (L : Language) : Prop :=
  ∃ (Λ : Type) (_ : Fintype Λ) (I : Inhabited Λ)
    (T : @TM0.Machine (Bool × Option Bool) Λ I) (accept reject : Λ) (c : Nat),
    ∀ N (y : Bitstring N),@Decides Λ I T accept reject (N^c+c) N y (L N y)
/-- Same relation and independent original-input witness bound. Both the fixed
finite verifier and both exponents are outside all query/witness quantifiers. -/
def UniformNP (L : Language) : Prop :=
  ∃ (R : WitnessRelation) (Λ : Type) (_ : Fintype Λ) (I : Inhabited Λ)
    (T : @TM0.Machine (Bool × Option Bool) Λ I) (accept reject : Λ)
    (verifierExponent witnessExponent : Nat),
    @Verifies Λ I T accept reject verifierExponent R ∧
    ∀ n (x : Bitstring n),L n x=true ↔
      ∃ m,∃ w : Bitstring m,m ≤ n^witnessExponent+witnessExponent ∧ R n m x w=true
end Ordinary
end UniformClassBridgeClosure
