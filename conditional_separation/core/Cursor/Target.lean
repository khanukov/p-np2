import Cursor.Machine
namespace Cursor.Target
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- Specification only. No transition consults W or M as a host value. -/
def W (k n : Nat) : Nat := (bitLength n+4)*(n^k+k)
def M (k n z : Nat) : Nat := 9+2*z+2^n+bitLength (W k n)+W k n
/-- All six scratch banks are false at MReady; delimiters remain original blanks. -/
def scratch (T : Nat → Option Bool) (F r n : Nat) : Nat → Option Bool := fun i =>
  if F+1 < i ∧ i < F+r+2 ∨ F+r+2 < i ∧ i < F+r+n+3 ∨
     F+r+n+3 < i ∧ i < F+2*r+n+4 ∨ F+2*r+n+4 < i ∧ i < F+3*r+n+5 ∨
     F+3*r+n+5 < i ∧ i < F+4*r+n+6 ∨ F+4*r+n+6 < i ∧ i < F+5*r+n+7
  then some false else T i
def image (T : Nat → Option Bool) (k S n z F : Nat) : Nat → Option Bool := fun i =>
  let p := min (9+2*z+2^n) S
  let V := if p < S then scratch T F (S-p) n else T
  if i=M k n z ∧ i < S then none else V i
def deadline (k R : Nat) : Nat := 1048576*(k+2)*(R+1)^5
/-- Full intended literal raw M closure; remains RED until executed AND proved. -/
def Raw (k : Nat) : Prop :=
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m) {pr : AcceptedBody.Parsed k},
    contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr →
    FixedContentTagGate.tagMatches (Fin.append x w)=true → 3 ≤ pr.2.n →
    ∃ z, 2 ≤ z ∧ FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
      (pr.2.n < FixedRawLengthFence.capacity a m z → 9+2*z ≤ a+m →
       2^pr.2.n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+pr.2.n+3)-1 →
        ∃ (t : Nat) (hH : a+m+z+pr.2.n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)))
          (mode : Fin 3), t ≤ deadline k (pairLength a m) ∧
          (mode.val=2 ↔ a+m ≤ M k pr.2.n z) ∧
          InputRead.result mode=padRead (Fin.append x w) (M k pr.2.n z) ∧
          let U := Body.extend (Body.installedTape (FixedRawLengthFence.countdownTape
            (FixedRawLengthFence.allocation (pairLength a m)) x w z 0 pr.2.n) (a+m+z+2) pr.2.n)
          let T := Stream.Target.image U (a+m) z pr.2.n (9+2*z) (2^pr.2.n) (2^pr.2.n) false
          FixedRawLengthFence.fencePos (pairLength a m)+5*((a+m)-min (9+2*z+2^pr.2.n) (a+m))+pr.2.n+7 <
            tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)) ∧
          (rawMachine k).run t (initialConfig (rawMachine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            FixedRawLengthFence.prefixed.seqEmbedRight (machine k)
              ⟨mReady k mode,⟨a+m+z+pr.2.n+3,hH⟩,
                fun i => image T k (a+m) pr.2.n z (FixedRawLengthFence.fencePos (pairLength a m)) i.val⟩)
def PartA (partAMachine : Nat → UniformTM) (partAExponent : Nat → Nat) : Prop :=
  ∀ k, VerifiesRelation (partAMachine k) (partAExponent k)
    (PartAEndpoint.thresholdContentWitnessRelation k)
end Cursor.Target
