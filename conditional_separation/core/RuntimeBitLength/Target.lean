import CappedWorkspace.Raw
namespace RuntimeBitLength.Target
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- Exact first halving output, relative to the actual q201 whole tape X. -/
def image (X : Nat → Option Bool) (L n F r : Nat) : Nat → Option Bool := fun i =>
  if L < i ∧ i < L+n+1 then some false else
  if F+r+2 < i ∧ i ≤ F+r+2+n/2 then some true else
  if i=F+r+n+4 then some true else X i
/-- Intended full bitLength output; both success and overflow are retained RED. -/
def fullImage (X : Nat → Option Bool) (L n F r : Nat) : Nat → Option Bool := fun i =>
  let g := bitLength n
  let v := n/2^(r+1)
  if L < i ∧ i < L+n+1 then some (decide (r < g ∧ (r+1)%2=0 ∧ i ≤ L+v)) else
  if F+r+2 < i ∧ i < F+r+n+3 then
    some (decide (r < g ∧ (r+1)%2=1 ∧ i ≤ F+r+2+v)) else
  if F+r+n+3 < i ∧ i ≤ F+r+n+3+min g r then some true else X i
def FullRaw (k : Nat) : Prop :=
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m) {pr : AcceptedBody.Parsed k},
    contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr →
    FixedContentTagGate.tagMatches (Fin.append x w)=true → 3 ≤ pr.2.n →
    ∃ z, 2 ≤ z ∧ FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
      (pr.2.n < FixedRawLengthFence.capacity a m z → 9+2*z ≤ a+m →
       2^pr.2.n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+pr.2.n+3)-1 →
       min (9+2*z+2^pr.2.n) (a+m) < a+m →
        ∃ (t : Nat) (h : (if bitLength pr.2.n ≤ (a+m)-min (9+2*z+2^pr.2.n) (a+m) then a+m+z+2
            else FixedRawLengthFence.fencePos (pairLength a m)+((a+m)-min (9+2*z+2^pr.2.n) (a+m))+pr.2.n+3) <
            tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
          t ≤ 16777216*(pairLength a m+1)^4 ∧
          (∀ u, u < t → ∀ s ∈ [308,250,304], ((Cursor.rawMachine k).run u (initialConfig (Cursor.rawMachine k)
            (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state ≠
              FixedRawLengthFence.prefixed.seqRight (Cursor.machine k) (Cursor.q k s)) ∧
          let S := a+m
          let n := pr.2.n
          let F := FixedRawLengthFence.fencePos (pairLength a m)
          let r := S-min (9+2*z+2^n) S
          let U := Body.extend (Body.installedTape (FixedRawLengthFence.countdownTape
            (FixedRawLengthFence.allocation (pairLength a m)) x w z 0 n) (S+z+2) n)
          let T := Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
          let X := CappedWorkspace.Target.image (SuffixCap.Target.image T F r) (S+z+2) n F r
          (r < bitLength n → S < Cursor.Target.M k n z) ∧
          F+5*r+n+7 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)) ∧
          (Cursor.rawMachine k).run t (initialConfig (Cursor.rawMachine k)
            (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            FixedRawLengthFence.prefixed.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.q k (if bitLength n ≤ r then 308 else if (r+1)%2=1 then 250 else 304),
                ⟨if bitLength n ≤ r then S+z+2 else F+r+n+3,h⟩,
                fun i => fullImage X (S+z+2) n F r i.val⟩)

/-- Connected first halving, first q254 AFTER the first q201; no global q254 claim. -/
def Raw (k : Nat) : Prop :=
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m) {pr : AcceptedBody.Parsed k},
    contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr →
    FixedContentTagGate.tagMatches (Fin.append x w)=true → 3 ≤ pr.2.n →
    ∃ z, 2 ≤ z ∧ FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
      (pr.2.n < FixedRawLengthFence.capacity a m z → 9+2*z ≤ a+m →
       2^pr.2.n ≤ FixedRawLengthFence.fencePos (pairLength a m)-(a+m+z+pr.2.n+3)-1 →
       min (9+2*z+2^pr.2.n) (a+m) < a+m →
        ∃ (t0 t : Nat) (h : FixedRawLengthFence.fencePos (pairLength a m)+
            ((a+m)-min (9+2*z+2^pr.2.n) (a+m))+2 <
            tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
          t ≤ 2097152*(pairLength a m+1)^3 ∧ t0 ≤ t ∧
          ((Cursor.rawMachine k).run t0 (initialConfig (Cursor.rawMachine k)
            (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state =
              FixedRawLengthFence.prefixed.seqRight (Cursor.machine k) (Cursor.q k 201) ∧
          (∀ u, u < t0 → ((Cursor.rawMachine k).run u (initialConfig (Cursor.rawMachine k)
            (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state ≠
              FixedRawLengthFence.prefixed.seqRight (Cursor.machine k) (Cursor.q k 201)) ∧
          (∀ u, t0 ≤ u → u < t → ((Cursor.rawMachine k).run u (initialConfig (Cursor.rawMachine k)
            (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state ≠
              FixedRawLengthFence.prefixed.seqRight (Cursor.machine k) (Cursor.q k 254)) ∧
          let S := a+m
          let n := pr.2.n
          let F := FixedRawLengthFence.fencePos (pairLength a m)
          let r := S-min (9+2*z+2^n) S
          let U := Body.extend (Body.installedTape (FixedRawLengthFence.countdownTape
            (FixedRawLengthFence.allocation (pairLength a m)) x w z 0 n) (S+z+2) n)
          let T := Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
          let X := CappedWorkspace.Target.image (SuffixCap.Target.image T F r) (S+z+2) n F r
          F+5*r+n+7 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)) ∧
          (Cursor.rawMachine k).run t (initialConfig (Cursor.rawMachine k)
            (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)) =
            FixedRawLengthFence.prefixed.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.q k 254,⟨F+r+2,h⟩,fun i => image X (S+z+2) n F r i.val⟩)
end RuntimeBitLength.Target
