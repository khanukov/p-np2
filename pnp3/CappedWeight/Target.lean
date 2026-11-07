import AllArityBitLength.Raw
namespace CappedWeight.Target
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- Unary bank image, retaining every delimiter and every exterior source cell. -/
def image (T : Nat → Option Bool) (L n F r v2 v3 v4 v5 d : Nat) : Nat → Option Bool := fun i =>
  if L < i ∧ i < L+n+1 then some (decide (L+n+1-d ≤ i))
  else if F+r+n+3 < i ∧ i < F+2*r+n+4 then some (decide (i ≤ F+r+n+3+v2))
  else if F+2*r+n+4 < i ∧ i < F+3*r+n+5 then some (decide (i ≤ F+2*r+n+4+v3))
  else if F+3*r+n+5 < i ∧ i < F+4*r+n+6 then some (decide (i ≤ F+3*r+n+5+v4))
  else if F+4*r+n+6 < i ∧ i < F+5*r+n+7 then some (decide (i ≤ F+4*r+n+6+v5))
  else T i
/-- Exact residual counters at a capped arithmetic exit. -/
def Cap (k n r v2 v3 v4 v5 d : Nat) : Prop :=
  (∃ j a e, j<k ∧ a<n^j ∧ e<n ∧ r=a*n+e ∧
    v2=bitLength n ∧ v3=n^j-a-1 ∧ v4=r ∧ v5=0 ∧ d=e+1) ∨
  (∃ j, j<k ∧ n^k+j=r ∧ v2=bitLength n ∧ v3=r ∧ v4=0 ∧ v5=0 ∧ d=0) ∨
  (∃ j, j<4 ∧ bitLength n+j=r ∧ v2=r ∧ v3=n^k+k ∧ v4=0 ∧ v5=0 ∧ d=0) ∨
  (∃ a e, a<bitLength n+4 ∧ e<n^k+k ∧ r=a*(n^k+k)+e ∧
    v2=bitLength n+4-a-1 ∧ v3=n^k+k-e-1 ∧ v4=r ∧ v5=e ∧ d=0)
/-- Full requested raw capstone. This stronger target remains separate from any split. -/
def FullRaw (k : Nat) : Prop :=
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true →
    ∃ pr : (Sigma fun q : Nat => PrefixInput
      (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) q)),
      contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr ∧
      ∃ (z : Nat) (hH : a+m+z+pr.2.n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
      FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
      let S := a+m; let R := pairLength a m; let B := FixedRawLengthFence.allocation R
      let n := pr.2.n; let L := S+z+2; let F := FixedRawLengthFence.fencePos R
      let p := min (9+2*z+2^n) S; let r := S-p
      let U := Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
      let V := Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
      let X := CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
      let Y := RuntimeBitLength.Target.fullImage X L n F r
      let Z := AllArityBitLength.Target.seedImage Y F r n
      let c := initialConfig (AllArityCursor.machine k) B (encodePair x w)
      (p=S → ∃ t, t≤268435456*(k+1)*(R+1)^4 ∧ S≤Cursor.Target.M k n z ∧
        (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
          ⟨Cursor.mReady k ⟨2,by decide⟩,⟨S+z+n+3,hH⟩,fun i => V i.val⟩) ∧
      (p<S → ∃ (h : F+5*r+n+7 < tapeLength R B) (t : Nat),
        t≤268435456*(k+1)*(R+1)^4 ∧
        ((r<bitLength n ∧ S<Cursor.Target.M k n z ∧
          (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
            ⟨Cursor.q k (if (r+1)%2=1 then 250 else 304),⟨F+r+n+3,lt_of_le_of_lt (by omega : F+r+n+3 ≤ F+5*r+n+7) h⟩,fun i => Y i.val⟩) ∨
         (bitLength n≤r ∧
          (((Cursor.Target.W k n≤r) ∧
            (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.q k (430+93*k),⟨F+r+n+3,lt_of_le_of_lt (by omega : F+r+n+3 ≤ F+5*r+n+7) h⟩,
                fun i => image Z L n F r 0 (n^k+k) (Cursor.Target.W k n) 0 0 i.val⟩ ∧
            ∀ u, u<t → ((AllArityCursor.machine k).run u c).state≠
              SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k (430+93*k))) ∨
           (∃ v2 v3 v4 v5 d, Cap k n r v2 v3 v4 v5 d ∧ S<Cursor.Target.M k n z ∧
            (AllArityCursor.machine k).run t c=SmallIngress.producer.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.q k (798+93*k),⟨F+1,lt_of_le_of_lt (by omega : F+1 ≤ F+5*r+n+7) h⟩,fun i => image Z L n F r v2 v3 v4 v5 d i.val⟩ ∧
            ∀ u, u<t → ((AllArityCursor.machine k).run u c).state≠
              SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k (798+93*k)))))))
/-- Candidate split: the first actual multiplication by the assignment width.
Strict firstness here is relative to the real q329 arrival, never its deadline. -/
def FirstProduct (k N B L n F r : Nat) (T : Nat → Option Bool) : Prop :=
  ∀ (fit : F+5*r+n+7 < tapeLength N B),
  ∃ t, t≤1024*(n+r+1)^2*(F+5*r+n+9) ∧
    (Cursor.machine k).run t
      (⟨Cursor.q k 329,⟨F+2*r+n+4,by omega⟩,fun i => T i.val⟩ : Config (Cursor.machine k).stateCount N B)=
      ⟨Cursor.q k (if n≤r then 411 else 798+93*k),
        ⟨if n≤r then F+2*r+n+4 else F+1,by split <;> omega⟩,
        fun i => image T L n F r (bitLength n) (if n≤r then n else 0) (if n≤r then 0 else r) 0 (if n≤r then 0 else r+1) i.val⟩ ∧
    (∀ u, u<t → ((Cursor.machine k).run u
      (⟨Cursor.q k 329,⟨F+2*r+n+4,by omega⟩,fun i => T i.val⟩ : Config (Cursor.machine k).stateCount N B)).state.val<411)
end CappedWeight.Target
