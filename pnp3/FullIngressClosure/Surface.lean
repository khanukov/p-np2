import FullIngressClosure.Closure
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
theorem check_body (k : Nat) :
  ∀ (R S z n p g W Q : Nat) (source : Fin S  →  Bool) (beta : Fin n  →  Bool) (T : Nat  →  Option Bool),
    1 ≤ R  →  S ≤ R  →  n ≤ R  →  p < S  →
    let r:=S-p; let L:=S+z+2; let H:=L+n+1; let F:=FixedRawLengthFence.fencePos R
    let B:=FixedRawLengthFence.allocation R; let D:=SerializedBody.delimiter F r n
    g ≤ r  →  W ≤ r  →  bitLength n ≤ r  →  0 < Q  →  H+Q < F  →
    (∀ i, p ≤ i  →  ∀ hi : i < S, T i=some (source ⟨i,hi⟩))  →  T S=none  →
    (∀ i,S < i  →  i < L  →  T i=some false)  →  T L=none  →  T H=none  →
    (∀ j:Fin n,T (H-1-j.val)=some (beta j))  →
    (∀ i,H < i  →  i ≤ H+Q  →  T i=some true)  →
    (∀ i,H+Q < i  →  i < F  →  T i=none)  →  T F=some false  →
    (∀ j,j ≤ 6  →  T (D j)=none)  →
    (∀ i,D 0 < i  →  i < D 1  →  T i=some (decide (i-D 0 ≤ g)))  →
    (∀ i,D 1 < i  →  i < D 2  →  T i=some false)  →
    (∀ i,D 2 < i  →  i < D 3  →  T i=some (decide (i-D 2 ≤ bitLength W)))  →
    (∀ i,D 3 < i  →  i < D 5  →  i ≠ D 4  →  T i=some false)  →
    (∀ i,D 5 < i  →  i < D 6  →  T i=some (decide (i-D 5 ≤ W)))  →
    (∀ i,D 6 < i  →  i ≤ D 12  →  T i=none)  →
    ∀ (_fit:D 12 < tapeLength R B) (hd:D 0 < tapeLength R B) (hh:H < tapeLength R B),
    let c:Config (BodyIngress.machine k).stateCount R B:=⟨BodyIngress.old k (CarryWindow.ready k),⟨D 0,hd⟩,fun i=>T i.val⟩
    let M:=p+bitLength W+W
    ∃ e,e ≤ 1073741824*(R+1)^3  ∧
      (BodyIngress.machine k).run e c=⟨BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode source M)),⟨H,hh⟩,
        fun i=>SerializedBody.prepared T S M F r n g W i.val⟩  ∧
      (∀ u,u ≤ e  →  p ≤ ((BodyIngress.machine k).run u c).head.val  ∧  ((BodyIngress.machine k).run u c).head.val ≤ D 12)  ∧
      (∀ u,u ≤ e  →  ((BodyIngress.machine k).run u c).state ≠ (BodyIngress.machine k).accept  ∧  ((BodyIngress.machine k).run u c).state ≠ (BodyIngress.machine k).reject)  ∧
      (∀ u,u < e  →  ∀ mode:Fin 3,((BodyIngress.machine k).run u c).state ≠ BodyIngress.body k (SerializedBody.entry mode)) := by
  exact body k
theorem check_raw (k : Nat) :
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true  →
    ∃ pr : (Sigma fun q : Nat => PrefixInput
      (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) q)),
    contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr  ∧
    ∃ (z : Nat) (hH : a+m+z+pr.2.n+3  <  tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
    FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z  ∧
    let S:=a+m; let R:=pairLength a m; let B:=FixedRawLengthFence.allocation R
    let n:=pr.2.n; let L:=S+z+2; let F:=FixedRawLengthFence.fencePos R
    let p:=min (9+2*z+2^n) S; let r:=S-p
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
    let Y:=RuntimeBitLength.Target.fullImage X L n F r
    let Z:=AllArityBitLength.Target.seedImage Y F r n
    let c:=initialConfig (BodyIngress.machine k) B (encodePair x w)
    let old:=initialConfig (IngressRepair.machine k) B (encodePair x w)
    let H : Fin (tapeLength R B):=⟨S+z+n+3,hH⟩
    let virtual (T : Nat  →  Option Bool) : Prop :=
      ∃ positive : 0 < n, S ≤ Cursor.Target.M k n z  ∧
      (∀ j : Fin (Cursor.Target.W k n), padRead (Fin.append x w) (Cursor.Target.M k n z+j.val)=false)  ∧
      (treeCircuitWitnessCodec (thresholdPoly k)).decode n (fun _ => false)=
        some (Pnp3.Models.Circuit.input ⟨0,positive⟩)  ∧
      ∃ t s, s ≤ t  ∧  t ≤ 2147483648*(k+1)*(R+1)^5  ∧
      (IngressRepair.machine k).run t old=⟨VirtualLeaf.entry k,H,fun i => T i.val⟩  ∧
      (IngressRepair.machine k).run s old=⟨VirtualLeaf.entry k,H,fun i => T i.val⟩  ∧
      (∀ u, u < s  →  ((IngressRepair.machine k).run u old).state ≠ VirtualLeaf.entry k)  ∧
      (BodyIngress.machine k).run s c=⟨BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.entry k)),H,fun i => T i.val⟩  ∧
      s+5 ≤ 4294967296*(k+1)*(R+1)^5  ∧
      (BodyIngress.machine k).run (s+5) c=
        ⟨BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k false)),H,Function.update (fun i => T i.val) H (some false)⟩  ∧
      (∀ u, u ≤ s+5  →  ((BodyIngress.machine k).run u c).state ≠ (BodyIngress.machine k).accept  ∧
        ((BodyIngress.machine k).run u c).state ≠ (BodyIngress.machine k).reject)  ∧
      (∀ u, u < s+5  →  ∀ b, ((BodyIngress.machine k).run u c).state ≠ BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b)))
    (p=S  →  virtual V)  ∧
    (p < S  →  ∃ fit : F+5*r+n+7  <  tapeLength R B,
      (r < bitLength n  ∧  S < Cursor.Target.M k n z  ∧  virtual (Cursor.Target.image V k S n z F)) ∨
      (bitLength n ≤ r  ∧
        ((Cursor.Target.W k n ≤ r  ∧  ∃ t d e,
          t ≤ 268435456*(k+1)*(R+1)^4  ∧  d ≤ 1048576*(R+1)^3  ∧
          t+d ≤ 8589934592*(k+1)*(R+1)^5  ∧
          (BodyIngress.machine k).run t c=BodyIngress.config k (CarryWindow.config k (VirtualLeaf.config k (IngressRepair.producer.seqEmbedRight (Cursor.machine k)
            ⟨Cursor.q k (430+93*k),⟨F+r+n+3,lt_of_le_of_lt (by omega : F+r+n+3 ≤ F+5*r+n+7) fit⟩,
              fun i => CappedWeight.Target.image Z L n F r 0 (n^k+k) (Cursor.Target.W k n) 0 0 i.val⟩)))  ∧
          (∀ u, u < t  →  ((BodyIngress.machine k).run u c).state ≠ BodyIngress.old k (CarryWindow.embed k (VirtualLeaf.embed k
            (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k (430+93*k))))))  ∧
          (BodyIngress.machine k).run (t+d) c=⟨BodyIngress.old k (CarryWindow.ready k),
            ⟨F+1,lt_of_le_of_lt (by omega : F+1 ≤ F+5*r+n+7) fit⟩,
            fun i => CarryWindow.Target.image (CappedWeight.Target.image Z L n F r 0 (n^k+k) (Cursor.Target.W k n) 0 0)
              F r n (n^k+k) (bitLength (Cursor.Target.W k n)) 0 0 (Cursor.Target.W k n) i.val⟩  ∧
          (∀ u, u < t+d  →  ((BodyIngress.machine k).run u c).state ≠ BodyIngress.old k (CarryWindow.ready k))  ∧
          ∃ fit12 : SerializedBody.delimiter F r n 12  <  tapeLength R B,
          let I:=CarryWindow.Target.image (CappedWeight.Target.image Z L n F r 0 (n^k+k) (Cursor.Target.W k n) 0 0)
            F r n (n^k+k) (bitLength (Cursor.Target.W k n)) 0 0 (Cursor.Target.W k n)
          let mode:=SerializedBody.sourceMode (Fin.append x w) (Cursor.Target.M k n z)
          e ≤ 1073741824*(R+1)^3  ∧  t+d+e ≤ 17179869184*(k+1)*(R+1)^6  ∧
          (∀ i, Cursor.Target.M k n z ≤ i  →  ∀ hi : i < S, I i=some ((Fin.append x w) ⟨i,hi⟩))  ∧
          (BodyIngress.machine k).run (t+d+e) c=
            ⟨BodyIngress.body k (SerializedBody.entry mode),H,
              fun i => SerializedBody.prepared I S (Cursor.Target.M k n z) F r n (n^k+k) (Cursor.Target.W k n) i.val⟩  ∧
          (∀ u, u < t+d+e  →  ∀ mode:Fin 3, ((BodyIngress.machine k).run u c).state ≠ BodyIngress.body k (SerializedBody.entry mode))  ∧
          (∀ u, u ≤ t+d+e  →  ((BodyIngress.machine k).run u c).state ≠ (BodyIngress.machine k).accept  ∧
            ((BodyIngress.machine k).run u c).state ≠ (BodyIngress.machine k).reject)) ∨
        (∃ v2 v3 v4 v5 d, CappedWeight.Target.Cap k n r v2 v3 v4 v5 d  ∧
          S < Cursor.Target.M k n z  ∧  virtual (Cursor.Target.image V k S n z F))))) := by
  exact raw k
end FullIngressClosure
