import FullIngressClosure.Closure
import Complexity.Uniform.V1.BudgetTransport
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- Fixed-k, input-length-only polynomial allocation; no input contents or run witness. -/
def allocation (k R : Nat) : Nat := 1099511627776*(k+1)*(R+1)^8
/-- The literal blank extension, retaining the full old state/head/tape. -/
def extendConfig {states N C B : Nat} (h : C ≤ B) (c : Config states N C) : Config states N B :=
  ⟨c.state,FixedPairParser.tapeEmbed h c.head,
    fun i => if hi : i.val < tapeLength N C then c.tape ⟨i.val,hi⟩ else none⟩
/-- Every concrete prefix configuration is transported, including all high blank cells. -/
def Trace (M : UniformTM) {N C B : Nat} (h : C ≤ B) (y : Bitstring N) (t : Nat) : Prop :=
  ∀ u,u ≤ t → FixedPairParser.ConfigExtension h
    (M.run u (initialConfig M C y)) (M.run u (initialConfig M B y))
/-- Right room is required only for an actual right-moving row; left clamp remains literal. -/
def MoveRoom (M : UniformTM) {N C : Nat} (y : Bitstring N) (t : Nat) : Prop :=
  ∀ u,u < t →
    let c:=M.run u (initialConfig M C y)
    (M.step c.state (c.tape c.head)).2.2=.right → c.head.val+1 < tapeLength N C
/-- Concrete quantitative footprint, not an elapsed-time comparison. -/
def Footprint (M : UniformTM) {N C : Nat} (y : Bitstring N) (t P : Nat) : Prop :=
  ∀ u,u ≤ t → (M.run u (initialConfig M C y)).head.val ≤ P
namespace Target
/-- Full old raw contract with all original outcomes, exact times, and concrete allocation transport. -/
def Raw (k : Nat) : Prop :=
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
    ∃ hBudget : B ≤ allocation k R,
    let large:=initialConfig (BodyIngress.machine k) (allocation k R) (encodePair x w)
    FixedPairParser.ConfigExtension hBudget c large ∧
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
      (∀ u, u < s+5  →  ∀ b, ((BodyIngress.machine k).run u c).state ≠ BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b))) ∧
      Footprint (BodyIngress.machine k) (C:=B) (encodePair x w) (s+5) (12*(R+1)^2) ∧
      MoveRoom (BodyIngress.machine k) (C:=B) (encodePair x w) (s+5) ∧
      Trace (BodyIngress.machine k) hBudget (encodePair x w) (s+5) ∧
      (BodyIngress.machine k).run (s+5) large=
        extendConfig hBudget
          ⟨BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k false)),H,
            Function.update (fun i => T i.val) H (some false)⟩ ∧
      (∀ u,u < s+5 → ∀ b,((BodyIngress.machine k).run u large).state ≠
        BodyIngress.old k (CarryWindow.embed k (CanonicalLeaf.result k b))) ∧
      (∀ u,u ≤ s+5 → ((BodyIngress.machine k).run u large).state ≠ (BodyIngress.machine k).accept ∧
        ((BodyIngress.machine k).run u large).state ≠ (BodyIngress.machine k).reject)
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
            ((BodyIngress.machine k).run u c).state ≠ (BodyIngress.machine k).reject) ∧
          Footprint (BodyIngress.machine k) (C:=B) (encodePair x w) (t+d+e) (12*(R+1)^2) ∧
          MoveRoom (BodyIngress.machine k) (C:=B) (encodePair x w) (t+d+e) ∧
          Trace (BodyIngress.machine k) hBudget (encodePair x w) (t+d+e) ∧
          (BodyIngress.machine k).run (t+d+e) large=
            extendConfig hBudget
              ⟨BodyIngress.body k (SerializedBody.entry mode),H,
                fun i => SerializedBody.prepared I S (Cursor.Target.M k n z) F r n (n^k+k) (Cursor.Target.W k n) i.val⟩ ∧
          (∀ u,u < t+d+e → ∀ mode:Fin 3,((BodyIngress.machine k).run u large).state ≠ BodyIngress.body k (SerializedBody.entry mode)) ∧
          (∀ u,u ≤ t+d+e → ((BodyIngress.machine k).run u large).state ≠ (BodyIngress.machine k).accept ∧
            ((BodyIngress.machine k).run u large).state ≠ (BodyIngress.machine k).reject)) ∨
        (∃ v2 v3 v4 v5 d, CappedWeight.Target.Cap k n r v2 v3 v4 v5 d  ∧
          S < Cursor.Target.M k n z  ∧  virtual (Cursor.Target.image V k S n z F)))))

end Target
end IngressAllocation
