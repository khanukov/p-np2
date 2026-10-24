import CarryWindow.Machine
namespace CarryWindow.Target
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- Exact preserved exterior, bank1 and assignment; only banks0 and2..5 change. -/
def image (T : Nat → Option Bool) (F r n v0 v2 v3 v4 v5 : Nat) : Nat → Option Bool := fun i =>
  if F+1 < i ∧ i < F+r+2 then some (decide (i ≤ F+1+v0))
  else if F+r+n+3 < i ∧ i < F+2*r+n+4 then some (decide (i ≤ F+r+n+3+v2))
  else if F+2*r+n+4 < i ∧ i < F+3*r+n+5 then some (decide (i ≤ F+2*r+n+4+v3))
  else if F+3*r+n+5 < i ∧ i < F+4*r+n+6 then some (decide (i ≤ F+3*r+n+5+v4))
  else if F+4*r+n+6 < i ∧ i < F+5*r+n+7 then some (decide (i ≤ F+4*r+n+6+v5))
  else T i
/-- Arbitrary canonical assignment and exterior; the real six occupied banks are caller frame only here. -/
def Body (k : Nat) : Prop :=
  ∀ {N B : Nat} (L n F r g W : Nat) (beta : Fin n → Bool) (T : Nat → Option Bool),
    let D : Nat → Nat := fun j => match j with
      | 0 => F+1 | 1 => F+r+2 | 2 => F+r+n+3 | 3 => F+2*r+n+4
      | 4 => F+3*r+n+5 | 5 => F+4*r+n+6 | _ => F+5*r+n+7
    L+n+1 < F → g ≤ r → W ≤ r →
    T L=none → T (L+n+1)=none →
    (∀ j : Fin n, T (L+n+1-1-j.val)=some (beta j)) →
    (∀ j, j ≤ 6 → T (D j)=none) →
    (∀ i, D 0 < i → i < D 1 → T i=some true) →
    (∀ i, D 1 < i → i < D 2 → ∃ b, T i=some b) →
    (∀ i, D 2 < i → i < D 3 → T i=some false) →
    (∀ i, D 3 < i → i < D 4 → T i=some (decide (i ≤ D 3+g))) →
    (∀ i, D 4 < i → i < D 5 → T i=some (decide (i ≤ D 4+W))) →
    (∀ i, D 5 < i → i < D 6 → T i=some false) →
    ∀ fit : D 6 < tapeLength N B,
    let c : Config (machine k).stateCount N B :=
      ⟨embed k (VirtualLeaf.embed k (IngressRepair.producer.seqRight (Cursor.machine k)
        (Cursor.q k (430+93*k)))),⟨D 2,by dsimp only [D] at fit ⊢; omega⟩,fun i => T i.val⟩
    ∃ t, t ≤ 8192*(r+1)*(D 6+2)^2 ∧
      (machine k).run t c=⟨ready k,⟨D 0,by dsimp only [D] at fit ⊢; omega⟩,
        fun i => image T F r n g (bitLength W) 0 0 W i.val⟩ ∧
      (∀ u, u ≤ t → D 0 ≤ ((machine k).run u c).head.val ∧
        ((machine k).run u c).head.val ≤ D 6) ∧
      (∀ u, u ≤ t → ((machine k).run u c).state ≠ (machine k).accept ∧
        ((machine k).run u c).state ≠ (machine k).reject) ∧
      (∀ u, u < t → ((machine k).run u c).state ≠ ready k)
/-- Accepted raw fork: virtual leaf branches retained; normal carries actual g,W,ellW. -/
def Raw (k : Nat) : Prop :=
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true →
    ∃ pr : (Sigma fun q : Nat => PrefixInput
      (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) q)),
    contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr ∧
    ∃ (z : Nat) (hH : a+m+z+pr.2.n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
    FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
    let S:=a+m; let R:=pairLength a m; let B:=FixedRawLengthFence.allocation R
    let n:=pr.2.n; let L:=S+z+2; let F:=FixedRawLengthFence.fencePos R
    let p:=min (9+2*z+2^n) S; let r:=S-p
    let U:=Body.extend (Body.installedTape (SmallIngress.prepared B x w z n) L n)
    let V:=Stream.Target.image U S z n (9+2*z) (2^n) (2^n) false
    let X:=CappedWorkspace.Target.image (SuffixCap.Target.image V F r) L n F r
    let Y:=RuntimeBitLength.Target.fullImage X L n F r
    let Z:=AllArityBitLength.Target.seedImage Y F r n
    let c:=initialConfig (machine k) B (encodePair x w)
    let old:=initialConfig (IngressRepair.machine k) B (encodePair x w)
    let H : Fin (tapeLength R B):=⟨S+z+n+3,hH⟩
    let virtual (T : Nat → Option Bool) : Prop :=
      ∃ positive : 0<n, S≤Cursor.Target.M k n z ∧
      (∀ j : Fin (Cursor.Target.W k n), padRead (Fin.append x w) (Cursor.Target.M k n z+j.val)=false) ∧
      (treeCircuitWitnessCodec (thresholdPoly k)).decode n (fun _ => false)=
        some (Pnp3.Models.Circuit.input ⟨0,positive⟩) ∧
      ∃ t s, s≤t ∧ t≤2147483648*(k+1)*(R+1)^5 ∧
      (IngressRepair.machine k).run t old=⟨VirtualLeaf.entry k,H,fun i => T i.val⟩ ∧
      (IngressRepair.machine k).run s old=⟨VirtualLeaf.entry k,H,fun i => T i.val⟩ ∧
      (∀ u, u<s → ((IngressRepair.machine k).run u old).state≠VirtualLeaf.entry k) ∧
      (machine k).run s c=⟨embed k (CanonicalLeaf.entry k),H,fun i => T i.val⟩ ∧
      s+5≤4294967296*(k+1)*(R+1)^5 ∧
      (machine k).run (s+5) c=
        ⟨embed k (CanonicalLeaf.result k false),H,Function.update (fun i => T i.val) H (some false)⟩ ∧
      (∀ u, u≤s+5 → ((machine k).run u c).state≠(machine k).accept ∧
        ((machine k).run u c).state≠(machine k).reject) ∧
      (∀ u, u<s+5 → ∀ b, ((machine k).run u c).state≠embed k (CanonicalLeaf.result k b))
    (p=S → virtual V) ∧
    (p<S → ∃ fit : F+5*r+n+7 < tapeLength R B,
      (r<bitLength n ∧ S<Cursor.Target.M k n z ∧ virtual (Cursor.Target.image V k S n z F)) ∨
      (bitLength n≤r ∧
        ((Cursor.Target.W k n≤r ∧ ∃ t d,
          t≤268435456*(k+1)*(R+1)^4 ∧ d≤1048576*(R+1)^3 ∧
          t+d≤8589934592*(k+1)*(R+1)^5 ∧
          (machine k).run t c=config k (VirtualLeaf.config k (IngressRepair.producer.seqEmbedRight (Cursor.machine k)
            ⟨Cursor.q k (430+93*k),⟨F+r+n+3,lt_of_le_of_lt (by omega : F+r+n+3≤F+5*r+n+7) fit⟩,
              fun i => CappedWeight.Target.image Z L n F r 0 (n^k+k) (Cursor.Target.W k n) 0 0 i.val⟩)) ∧
          (∀ u, u<t → ((machine k).run u c).state≠embed k (VirtualLeaf.embed k
            (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k (430+93*k))))) ∧
          (machine k).run (t+d) c=⟨ready k,⟨F+1,lt_of_le_of_lt (by omega : F+1≤F+5*r+n+7) fit⟩,
            fun i => image (CappedWeight.Target.image Z L n F r 0 (n^k+k) (Cursor.Target.W k n) 0 0)
              F r n (n^k+k) (bitLength (Cursor.Target.W k n)) 0 0 (Cursor.Target.W k n) i.val⟩ ∧
          (∀ u, u≤t+d → ((machine k).run u c).state≠(machine k).accept ∧
            ((machine k).run u c).state≠(machine k).reject) ∧
          (∀ u, u<t+d → ((machine k).run u c).state≠ready k)) ∨
        (∃ v2 v3 v4 v5 d, CappedWeight.Target.Cap k n r v2 v3 v4 v5 d ∧
          S<Cursor.Target.M k n z ∧ virtual (Cursor.Target.image V k S n z F)))))
end CarryWindow.Target
