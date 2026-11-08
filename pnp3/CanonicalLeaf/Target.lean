import CanonicalLeaf.Machine
namespace CanonicalLeaf.Target
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- Canonical counter layout H-1-j. The valid donor forward contract is unchanged. -/
def Body (k : Nat) : Prop :=
  ∀ {N B : Nat} (L n : Nat) (beta : Fin n → Bool) (T : Fin (tapeLength N B) → Option Bool)
    (fit : L+n+1 < tapeLength N B),
    T ⟨L,by omega⟩=none → T ⟨L+n+1,fit⟩=none →
    (∀ j : Fin n, T ⟨(L+n+1)-1-j.val,by omega⟩=some (beta j)) →
    let H : Fin (tapeLength N B):=⟨L+n+1,fit⟩
    let c : Config (machine k).stateCount N B:=⟨entry k,H,T⟩
    let b:=if h : 0<n then beta ⟨0,h⟩ else false
    (machine k).run 5 c=
      ⟨if n=0 then (machine k).reject else result k b,H,
        if n=0 then T else Function.update T H (some b)⟩ ∧
    (∀ u, u≤5 → L≤((machine k).run u c).head.val ∧ ((machine k).run u c).head.val≤L+n+1) ∧
    (∀ u, u<5 → ((machine k).run u c).state≠(machine k).accept ∧
      ((machine k).run u c).state≠(machine k).reject) ∧
    (∀ u, u<5 → ∀ v, ((machine k).run u c).state≠result k v) ∧
    (∀ u, u<5 → ((machine k).run u c).tape=T) ∧
    ((treeCircuitWitnessCodec (thresholdPoly k)).decode n (fun _ => false)).map
      (fun c => (Pnp3.Models.Circuit.size c,Pnp3.Models.Circuit.eval c beta))=
      (if n=0 then none else some (1,b)) ∧
    bitLength n+4≤Cursor.Target.W k n ∧
    (∀ pos : 0<n, decodeCircuitFull n (bitLength n) (List.replicate (Cursor.Target.W k n) false)=
      some (Pnp3.Models.Circuit.input ⟨0,pos⟩,List.replicate (Cursor.Target.W k n-(3+bitLength n)) false))
/-- Same accepted raw branch coverage, exact five rows and globally first WORK result. -/
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
      (machine k).run s c=⟨entry k,H,fun i => T i.val⟩ ∧
      s+5≤4294967296*(k+1)*(R+1)^5 ∧
      (machine k).run (s+5) c=
        ⟨result k false,H,Function.update (fun i => T i.val) H (some false)⟩ ∧
      (∀ u, u≤s+5 → ((machine k).run u c).state≠(machine k).accept ∧
        ((machine k).run u c).state≠(machine k).reject) ∧
      (∀ u, u<s+5 → ∀ b, ((machine k).run u c).state≠result k b)
    (p=S → virtual V) ∧
    (p<S → ∃ fit : F+5*r+n+7 < tapeLength R B,
      (r<bitLength n ∧ S<Cursor.Target.M k n z ∧ virtual (Cursor.Target.image V k S n z F)) ∨
      (bitLength n≤r ∧
        ((Cursor.Target.W k n≤r ∧ ∃ t d,
          t≤268435456*(k+1)*(R+1)^4 ∧ d≤524288*(R+1)^3 ∧
          t+d≤4294967296*(k+1)*(R+1)^5 ∧
          (machine k).run t c=VirtualLeaf.config k (IngressRepair.producer.seqEmbedRight (Cursor.machine k)
            ⟨Cursor.q k (430+93*k),⟨F+r+n+3,lt_of_le_of_lt (by omega : F+r+n+3≤F+5*r+n+7) fit⟩,
              fun i => CappedWeight.Target.image Z L n F r 0 (n^k+k) (Cursor.Target.W k n) 0 0 i.val⟩) ∧
          (∀ u, u<t → ((machine k).run u c).state≠VirtualLeaf.embed k
            (IngressRepair.producer.seqRight (Cursor.machine k) (Cursor.q k (430+93*k)))) ∧
          (machine k).run (t+d) c=VirtualLeaf.config k (IngressRepair.producer.seqEmbedRight (Cursor.machine k)
            ⟨Cursor.q k (613+93*k),⟨F+1,lt_of_le_of_lt (by omega : F+1≤F+5*r+n+7) fit⟩,
              fun i => CappedWeight.Target.image Z L n F r (bitLength (Cursor.Target.W k n)) 0 0 (Cursor.Target.W k n) 0 i.val⟩)) ∨
        (∃ v2 v3 v4 v5 d, CappedWeight.Target.Cap k n r v2 v3 v4 v5 d ∧
          S<Cursor.Target.M k n z ∧ virtual (Cursor.Target.image V k S n z F)))))
end CanonicalLeaf.Target
