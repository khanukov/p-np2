import SmallOrbit.Runtime
import Cursor.Proof
namespace AllArityCursor
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
/-- The concrete producer288 followed by the unchanged literal Cursor table.
This differs from Cursor.rawMachine, whose producer has 256 states. -/
def machine (k : Nat) : UniformTM := SmallIngress.producer.seq (Cursor.machine k)
def mapOld (k : Nat) {N B : Nat} (c : Config SmallIngress.machine.stateCount N B) :
    Config (machine k).stateCount N B :=
  ⟨⟨c.state.val,by
      have h : c.state.val < 352 := c.state.isLt
      change c.state.val < 288+Cursor.stateCount k
      unfold Cursor.stateCount; omega⟩,c.head,c.tape⟩
namespace Target
/-- All arities, same parsed Sigma, first work arrival, every paid whole Config,
and two actual live rows. No M or semantic verdict is asserted. -/
def AcceptedRaw (k : Nat) : Prop :=
  ∀ {a m : Nat} (x : Bitstring a) (w : Bitstring m),
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=true →
    ∃ pr : (Sigma fun r : Nat => PrefixInput
      (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec (treeCircuitWitnessCodec (thresholdPoly k))))
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r)),
      contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)=some pr ∧
      Pnp3.Models.Partial.tableLen pr.2.n ≤ a+m ∧
      ∃ (z T t : Nat)
        (hH : a+m+z+pr.2.n+3 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
        FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
        T ≤ 4096*(pairLength a m+1)^2 ∧ t ≤ T ∧
        t+2 ≤ 8192*(pairLength a m+1)^2 ∧
        let U := Body.extend (Body.installedTape (SmallIngress.prepared
          (FixedRawLengthFence.allocation (pairLength a m)) x w z pr.2.n) (a+m+z+2) pr.2.n)
        let V := Stream.Target.image U (a+m) z pr.2.n (9+2*z) (2^pr.2.n) (2^pr.2.n) false
        let p := Stream.Target.cursor (9+2*z) (a+m) (2^pr.2.n)
        let old := initialConfig SmallIngress.machine (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
        let raw := initialConfig (machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
        ∃ (hp : p < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m)))
          (hp1 : p+1 < tapeLength (pairLength a m) (FixedRawLengthFence.allocation (pairLength a m))),
          SmallIngress.machine.run T old = SmallIngress.producer.seqEmbedRight Stream.machine
            ⟨Stream.q (if p=a+m then 57 else 58),⟨p,hp⟩,fun i => V i.val⟩ ∧
          SmallIngress.machine.run t old = SmallIngress.producer.seqEmbedRight Stream.machine
            ⟨Stream.q (if p=a+m then 57 else 58),⟨p,hp⟩,fun i => V i.val⟩ ∧
          (∀ u, u ≤ t → (machine k).run u raw = mapOld k (SmallIngress.machine.run u old)) ∧
          (∀ u, u < t →
            (SmallIngress.machine.run u old).state.val≠345 ∧
            (SmallIngress.machine.run u old).state.val≠346 ∧
            ((machine k).run u raw).state.val≠345 ∧
            ((machine k).run u raw).state.val≠346) ∧
          (∀ r, r < 2^pr.2.n → ∃ u, u < t ∧
            (machine k).run u raw = SmallIngress.producer.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.q k (Stream.paid (Stream.Target.mode U (Stream.Target.cursor (9+2*z) (a+m) r) (a+m))).val,
                ⟨a+m+z+pr.2.n+3,hH⟩,
                fun i => Stream.Target.image U (a+m) z pr.2.n (9+2*z) r (r+1) true i.val⟩) ∧
          (machine k).run t raw = SmallIngress.producer.seqEmbedRight (Cursor.machine k)
            ⟨Cursor.q k (if p=a+m then 57 else 58),⟨p,hp⟩,fun i => V i.val⟩ ∧
          (p=a+m → V p=none ∧
            (machine k).run (t+1) raw = SmallIngress.producer.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.q k 65,⟨p,hp⟩,fun i => V i.val⟩ ∧
            (machine k).run (t+2) raw = SmallIngress.producer.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.q k 66,⟨p+1,hp1⟩,fun i => V i.val⟩) ∧
          (p < a+m → ∃ b : Bool, V p=some b ∧
            (machine k).run (t+1) raw = SmallIngress.producer.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.q k 64,⟨p,hp⟩,fun i => V i.val⟩ ∧
            (machine k).run (t+2) raw = SmallIngress.producer.seqEmbedRight (Cursor.machine k)
              ⟨Cursor.q k (if b then 83 else 68),⟨p+1,hp1⟩,
                fun i => if i.val=p then none else V i.val⟩)
end Target
end AllArityCursor
