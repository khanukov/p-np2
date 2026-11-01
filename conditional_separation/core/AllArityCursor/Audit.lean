import AllArityCursor.Runtime
import Lean
namespace AllArityCursor.Audit
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
def pin_machine (k : Nat) : UniformTM := @AllArityCursor.machine k
def pin_mapOld (k : Nat) {N B : Nat} (c : Config SmallIngress.machine.stateCount N B) :
    Config (AllArityCursor.machine k).stateCount N B := @AllArityCursor.mapOld k N B c
def pin_AcceptedRaw (k : Nat) : Prop := @AllArityCursor.Target.AcceptedRaw k
theorem check_physical_two (k : Nat) {N B : Nat} (V : Nat → Option Bool) (p : Nat)
    (hp : p < tapeLength N B) (hp1 : p+1 < tapeLength N B) (b : Bool) (bit : V p=some b) :
    (machine k).run 1 (SmallIngress.producer.seqEmbedRight (Cursor.machine k)
      ⟨Cursor.q k 58,⟨p,hp⟩,fun i => V i.val⟩)=
        SmallIngress.producer.seqEmbedRight (Cursor.machine k)
          ⟨Cursor.q k 64,⟨p,hp⟩,fun i => V i.val⟩ ∧
    (machine k).run 2 (SmallIngress.producer.seqEmbedRight (Cursor.machine k)
      ⟨Cursor.q k 58,⟨p,hp⟩,fun i => V i.val⟩)=
        SmallIngress.producer.seqEmbedRight (Cursor.machine k)
          ⟨Cursor.q k (if b then 83 else 68),⟨p+1,hp1⟩,
            fun i => if i.val=p then none else V i.val⟩ := AllArityCursor.physical_two k V p hp hp1 b bit
theorem check_eof_two (k : Nat) {N B : Nat} (V : Nat → Option Bool) (p : Nat)
    (hp : p < tapeLength N B) (hp1 : p+1 < tapeLength N B) (blank : V p=none) :
    (machine k).run 1 (SmallIngress.producer.seqEmbedRight (Cursor.machine k)
      ⟨Cursor.q k 57,⟨p,hp⟩,fun i => V i.val⟩)=
        SmallIngress.producer.seqEmbedRight (Cursor.machine k)
          ⟨Cursor.q k 65,⟨p,hp⟩,fun i => V i.val⟩ ∧
    (machine k).run 2 (SmallIngress.producer.seqEmbedRight (Cursor.machine k)
      ⟨Cursor.q k 57,⟨p,hp⟩,fun i => V i.val⟩)=
        SmallIngress.producer.seqEmbedRight (Cursor.machine k)
          ⟨Cursor.q k 66,⟨p+1,hp1⟩,fun i => V i.val⟩ := AllArityCursor.eof_two k V p hp hp1 blank
theorem check_accepted_raw (k : Nat) :
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
                fun i => if i.val=p then none else V i.val⟩) := @AllArityCursor.accepted_raw k
end AllArityCursor.Audit
#print axioms AllArityCursor.machine
#print axioms AllArityCursor.mapOld
#print axioms AllArityCursor.Target.AcceptedRaw
#print axioms AllArityCursor.Audit.pin_machine
#print axioms AllArityCursor.Audit.pin_mapOld
#print axioms AllArityCursor.Audit.pin_AcceptedRaw
#print axioms AllArityCursor.physical_two
#print axioms AllArityCursor.Audit.check_physical_two
#print axioms AllArityCursor.eof_two
#print axioms AllArityCursor.Audit.check_eof_two
#print axioms AllArityCursor.accepted_raw
#print axioms AllArityCursor.Audit.check_accepted_raw
open Lean in
run_cmd do
  let e ← getEnv
  for (n, _) in e.constants.toList do
    if n.toString.startsWith "AllArityCursor." then logInfo m!"surface|{n}"
    if (e.getModuleIdxFor? n).isNone && !n.toString.startsWith "_private." then logInfo m!"owned|{n}"
  for n in e.header.moduleNames do logInfo m!"imported|{n}"
