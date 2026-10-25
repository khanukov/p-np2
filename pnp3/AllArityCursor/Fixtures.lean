import AllArityCursor.Safety
import Lean
namespace AllArityCursor.Fixtures
open Pnp3.Complexity.Uniform.V1 PairEncoding
attribute [local irreducible] UniformTM.run
/-- Prepared n0 geometry only: S=11, z=0, H=14, p=min(9+1,11)=10.
This fixture asserts literal post-handoff rows, not accepted raw non-vacuity. -/
theorem n0_physical_false :
    let R := pairLength 5 6
    let B := FixedRawLengthFence.allocation R
    let V : Nat → Option Bool := fun i =>
      if i=7 then none else if i=8 then some true else if i=10 then some false
      else if i < 11 ∨ i=12 then some false else if i=15 then some true
      else if i=53 then some false else none
    (AllArityCursor.machine 0).run 2
      (SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
        (⟨Cursor.q 0 58,⟨10,by decide⟩,fun i => V i.val⟩ : Config (Cursor.machine 0).stateCount R B))=
      SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
        ⟨Cursor.q 0 68,⟨11,by decide⟩,fun i => if i.val=10 then none else V i.val⟩ := by
  dsimp only
  exact (AllArityCursor.physical_two (N := pairLength 5 6)
    (B := FixedRawLengthFence.allocation (pairLength 5 6)) 0
    (fun i => if i=7 then none else if i=8 then some true else if i=10 then some false
      else if i < 11 ∨ i=12 then some false else if i=15 then some true
      else if i=53 then some false else none)
    10 (by decide) (by decide) false (by decide)).2
theorem n0_physical_true :
    let R := pairLength 5 6
    let B := FixedRawLengthFence.allocation R
    let V : Nat → Option Bool := fun i =>
      if i=7 then none else if i=8 then some true else if i=10 then some true
      else if i < 11 ∨ i=12 then some false else if i=15 then some true
      else if i=53 then some false else none
    (AllArityCursor.machine 0).run 2
      (SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
        (⟨Cursor.q 0 58,⟨10,by decide⟩,fun i => V i.val⟩ : Config (Cursor.machine 0).stateCount R B))=
      SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
        ⟨Cursor.q 0 83,⟨11,by decide⟩,fun i => if i.val=10 then none else V i.val⟩ := by
  dsimp only
  exact (AllArityCursor.physical_two (N := pairLength 5 6)
    (B := FixedRawLengthFence.allocation (pairLength 5 6)) 0
    (fun i => if i=7 then none else if i=8 then some true else if i=10 then some true
      else if i < 11 ∨ i=12 then some false else if i=15 then some true
      else if i=53 then some false else none)
    10 (by decide) (by decide) true (by decide)).2
/-- Prepared n0 EOF geometry only: S=9, z=0, H=12; n-width bank is empty. -/
theorem n0_eof :
    let R := pairLength 4 5
    let B := FixedRawLengthFence.allocation R
    let V : Nat → Option Bool := fun i =>
      if i=7 then none else if i=8 then some true else if i < 9 ∨ i=10 then some false
      else if i=13 then some true else if i=44 then some false else none
    (AllArityCursor.machine 0).run 2
      (SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
        (⟨Cursor.q 0 57,⟨9,by decide⟩,fun i => V i.val⟩ : Config (Cursor.machine 0).stateCount R B))=
      SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
        ⟨Cursor.q 0 66,⟨10,by decide⟩,fun i => V i.val⟩ := by
  dsimp only
  exact (AllArityCursor.eof_two (N := pairLength 4 5)
    (B := FixedRawLengthFence.allocation (pairLength 4 5)) 0
    (fun i => if i=7 then none else if i=8 then some true else if i < 9 ∨ i=10 then some false
      else if i=13 then some true else if i=44 then some false else none)
    9 (by decide) (by decide) (by decide)).2
theorem check_n0_physical_false :
    let R := pairLength 5 6
    let B := FixedRawLengthFence.allocation R
    let V : Nat → Option Bool := fun i =>
      if i=7 then none else if i=8 then some true else if i=10 then some false
      else if i < 11 ∨ i=12 then some false else if i=15 then some true
      else if i=53 then some false else none
    (AllArityCursor.machine 0).run 2
      (SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
        (⟨Cursor.q 0 58,⟨10,by decide⟩,fun i => V i.val⟩ : Config (Cursor.machine 0).stateCount R B))=
      SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
        ⟨Cursor.q 0 68,⟨11,by decide⟩,fun i => if i.val=10 then none else V i.val⟩ := @AllArityCursor.Fixtures.n0_physical_false
theorem check_n0_physical_true :
    let R := pairLength 5 6
    let B := FixedRawLengthFence.allocation R
    let V : Nat → Option Bool := fun i =>
      if i=7 then none else if i=8 then some true else if i=10 then some true
      else if i < 11 ∨ i=12 then some false else if i=15 then some true
      else if i=53 then some false else none
    (AllArityCursor.machine 0).run 2
      (SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
        (⟨Cursor.q 0 58,⟨10,by decide⟩,fun i => V i.val⟩ : Config (Cursor.machine 0).stateCount R B))=
      SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
        ⟨Cursor.q 0 83,⟨11,by decide⟩,fun i => if i.val=10 then none else V i.val⟩ := @AllArityCursor.Fixtures.n0_physical_true
theorem check_n0_eof :
    let R := pairLength 4 5
    let B := FixedRawLengthFence.allocation R
    let V : Nat → Option Bool := fun i =>
      if i=7 then none else if i=8 then some true else if i < 9 ∨ i=10 then some false
      else if i=13 then some true else if i=44 then some false else none
    (AllArityCursor.machine 0).run 2
      (SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
        (⟨Cursor.q 0 57,⟨9,by decide⟩,fun i => V i.val⟩ : Config (Cursor.machine 0).stateCount R B))=
      SmallIngress.producer.seqEmbedRight (Cursor.machine 0)
        ⟨Cursor.q 0 66,⟨10,by decide⟩,fun i => V i.val⟩ := @AllArityCursor.Fixtures.n0_eof
/-- Symbolic accepted RAW non-vacuity, separate from the three literal row fixtures.
The canonical serializer supplies the real certificate; no literal trace-word reduction is claimed. -/
theorem canonical_raw_handoff (k : Nat) (n : Fin 3) (b : Bool) :
    let codec := Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
      (Pnp4.Frontier.ContractExpansion.thresholdPoly k)
    let a := Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM codec n.val
    let m := Pnp3.ComplexityInterfaces.certificateLength a 1
    let x := Pnp4.Frontier.ContractExpansion.zeroPrefixQueryValue codec n.val (fun _ => b)
    ∃ w : Bitstring m,
      Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation k a m x w=true ∧
      ∃ t, t ≤ 4096*(pairLength a m+1)^2 ∧
        let c := initialConfig (AllArityCursor.machine k)
          (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
        (((AllArityCursor.machine k).run t c).state.val=345 ∨
          ((AllArityCursor.machine k).run t c).state.val=346) ∧
        ∀ u, u ≤ t → ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).accept ∧
          ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).reject := by
  dsimp only
  obtain ⟨w,accepted⟩ := SmallIngress.Fixtures.canonical_nonvacuity k n b
  exact ⟨w,accepted,AllArityCursor.accepted_prefix_no_verdict k _ w accepted⟩
theorem check_canonical_raw_handoff (k : Nat) (n : Fin 3) (b : Bool) :
    let codec := Pnp4.Frontier.ContractExpansion.treeCircuitWitnessCodec
      (Pnp4.Frontier.ContractExpansion.thresholdPoly k)
    let a := Pnp4.Frontier.ContractExpansion.treeMCSPPrefixM codec n.val
    let m := Pnp3.ComplexityInterfaces.certificateLength a 1
    let x := Pnp4.Frontier.ContractExpansion.zeroPrefixQueryValue codec n.val (fun _ => b)
    ∃ w : Bitstring m,
      Pnp4.Frontier.ContractExpansion.PartAEndpoint.thresholdContentWitnessRelation k a m x w=true ∧
      ∃ t, t ≤ 4096*(pairLength a m+1)^2 ∧
        let c := initialConfig (AllArityCursor.machine k)
          (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
        (((AllArityCursor.machine k).run t c).state.val=345 ∨
          ((AllArityCursor.machine k).run t c).state.val=346) ∧
        ∀ u, u ≤ t → ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).accept ∧
          ((AllArityCursor.machine k).run u c).state≠(AllArityCursor.machine k).reject := @AllArityCursor.Fixtures.canonical_raw_handoff k n b
end AllArityCursor.Fixtures
#print axioms AllArityCursor.Fixtures.n0_physical_false
#print axioms AllArityCursor.Fixtures.check_n0_physical_false
#print axioms AllArityCursor.Fixtures.n0_physical_true
#print axioms AllArityCursor.Fixtures.check_n0_physical_true
#print axioms AllArityCursor.Fixtures.n0_eof
#print axioms AllArityCursor.Fixtures.check_n0_eof
#print axioms AllArityCursor.Fixtures.canonical_raw_handoff
#print axioms AllArityCursor.Fixtures.check_canonical_raw_handoff
open Lean in
run_cmd do
  let e ← getEnv
  for (n, _) in e.constants.toList do
    if n.toString.startsWith "AllArityCursor." then logInfo m!"surface|{n}"
    if (e.getModuleIdxFor? n).isNone && !n.toString.startsWith "_private." then logInfo m!"owned|{n}"
  for n in e.header.moduleNames do logInfo m!"imported|{n}"
