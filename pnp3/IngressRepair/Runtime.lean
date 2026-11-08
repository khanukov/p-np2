import IngressRepair.Transport
namespace IngressRepair
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
set_option maxRecDepth 4000
attribute [local irreducible] UniformTM.run
private theorem accepted_header (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true) :
    FixedContentTagGate.tagMatches (Fin.append x w)=true ∧
    ∃ z, FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z ∧
      (z=0 ∨ 9+z<a+m) := by
  have semantic : contentSemanticAccepts (treeCircuitWitnessCodec (thresholdPoly k))
      (PartAEndpoint.concatV1ToPrefixBitVec x w)=true := by
    unfold PartAEndpoint.thresholdContentWitnessRelation PartAEndpoint.contentWitnessRelation at accepted
    split at accepted
    · rename_i shape
      cases shape
      exact accepted
    · contradiction
  rw [AcceptedBody.concat_eq_append] at semantic
  have tag : FixedContentTagGate.tagMatches (Fin.append x w)=true := by
    have factor := fixedTag_semantic_factorization.1 (treeCircuitWitnessCodec (thresholdPoly k)) (Fin.append x w)
    rw [semantic] at factor
    simpa using factor.symm
  obtain ⟨pr,parsed,_rows,z,_t,_hH,gamma,_⟩ := AllArityWorkspace.accepted_raw k x w accepted
  refine ⟨tag,z,gamma,?_⟩
  by_cases small : pr.2.n<3
  · obtain ⟨g,full,_⟩ := SmallOrbit.small_header_physical k x w accepted parsed small
    have eq : z=(if pr.2.n=0 then 0 else 1) := Option.some.inj (gamma.symm.trans g)
    by_cases hz : pr.2.n=0
    · left; simpa only [hz,if_pos rfl] using eq
    · right
      simp only [if_neg hz] at eq full
      omega
  · have full := GammaSupport.exact k x w parsed semantic (by omega) z gamma
    omega
/-- All accepted words preserve the complete raw run at EVERY time. -/
theorem accepted_transport (k : Nat) : Target.AcceptedTransport k := by
  intro a m x w accepted u
  obtain ⟨tag,z,gamma,physical⟩ := accepted_header k x w accepted
  exact supported_transport k x w z tag gamma physical u
/-- Original all-arity whole-tape/first-q201 or executed EOF ABI, unchanged allocation and clock. -/
theorem accepted_raw (k : Nat) : Target.AcceptedRaw k := by
  intro a m x w accepted
  have old := AllArityWorkspace.accepted_raw k x w accepted
  simpa only [←accepted_transport k x w accepted] using old

/-- Sound literal negative domain: a physical terminator with no first payload. -/
theorem absent_first_payload (k : Nat) : Target.AbsentFirstPayload k := by
  intro a m x w z tag gamma pos short
  obtain ⟨t,h,price,done,first,safe⟩ := missing_payload_run k x w z tag gamma pos short
  refine ⟨t,price,congrArg Config.state done,first,safe,?_⟩
  cases rel : PartAEndpoint.thresholdContentWitnessRelation k a m x w with
  | false => rfl
  | true =>
    obtain ⟨_tag,z',g',phys⟩ := accepted_header k x w rel
    have eq : z=z' := Option.some.inj (gamma.symm.trans g')
    omega
/-- The independently verified old all-k stall word FIRST literally rejects, on its original B9216. -/
theorem repair_witness (k : Nat) : Target.RepairWitness k := by
  let x : Bitstring 11 := fun i => i.val==0 || i.val==2 || i.val==3 || i.val==6 || i.val==10
  let w : Bitstring 0 := Fin.elim0
  have tag : FixedContentTagGate.tagMatches (Fin.append x w)=true := by decide
  have gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some 2 := by decide
  obtain ⟨t,h,price,done,first,safe⟩ := missing_payload_run k x w 2 tag gamma (by decide) (by decide)
  have rel := (absent_first_payload k x w 2 tag gamma (by decide) (by decide))
  obtain ⟨_t,_price,_done,_first,_safe,negative⟩ := rel
  exact ⟨t,price,done,first,safe,negative⟩
/-- Previously proved raw tag/gamma failures still literally reject, at their old polynomial deadline. -/
theorem syntactic_reject (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (bad : FixedContentTagGate.tagMatches (Fin.append x w)=false ∨
      FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=none) :
    ∃ t, t≤128*(pairLength a m+1)^2 ∧
      ((machine k).run t (initialConfig (machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=(machine k).reject ∧
      PartAEndpoint.thresholdContentWitnessRelation k a m x w=false := by
  obtain ⟨t,price,done,_first,_safe,negative,_⟩ := RawFrontier.syntactic_reject k x w bad
  exact ⟨t,price,reject_preserved k _ t done,negative⟩

/-- Soundness of EVERY actual use of the changed row, with no parser/header premise. -/
theorem guard_sound (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m) (t : Nat)
    (atRead : ((machine k).run t (initialConfig (machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state.val=138)
    (blank : let c := (machine k).run t (initialConfig (machine k)
      (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)); c.tape c.head=none) :
    PartAEndpoint.thresholdContentWitnessRelation k a m x w=false := by
  cases rel : PartAEndpoint.thresholdContentWitnessRelation k a m x w with
  | false => rfl
  | true =>
    let c := initialConfig (machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
    let d := (machine k).run t c
    change d.state.val=138 at atRead
    change d.tape d.head=none at blank
    have a0 := accepted_transport k x w rel t
    have a1 := accepted_transport k x w rel (t+1)
    change (machine k).run t c=(AllArityCursor.machine k).run t c at a0
    rw [UniformTM.run,UniformTM.run] at a1
    change (machine k).stepConfig ((machine k).run t c)=
      (AllArityCursor.machine k).stepConfig ((AllArityCursor.machine k).run t c) at a1
    rw [←a0] at a1
    have eq : d.state=producer.seqLeft (Cursor.machine k) (SmallIngress.q 138) := Fin.ext atRead
    have nr : ((producer.seq (Cursor.machine k)).step
        (producer.seqLeft (Cursor.machine k) (SmallIngress.q 138)) none).1=(machine k).reject := by
      rw [UniformTM.seq_step_left]
      have r : producer.step (SmallIngress.q 138) none=(producer.reject,none,.stay) := by decide
      rw [r]; rfl
    have old : ((SmallIngress.producer.seq (Cursor.machine k)).step
        (producer.seqLeft (Cursor.machine k) (SmallIngress.q 138)) none).1.val=140 := by
      change ((SmallIngress.producer.seq (Cursor.machine k)).step
        (SmallIngress.producer.seqLeft (Cursor.machine k) (SmallIngress.q 138)) none).1.val=140
      rw [UniformTM.seq_step_left]
      rfl
    have states := congrArg (fun e => e.state.val) a1
    change ((producer.seq (Cursor.machine k)).step d.state (d.tape d.head)).1.val=
      ((SmallIngress.producer.seq (Cursor.machine k)).step d.state (d.tape d.head)).1.val at states
    rw [blank,eq,nr,old] at states
    have val : (machine k).reject.val=328 := (AllArityCursor.control_values k).2.2.2
    omega
/-- Old wide-header capacity failures remain connected raw literal rejects. -/
theorem capacity_reject (k : Nat) {a m z v : Nat} (x : Bitstring a) (w : Bitstring m)
    (tag : FixedContentTagGate.tagMatches (Fin.append x w)=true)
    (gamma : FixedContentGammaTerminator.gammaZeros? (Fin.append x w)=some z) (wide : 2≤z)
    (digits : ∀ j, j≤z → v.testBit (z-j)=FixedGammaTargetRegisterDecrement.decBit x w z
      (FixedGammaTargetRegisterDecrement.borrow x w z) j)
    (high : ∀ b, z<b → v.testBit b=false) (overflow : FixedRawLengthFence.capacity a m z<v) :
    ∃ t, t≤128*(pairLength a m+1)^2 ∧
      ((machine k).run t (initialConfig (machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w))).state=(machine k).reject ∧
      PartAEndpoint.thresholdContentWitnessRelation k a m x w=false := by
  obtain ⟨t,price,done,_first,_safe,negative,_⟩ := RawFrontier.capacity_reject k x w tag gamma wide digits high overflow
  exact ⟨t,price,reject_preserved k _ t done,negative⟩
end IngressRepair
