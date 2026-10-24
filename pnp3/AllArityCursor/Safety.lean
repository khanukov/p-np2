import AllArityCursor.Runtime
import Lean
namespace AllArityCursor
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier Pnp4.Frontier.ContractExpansion
open Pnp4.AlgorithmsToLowerBounds PairEncoding
private theorem no_prior (A : UniformTM) {N B : Nat} (c : Config A.stateCount N B)
    (t : Nat) (outside : (A.run t c).state≠A.accept ∧ (A.run t c).state≠A.reject) :
    ∀ u, u ≤ t → (A.run u c).state≠A.accept ∧ (A.run u c).state≠A.reject := by
  intro u hu
  constructor
  · intro h
    have later : A.run t c=A.run u c := by
      rw [show t=u+(t-u) by omega,A.run_add]
      exact A.run_accept _ h _
    exact outside.1 (by rw [later]; exact h)
  · intro h
    have later : A.run t c=A.run u c := by
      rw [show t=u+(t-u) by omega,A.run_add]
      exact A.run_reject _ h _
    exact outside.2 (by rw [later]; exact h)
/-- Absolute work states for this producer288 wrapper, with literal verdicts. -/
theorem control_values (k : Nat) :
    (SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 57)).val=345 ∧
    (SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 58)).val=346 ∧
    (machine k).accept.val=327 ∧ (machine k).reject.val=328 := by
  have small (i : Nat) (hi : i < 64) : i % Cursor.stateCount k=i :=
    Nat.mod_eq_of_lt (by unfold Cursor.stateCount; omega)
  change 288+57 % Cursor.stateCount k=345 ∧ 288+58 % Cursor.stateCount k=346 ∧
    288+39 % Cursor.stateCount k=327 ∧ 288+40 % Cursor.stateCount k=328
  rw [small 57 (by decide),small 58 (by decide),small 39 (by decide),small 40 (by decide)]
  decide
/-- Accepted raw prefix through first live handoff has no literal verdict.
This does not assert anything about rejecting all false or malformed inputs. -/
theorem accepted_prefix_no_verdict (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true) :
    ∃ t, t ≤ 4096*(pairLength a m+1)^2 ∧
      let c := initialConfig (machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
      (((machine k).run t c).state.val=345 ∨ ((machine k).run t c).state.val=346) ∧
      ∀ u, u ≤ t → ((machine k).run u c).state≠(machine k).accept ∧
        ((machine k).run u c).state≠(machine k).reject := by
  obtain ⟨pr,_parsed,_table,z,T,t,_hH,_gamma,price,ht,_cost,_hp,_hp1,_old,_first,_path,_absent,_paid,endpoint,_eof,_physical⟩ :=
    accepted_raw k x w accepted
  let c := initialConfig (machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
  have hit : ((machine k).run t c).state.val=345 ∨ ((machine k).run t c).state.val=346 := by
    rw [endpoint]
    split_ifs
    · exact Or.inl (control_values k).1
    · exact Or.inr (control_values k).2.1
  refine ⟨t,ht.trans price,hit,no_prior (machine k) c t ?_⟩
  constructor
  · intro h
    have val := congrArg Fin.val h
    rw [(control_values k).2.2.1] at val
    omega
  · intro h
    have val := congrArg Fin.val h
    rw [(control_values k).2.2.2] at val
    omega
theorem Audit.check_control_values (k : Nat) :
    (SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 57)).val=345 ∧
    (SmallIngress.producer.seqRight (Cursor.machine k) (Cursor.q k 58)).val=346 ∧
    (machine k).accept.val=327 ∧ (machine k).reject.val=328 := @AllArityCursor.control_values k
theorem Audit.check_accepted_prefix_no_verdict (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m)
    (accepted : PartAEndpoint.thresholdContentWitnessRelation k a m x w=true) :
    ∃ t, t ≤ 4096*(pairLength a m+1)^2 ∧
      let c := initialConfig (machine k) (FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
      (((machine k).run t c).state.val=345 ∨ ((machine k).run t c).state.val=346) ∧
      ∀ u, u ≤ t → ((machine k).run u c).state≠(machine k).accept ∧
        ((machine k).run u c).state≠(machine k).reject := @AllArityCursor.accepted_prefix_no_verdict k a m x w accepted
end AllArityCursor
#print axioms AllArityCursor.control_values
#print axioms AllArityCursor.Audit.check_control_values
#print axioms AllArityCursor.accepted_prefix_no_verdict
#print axioms AllArityCursor.Audit.check_accepted_prefix_no_verdict
open Lean in
run_cmd do
  let e ← getEnv
  for (n, _) in e.constants.toList do
    if n.toString.startsWith "AllArityCursor." then logInfo m!"surface|{n}"
    if (e.getModuleIdxFor? n).isNone && !n.toString.startsWith "_private." then logInfo m!"owned|{n}"
  for n in e.header.moduleNames do logInfo m!"imported|{n}"
