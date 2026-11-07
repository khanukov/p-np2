import TotalIngressClosure.Target
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 PairEncoding
attribute [local irreducible] UniformTM.run
private theorem budget_mono (k N : Nat) : FixedRawLengthFence.allocation N ≤ allocation k N := by
  have power:(N+1)^2 ≤ (N+1)^8:=Nat.pow_le_pow_right (by omega) (by decide)
  have coeff:16 ≤ 1099511627776*(k+1):=by omega
  exact Nat.mul_le_mul coeff power
private theorem parser_room (k N : Nat) : FixedPairParser.clock N ≤ allocation k N := by
  have small:FixedPairParser.clock N ≤ FixedRawLengthFence.allocation N:=by
    change 2*N+1 ≤ 16*(N+1)^2
    nlinarith only [Nat.zero_le N,Nat.zero_le (N^2)]
  exact small.trans (budget_mono k N)
private theorem old_rows (k : Nat) (q : Fin (BodyIngress.machine k).stateCount) (b : Option Bool) :
    (machine k).step (old k q) b=(old k ((BodyIngress.machine k).step q b).1,((BodyIngress.machine k).step q b).2) :=
  FixedPairParser.machine.seq_step_right (BodyIngress.machine k) q b
private theorem old_injective (k : Nat) : Function.Injective (old k) :=
  FixedPairParser.machine.seqRight_injective (BodyIngress.machine k)
private theorem parser_not_before {N B : Nat} (y : Bitstring N)
    (room:FixedPairParser.clock N ≤ B) (u : Nat) (prior:u < FixedPairParser.clock N) :
    (FixedPairParser.machine.run u (initialConfig FixedPairParser.machine B y)).state ≠ FixedPairParser.machine.accept ∧
    (FixedPairParser.machine.run u (initialConfig FixedPairParser.machine B y)).state ≠ FixedPairParser.machine.reject := by
  exact FixedPairParser.ambient_no_public_terminal_before_clock y room u prior
private theorem parser_prefix (k : Nat) {N B : Nat} (y : Bitstring N)
    (room:FixedPairParser.clock N ≤ B) (u : Nat) (prior:u ≤ FixedPairParser.clock N) :
    (machine k).run u (initialConfig (machine k) B y)=
      FixedPairParser.machine.seqEmbedRouted (BodyIngress.machine k)
        (FixedPairParser.machine.run u (initialConfig FixedPairParser.machine B y)) := by
  have h:=FixedPairParser.machine.seq_run_left (BodyIngress.machine k)
    (initialConfig FixedPairParser.machine B y) (fun t ht=>(parser_not_before y room t ht).1) u prior
  rw [←UniformTM.seq_initialConfig] at h
  exact h
private theorem prefix_states (k : Nat) {N B : Nat} (y : Bitstring N)
    (room:FixedPairParser.clock N ≤ B) (u : Nat) (prior:u < FixedPairParser.clock N) :
    ((machine k).run u (initialConfig (machine k) B y)).state.val < 10 := by
  rw [parser_prefix k y room u (Nat.le_of_lt prior)]
  have safe:=parser_not_before y room u prior
  change (FixedPairParser.machine.seqRoute (BodyIngress.machine k)
    (FixedPairParser.machine.run u (initialConfig FixedPairParser.machine B y)).state).val < 10
  rw [UniformTM.seqRoute,if_neg safe.1,if_neg safe.2]
  exact (FixedPairParser.machine.run u (initialConfig FixedPairParser.machine B y)).state.isLt
private theorem prefix_heads (k : Nat) {N B : Nat} (y : Bitstring N)
    (room:FixedPairParser.clock N ≤ B) (u : Nat) (prior:u ≤ FixedPairParser.clock N) :
    ((machine k).run u (initialConfig (machine k) B y)).head.val ≤ N := by
  rw [parser_prefix k y room u prior]
  have rel:=FixedPairParser.ambient_run_extension y room u prior
  have low:=FixedPairParser.exact_head_le_input_through_clock y u prior
  change (FixedPairParser.machine.run u (initialConfig FixedPairParser.machine B y)).head.val ≤ N
  rw [rel.2.1]
  exact low
private theorem entry (k : Nat) {N B : Nat} (y : Bitstring N)
    (room:FixedPairParser.clock N ≤ B) (p : DecodedPair) (parsed:decodePair y=some p) :
    (machine k).run (FixedPairParser.clock N) (initialConfig (machine k) B y)=
      config k (initialConfig (BodyIngress.machine k) B y) := by
  rw [parser_prefix k y room _ le_rfl,FixedPairParser.ambient_run_initialConfig_accept y room p parsed]
  apply Config.ext_parts
  · change FixedPairParser.machine.seqRoute (BodyIngress.machine k) FixedPairParser.qAccept=
      FixedPairParser.machine.seqRight (BodyIngress.machine k) (BodyIngress.machine k).start
    rw [UniformTM.seqRoute,if_pos (show FixedPairParser.qAccept=FixedPairParser.machine.accept from rfl)]
  · rfl
  · rfl
private theorem suffix (k : Nat) {N B : Nat} (y : Bitstring N)
    (room:FixedPairParser.clock N ≤ B) (p : DecodedPair) (parsed:decodePair y=some p) (u : Nat) :
    (machine k).run (FixedPairParser.clock N+u) (initialConfig (machine k) B y)=
      config k ((BodyIngress.machine k).run u (initialConfig (BodyIngress.machine k) B y)) := by
  rw [UniformTM.run_add,entry k y room p parsed]
  exact FixedPairParser.machine.seq_run_right (BodyIngress.machine k) _ u
private theorem malformed (k : Nat) {N B : Nat} (y : Bitstring N)
    (room:FixedPairParser.clock N ≤ B) (bad:decodePair y=none) :
    (machine k).run (FixedPairParser.clock N) (initialConfig (machine k) B y)=
      ⟨(machine k).reject,⟨0,by simp [tapeLength]⟩,(initialConfig (machine k) B y).tape⟩ := by
  rw [parser_prefix k y room _ le_rfl,FixedPairParser.ambient_run_initialConfig_reject y room bad]
  apply Config.ext_parts
  · change FixedPairParser.machine.seqRoute (BodyIngress.machine k) FixedPairParser.qReject=
      FixedPairParser.machine.seqRight (BodyIngress.machine k) (BodyIngress.machine k).reject
    rw [UniformTM.seqRoute,if_neg (by decide),if_pos (show FixedPairParser.qReject=FixedPairParser.machine.reject from rfl)]
  · rfl
  · rfl
end TotalIngressClosure
