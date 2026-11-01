import TotalIngressClosure.Gate
import IngressAllocation.Extension
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 PairEncoding
attribute [local irreducible] UniformTM.run
private theorem seq_prefix (O:UniformTM){N B:Nat}(y:Bitstring N)(room:FixedPairParser.clock N ≤ B)
    (u:Nat)(hu:u ≤ FixedPairParser.clock N):
    (FixedPairParser.machine.seq O).run u (initialConfig (FixedPairParser.machine.seq O) B y)=
      FixedPairParser.machine.seqEmbedRouted O (FixedPairParser.machine.run u (initialConfig FixedPairParser.machine B y)):=by
  have term:=FixedPairParser.ambient_no_public_terminal_before_clock y room
  have run:=FixedPairParser.machine.seq_run_left O (initialConfig FixedPairParser.machine B y)
    (fun v hv=>(term v hv).1) u hu
  rw [←UniformTM.seq_initialConfig] at run
  exact run
private theorem seq_suffix (O:UniformTM){N B:Nat}(y:Bitstring N)(room:FixedPairParser.clock N ≤ B)
    (p:DecodedPair)(parsed:decodePair y=some p)(u:Nat):
    (FixedPairParser.machine.seq O).run (FixedPairParser.clock N+u) (initialConfig (FixedPairParser.machine.seq O) B y)=
      FixedPairParser.machine.seqEmbedRight O (O.run u (initialConfig O B y)):=by
  have entry:(FixedPairParser.machine.seq O).run (FixedPairParser.clock N) (initialConfig (FixedPairParser.machine.seq O) B y)=
      FixedPairParser.machine.seqEmbedRight O (initialConfig O B y):=by
    rw [seq_prefix O y room _ le_rfl,FixedPairParser.ambient_run_initialConfig_accept y room p parsed]
    apply Config.ext_parts
    · change FixedPairParser.machine.seqRoute O FixedPairParser.qAccept=FixedPairParser.machine.seqRight O O.start
      rw [UniformTM.seqRoute,if_pos (show FixedPairParser.qAccept=FixedPairParser.machine.accept from rfl)]
    · rfl
    · rfl
  rw [UniformTM.run_add,entry,UniformTM.seq_run_right]
private theorem seq_span (O:UniformTM){N C B d P:Nat}(h:C ≤ B)(y:Bitstring N)
    (room:FixedPairParser.clock N ≤ B)(p:DecodedPair)(parsed:decodePair y=some p)
    (trace:IngressAllocation.Trace O h y d)
    (heads:IngressAllocation.Footprint O (C:=C) y d P)(inputBound:N ≤ P)
    (safe:∀ u,u ≤ d → (O.run u (initialConfig O C y)).state≠O.accept)
    {J:Type}(targets:J → Fin O.stateCount)
    (first:∀ u,u < d → ∀ j,(O.run u (initialConfig O C y)).state≠targets j):
    let Q:=FixedPairParser.machine.seq O;let c:=initialConfig Q B y
    (∀ u,u ≤ FixedPairParser.clock N+d → (Q.run u c).head.val ≤ P) ∧
    (∀ u,u ≤ FixedPairParser.clock N+d → (Q.run u c).state≠Q.accept) ∧
    (∀ u,u < FixedPairParser.clock N+d → ∀ j,(Q.run u c).state≠FixedPairParser.machine.seqRight O (targets j)):=by
  intro Q c
  have prefixLow(u:Nat)(hu:u < FixedPairParser.clock N):(Q.run u c).state.val < 10:=by
    rw [seq_prefix O y room u hu.le]
    have nonterm:=FixedPairParser.ambient_no_public_terminal_before_clock y room u hu
    change (FixedPairParser.machine.run u (initialConfig FixedPairParser.machine B y)).state≠FixedPairParser.machine.accept ∧
      (FixedPairParser.machine.run u (initialConfig FixedPairParser.machine B y)).state≠FixedPairParser.machine.reject at nonterm
    change (FixedPairParser.machine.seqRoute O _).val < 10
    rw [UniformTM.seqRoute,if_neg nonterm.1,if_neg nonterm.2]
    exact (FixedPairParser.machine.run u (initialConfig FixedPairParser.machine B y)).state.isLt
  have suffixRun(u:Nat):Q.run (FixedPairParser.clock N+u) c=
      FixedPairParser.machine.seqEmbedRight O (O.run u (initialConfig O B y)):=seq_suffix O y room p parsed u
  have oldHeads(u:Nat)(hu:u ≤ d):(O.run u (initialConfig O B y)).head.val ≤ P:=by
    have eq:=congrArg Fin.val (trace u hu).2.1
    change (O.run u (initialConfig O B y)).head.val=(O.run u (initialConfig O C y)).head.val at eq
    exact eq.le.trans (heads u hu)
  have inject:=FixedPairParser.machine.seqRight_injective O
  refine ⟨?_,?_,?_⟩
  · intro u hu
    by_cases early:u ≤ FixedPairParser.clock N
    · rw [seq_prefix O y room u early]
      have ext:=FixedPairParser.ambient_run_extension y room u early
      have low:=FixedPairParser.exact_head_le_input_through_clock y u early
      change (FixedPairParser.machine.run u (initialConfig FixedPairParser.machine B y)).head.val ≤ P
      rw [ext.2.1]
      exact low.trans inputBound
    · rw [show u=FixedPairParser.clock N+(u-FixedPairParser.clock N) by omega,suffixRun]
      change (O.run (u-FixedPairParser.clock N) (initialConfig O B y)).head.val ≤ P
      exact oldHeads (u-FixedPairParser.clock N) (by omega)
  · intro u hu
    by_cases early:u < FixedPairParser.clock N
    · have low:=prefixLow u early
      intro bad
      have eq:=congrArg Fin.val bad
      change (Q.run u c).state.val=10+O.accept.val at eq
      omega
    · rw [show u=FixedPairParser.clock N+(u-FixedPairParser.clock N) by omega,suffixRun]
      intro bad
      have same:(O.run (u-FixedPairParser.clock N) (initialConfig O B y)).state=O.accept:=inject bad
      exact safe (u-FixedPairParser.clock N) (by omega) ((trace _ (by omega)).1.trans same)
  · intro u hu j
    by_cases early:u < FixedPairParser.clock N
    · have low:=prefixLow u early
      intro bad
      have eq:=congrArg Fin.val bad
      change (Q.run u c).state.val=10+(targets j).val at eq
      omega
    · rw [show u=FixedPairParser.clock N+(u-FixedPairParser.clock N) by omega,suffixRun]
      intro bad
      have same:(O.run (u-FixedPairParser.clock N) (initialConfig O B y)).state=targets j:=inject bad
      exact first (u-FixedPairParser.clock N) (by omega) j ((trace _ (by omega)).1.trans same)
end TotalIngressClosure
