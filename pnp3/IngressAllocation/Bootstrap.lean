import IngressAllocation.Prepared
import IngressAllocation.SmallPaths
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 PairEncoding Lean Elab Command
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("IngressAllocation.Geometry","IngressAllocation","old_le_new","budgetMono"),
      ("IngressAllocation.Geometry","IngressAllocation","envelope_room","envelopeRoom"),
      ("IngressAllocation.Extension","IngressAllocation","trace_of_qualified_room","traceRoom"),
      ("IngressAllocation.Extension","IngressAllocation","extend_unique","extendUnique"),
      ("IngressAllocation.SmallPaths","IngressAllocation.SmallPrefix","every_head","pathHeads"),
      ("SmallIngress.Runtime","SmallIngress","posttag_0","post0"),
      ("SmallIngress.Runtime","SmallIngress","posttag_1","post1"),
      ("SmallIngress.Runtime","SmallIngress","posttag_2","post2"),
      ("SmallIngress.Runtime","SmallIngress","Path.execute","pathRun")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,.thmInfo ci)] =>
      logInfo m!"private-term|{n}|kind=theorem|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique theorem {mod}/{ns}/{key}: {found.map Prod.fst}"
/-- The actual framing/tag prefix fits the envelope; later loops are not priced by this lemma. -/
private theorem bootstrap_price (a m : Nat) :
    FixedRawLengthFence.installClock (pairLength a m)+FixedRawLengthFence.contentClock a m+3*(a+m)+7
      ≤ 12*(pairLength a m+1)^2 := by
  have positive : pairLength a m ≠ 0 := by simp only [pairLength];omega
  simp only [FixedRawLengthFence.installClock]
  rw [if_neg positive]
  simp only [FixedRawLengthFence.contentClock,pairLength]
  nlinarith only [Nat.zero_le (a*m),Nat.zero_le (a*a),Nat.zero_le (m*m)]
private theorem bootstrap_trace (k : Nat) {a m : Nat} (x : Bitstring a) (w : Bitstring m) :
    let R:=pairLength a m
    let g:=FixedRawLengthFence.installClock R+FixedRawLengthFence.contentClock a m+3*(a+m)+7
    Footprint (BodyIngress.machine k) (C:=FixedRawLengthFence.allocation R) (encodePair x w) g (12*(R+1)^2) ∧
    MoveRoom (BodyIngress.machine k) (C:=FixedRawLengthFence.allocation R) (encodePair x w) g ∧
    Trace (BodyIngress.machine k) (budgetMono k R) (encodePair x w) g := by
  dsimp only
  have heads : Footprint (BodyIngress.machine k)
      (C:=FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
      (FixedRawLengthFence.installClock (pairLength a m)+FixedRawLengthFence.contentClock a m+3*(a+m)+7)
      (12*(pairLength a m+1)^2) := by
    intro u hu
    exact (UniformTM.run_initialConfig_head_le _ _).trans (hu.trans (bootstrap_price a m))
  have room : MoveRoom (BodyIngress.machine k)
      (C:=FixedRawLengthFence.allocation (pairLength a m)) (encodePair x w)
      (FixedRawLengthFence.installClock (pairLength a m)+FixedRawLengthFence.contentClock a m+3*(a+m)+7) := by
    intro u hu
    dsimp only
    intro _
    have bound:=heads u (by omega)
    have strict:=envelopeRoom (pairLength a m)
    omega
  exact ⟨heads,room,traceRoom _ _ _ _ room⟩
private theorem small_modes_trace (N B S : Nat) (n : Fin 3) (T : Nat → Option Bool)
    (full : (if n.val=0 then 9 else 11) ≤ S) (fit : S+6 < tapeLength N B)
    (h6 : T 6=some true) (h7 : T 7=some false) (h8 : T 8=some (n.val==0))
    (h9 : n.val≠0 → T 9=some true) (h10 : n.val≠0 → T 10=some (n.val==2))
    (source : ∀ i,i < S → ∃ b,T i=some b)
    (clear : ∀ i,S ≤ i → i ≤ S+6 → T i=none) :
    ∃ t,t ≤ 6*S+100 ∧
      SmallIngress.producer.run (n:=N) (budget:=B) t
        ⟨SmallIngress.q 124,⟨8,by split_ifs at full <;> omega⟩,fun i=>T i.val⟩=
        ⟨SmallIngress.producer.accept,⟨S+(if n.val=0 then 0 else 1)+2,by split_ifs <;> omega⟩,
          fun i=>SmallIngress.seeded T S n.val i.val⟩ ∧
      ∀ u,u ≤ t → (SmallIngress.producer.run (n:=N) (budget:=B) u
        ⟨SmallIngress.q 124,⟨8,by split_ifs at full <;> omega⟩,fun i=>T i.val⟩).head.val ≤ S+6 := by
  rcases n with ⟨n,hn⟩
  interval_cases n
  · obtain ⟨t,ht,path⟩:=post0 T S (by simpa using full) h6 h7 (by simpa using h8) source clear
    refine ⟨t,ht,pathRun path fit,?_⟩
    exact pathHeads path fit (by
      change 8 < tapeLength N B
      have base : 9 ≤ S := by split_ifs at full <;> omega
      omega)
  · obtain ⟨t,ht,path⟩:=post1 T S (by simpa using full) h6 h7 (by simpa using h8)
      (h9 (by simp)) (by simpa using h10 (by simp)) source clear
    refine ⟨t,ht,pathRun path fit,?_⟩
    exact pathHeads path fit (by
      change 8 < tapeLength N B
      have base : 9 ≤ S := by split_ifs at full <;> omega
      omega)
  · obtain ⟨t,ht,path⟩:=post2 T S (by simpa using full) h6 h7 (by simpa using h8)
      (h9 (by simp)) (by simpa using h10 (by simp)) source clear
    refine ⟨t,ht,pathRun path fit,?_⟩
    exact pathHeads path fit (by
      change 8 < tapeLength N B
      have base : 9 ≤ S := by split_ifs at full <;> omega
      omega)
end IngressAllocation
