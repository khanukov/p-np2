import TotalIngressClosure.SupportedLift
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("IngressAllocation.StreamTrace","IngressAllocation","stream_finish_trace","successTrace"),
      ("Stream.Kernel","Stream","Arena","Arena"),("Stream.Kernel","Stream","Arena.mk","makeArena"),
      ("Stream.Kernel","Stream","entry","orbitEntry"),("Stream.Kernel","Stream","embed","pathEmbed"),
      ("Stream.Kernel","Stream","unpaid_orbit","unpaidOrbit"),("Stream.Kernel","Stream","cut_row","cutRow"),
      ("Stream.Kernel","Stream","Path.append","pathAppend"),("Stream.Kernel","Stream","Path.bounds","pathBounds"),
      ("Stream.Kernel","Stream","Path.execute","pathRun"),("Stream.Kernel","Stream","price_bound","priceBound"),
      ("IngressAllocation.ArithmeticPaths","IngressAllocation.StreamStage","every_head","pathHeads")] do
    let found:=env.constants.toList.filter fun (n,_)=>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)]=>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun s=>{s with openDecls:=.explicit (Name.str .anonymous aliasName) n::s.openDecls}
    | _=>throwError "Nonunique original bounded Stream path {mod}/{key}: {found.map Prod.fst}"
/-- Both actual physical row-budget outcomes. No all-input tableLen support is assumed. -/
private theorem finish_all (N B S z n A F : Nat) (U : Nat → Option Bool)
    (startLe:A ≤ S) (room:S+z+n+3 < F) (fit:F < tapeLength N B)
    (source:∀ i,A ≤ i → i < S → ∃ b,U i=some b) (eof:U S=none)
    (reg:∀ i,S < i → i < S+z+2 → U i=some false) (sep:U (S+z+2)=none)
    (right:U (S+z+n+3)=none) (scratch:∀ i,S+z+n+3 < i → i < F → U i=none)
    (fence:U F=some false) (hH:S+z+n+3 < tapeLength N B) :
    let c:Config Stream.machine.stateCount N B:=
      ⟨Stream.unpaid (Stream.Target.mode U A S),⟨S+z+n+3,hH⟩,
        fun i=>Stream.Target.image U S z n A 0 0 true i.val⟩
    ∃ t,t ≤ 64*(F+1)^2 ∧ (∀ u,u ≤ t → (Stream.machine.run u c).head.val ≤ F) ∧
      (if 2^n ≤ F-(S+z+n+3)-1 then
        ∃ hp:Stream.Target.cursor A S (2^n) < tapeLength N B,
          Stream.machine.run t c=
            ⟨Stream.q (if Stream.Target.cursor A S (2^n)=S then 57 else 58),
              ⟨Stream.Target.cursor A S (2^n),hp⟩,fun i=>Stream.Target.image U S z n A (2^n) (2^n) false i.val⟩
       else Stream.machine.run t c=
         ⟨Stream.machine.reject,⟨F,fit⟩,
           fun i=>Stream.Target.image U S z n A (F-(S+z+n+3)-1) (F-(S+z+n+3)-1) true i.val⟩) := by
  intro c
  by_cases rows:2^n ≤ F-(S+z+n+3)-1
  · obtain ⟨t,price,hp,done,heads⟩:=successTrace N B S z n A F U startLe room fit source eof reg sep right scratch fence rows hH
    exact ⟨t,price,heads,by rw [if_pos rows];exact ⟨hp,done⟩⟩
  · let cap:=F-(S+z+n+3)-1
    let arena:Arena U S z n A F:=makeArena startLe room source eof reg sep right scratch fence
    have capLe:cap ≤ F:=by dsimp only [cap];omega
    obtain ⟨t,price,path⟩:=unpaidOrbit U S z n A F cap arena (by dsimp only [cap];omega) le_rfl
    have cut:=cutRow U S z n A F arena
    have whole:=pathAppend path cut
    have cost:=priceBound F cap cap t (cap+2) capLe le_rfl price (by omega)
    have cursor:Stream.Target.cursor A S 0=A:=by simp [Stream.Target.cursor,Nat.min_eq_left startLe]
    have initial:pathEmbed (N:=N) (B:=B) (orbitEntry U S z n A 0) hH=c:=by
      dsimp only [pathEmbed,orbitEntry,c]
      rw [cursor]
    have done:=pathRun (N:=N) (B:=B) whole fit
    have heads:=pathHeads whole fit hH
    rw [initial] at done heads
    refine ⟨t+(cap+2),cost,heads,?_⟩
    rw [if_neg rows]
    exact done
end TotalIngressClosure
