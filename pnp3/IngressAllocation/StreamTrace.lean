import IngressAllocation.ArithmeticPaths
namespace IngressAllocation
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("Stream.Kernel","Stream","Arena","Arena"),("Stream.Kernel","Stream","Arena.mk","makeArena"),("Stream.Kernel","Stream","entry","orbitEntry"),
      ("Stream.Kernel","Stream","ended","orbitEnd"),("Stream.Kernel","Stream","embed","pathEmbed"),
      ("Stream.Kernel","Stream","unpaid_orbit","unpaidOrbit"),("Stream.Kernel","Stream","step_row","stepRow"),
      ("Stream.Kernel","Stream","last_overflow","lastOverflow"),("Stream.Kernel","Stream","Path.append","pathAppend"),
      ("Stream.Kernel","Stream","Path.bounds","pathBounds"),("Stream.Kernel","Stream","Path.execute","pathRun"),
      ("Stream.Kernel","Stream","price_bound","priceBound"),
      ("IngressAllocation.ArithmeticPaths","IngressAllocation.StreamStage","every_head","pathHeads")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique literal Stream path interface {mod}/{key}: {found.map Prod.fst}"
private theorem stream_finish_trace (N B S z n A F : Nat) (U : Nat → Option Bool)
    (startLe : A ≤ S) (room : S+z+n+3 < F) (fit : F < tapeLength N B)
    (source : ∀ i,A ≤ i → i < S → ∃ b,U i=some b)
    (eof : U S=none) (reg : ∀ i,S < i → i < S+z+2 → U i=some false)
    (sep : U (S+z+2)=none) (right : U (S+z+n+3)=none)
    (scratch : ∀ i,S+z+n+3 < i → i < F → U i=none) (fence : U F=some false)
    (rows : 2^n ≤ F-(S+z+n+3)-1) (hH : S+z+n+3 < tapeLength N B) :
    ∃ t,t ≤ 64*(F+1)^2 ∧ ∃ hp : Stream.Target.cursor A S (2^n) < tapeLength N B,
      Stream.machine.run t
        ⟨Stream.unpaid (Stream.Target.mode U A S),⟨S+z+n+3,hH⟩,
          fun i=>Stream.Target.image U S z n A 0 0 true i.val⟩=
        ⟨Stream.q (if Stream.Target.cursor A S (2^n)=S then 57 else 58),
          ⟨Stream.Target.cursor A S (2^n),hp⟩,fun i=>Stream.Target.image U S z n A (2^n) (2^n) false i.val⟩ ∧
      ∀ u,u ≤ t → (Stream.machine.run u
        ⟨Stream.unpaid (Stream.Target.mode U A S),⟨S+z+n+3,hH⟩,
          fun i=>Stream.Target.image U S z n A 0 0 true i.val⟩).head.val ≤ F := by
  let arena : Arena U S z n A F:=makeArena startLe room source eof reg sep right scratch fence
  let r:=2^n-1
  have powPos : 0 < 2^n := by positivity
  have hr : r < 2^n := by dsimp only [r];omega
  have last : r+1=2^n := by dsimp only [r];omega
  obtain ⟨t,ht,path⟩:=unpaidOrbit U S z n A F r arena hr (by dsimp only [r];omega)
  obtain ⟨u,hu,next⟩:=stepRow U S z n A F r arena (by dsimp only [r];omega)
  rw [lastOverflow n r hr last] at next
  simp only [↓reduceIte] at next
  rw [last] at next
  have complete:=pathAppend path next
  have bounds:=pathBounds complete
  have price:=priceBound F (F-(S+z+n+3)-1) r t u (by omega) (by dsimp only [r];omega) ht hu
  have zero : Stream.Target.cursor A S 0=A := by simp [Stream.Target.cursor,Nat.min_eq_left startLe]
  have initial : pathEmbed (N:=N) (B:=B) (orbitEntry U S z n A 0) hH=
      ⟨Stream.unpaid (Stream.Target.mode U A S),⟨S+z+n+3,hH⟩,
        fun i=>Stream.Target.image U S z n A 0 0 true i.val⟩ := by
    dsimp only [pathEmbed,orbitEntry]
    rw [zero]
  have run:=pathRun (N:=N) (B:=B) complete fit
  rw [initial] at run
  refine ⟨t+u,price,lt_of_le_of_lt bounds.2 fit,run,?_⟩
  have heads:=pathHeads complete fit hH
  rw [initial] at heads
  exact heads
end IngressAllocation
