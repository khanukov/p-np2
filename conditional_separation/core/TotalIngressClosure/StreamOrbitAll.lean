import TotalIngressClosure.StreamAll
namespace TotalIngressClosure
open Pnp3.Complexity.Uniform.V1 Lean Elab Command
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("SmallOrbit.Runtime","SmallOrbit","Frame","StreamFrame"),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.full","fr_full"),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.room","fr_room"),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.source","fr_source"),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.eof","fr_eof"),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.reg","fr_reg"),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.sep","fr_sep"),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.right","fr_right"),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.scratch","fr_scratch"),
      ("SmallOrbit.Runtime","SmallOrbit","Frame.fence","fr_fence"),
      ("SmallOrbit.Runtime","SmallOrbit","install_read","installRead"),
      ("TotalIngressClosure.StreamAll","TotalIngressClosure","finish_all","finishAll"),
      ("IngressAllocation.StreamInstall","IngressAllocation","install_read_heads","readHeads")] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _=>throwError "Nonunique whole Stream interval interface {mod}/{key}: {found.map Prod.fst}"
private theorem orbit_all {N B S z n A F : Nat} (T : Nat → Option Bool)
    (frame : StreamFrame T S z n A F) (fit : F < tapeLength N B)
    (hL : S+z+2 < tapeLength N B) (hH : S+z+n+3 < tapeLength N B) :
    let U:=Body.clear T (S+z+3) n
    let c : Config Stream.machine.stateCount N B:=⟨Stream.machine.start,⟨S+z+2,hL⟩,fun i=>T i.val⟩
    ∃ tb,tb ≤ n+2+InputRead.readClock n z (S-A)+64*(F+1)^2 ∧
      (∀ u,u ≤ tb → (Stream.machine.run u c).head.val ≤ F) ∧
      (if 2^n ≤ F-(S+z+n+3)-1 then
        ∃ hp:Stream.Target.cursor A S (2^n) < tapeLength N B,
          Stream.machine.run tb c=
            ⟨Stream.q (if Stream.Target.cursor A S (2^n)=S then 57 else 58),
              ⟨Stream.Target.cursor A S (2^n),hp⟩,fun i=>Stream.Target.image U S z n A (2^n) (2^n) false i.val⟩
       else Stream.machine.run tb c=
         ⟨Stream.machine.reject,⟨F,fit⟩,
           fun i=>Stream.Target.image U S z n A (F-(S+z+n+3)-1) (F-(S+z+n+3)-1) true i.val⟩) := by
  intro U c
  have low (i : Nat) (hi : i ≤ S+z+2) : U i=T i := by
    unfold U Body.clear;rw [if_neg (by omega)]
  have high (i : Nat) (hi : S+z+n+3 ≤ i) : U i=T i := by
    unfold U Body.clear;rw [if_neg (by omega)]
  obtain ⟨last,price,heads,result⟩:=finishAll N B S z n A F U (fr_full frame).2 (fr_room frame) fit
    (by intro i lo hi;rw [low i (by omega)];exact fr_source frame i lo hi)
    (by rw [low S (by omega)];exact fr_eof frame)
    (by intro i lo hi;rw [low i (by omega)];exact fr_reg frame i lo hi)
    (by rw [low _ le_rfl];exact fr_sep frame)
    (by rw [high _ le_rfl];exact fr_right frame)
    (by intro i lo hi;rw [high i (by omega)];exact fr_scratch frame i lo hi)
    (by rw [high F (by have room:=fr_room frame;omega)];exact fr_fence frame) hH
  let pre:=n+2+InputRead.readClock n z (S-A)
  have preRun:=installRead T frame fit hL
  have headsAll (u : Nat) (hu:u ≤ pre+last):
      (Stream.machine.run u c).head.val ≤ F:=by
    by_cases before:u ≤ pre
    · exact (readHeads T frame fit hL u before).trans (Nat.le_of_lt (fr_room frame))
    · rw [show u=pre+(u-pre) by omega,UniformTM.run_add,preRun]
      exact heads (u-pre) (by omega)
  refine ⟨pre+last,by dsimp only [pre];omega,headsAll,?_⟩
  by_cases rows:2^n ≤ F-(S+z+n+3)-1
  · rw [if_pos rows] at result ⊢
    obtain ⟨hp,done⟩:=result
    exact ⟨hp,by rw [UniformTM.run_add,preRun];exact done⟩
  · rw [if_neg rows] at result ⊢
    rw [UniformTM.run_add,preRun]
    exact result
end TotalIngressClosure
