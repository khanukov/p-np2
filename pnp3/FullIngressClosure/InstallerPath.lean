import FullIngressClosure.SelectTail
import FullIngressClosure.CounterExterior
import FullIngressClosure.PhysicalFrame
import FullIngressClosure.CompletionClock
namespace FullIngressClosure
open Pnp3.Complexity.Uniform.V1 Pnp4.Frontier.ContractExpansion Lean Elab Command
set_option maxRecDepth 10000
run_cmd do
  let env ← getEnv
  for (mod,ns,key,aliasName) in [
      ("BodyIngress.Native","BodyIngress","Node.mk","pNode"),
      ("BodyIngress.Native","BodyIngress","Path","PPath"),
      ("BodyIngress.Native","BodyIngress","Path.append","pAppend"),
      ("FullIngressClosure.PhysicalFrame","FullIngressClosure","PhysicalFrame","PhysicalFrame"),
      ("FullIngressClosure.PhysicalFrame","FullIngressClosure","PhysicalFrame.six","frameSix"),
      ("FullIngressClosure.PhysicalFrame","FullIngressClosure","PhysicalFrame.fields","frameFields"),
      ("FullIngressClosure.PhysicalFrame","FullIngressClosure","PhysicalFrame.corridor","frameCorridor"),
      ("FullIngressClosure.PhysicalFrame","FullIngressClosure","PhysicalFrame.arena","frameArena"),
      ("FullIngressClosure.CounterFront","FullIngressClosure","installer_counter_front","counterFront"),
      ("FullIngressClosure.CounterFront","FullIngressClosure","counterTape","counterTape"),
      ("FullIngressClosure.CounterExterior","FullIngressClosure","counter_original","counterOriginal"),
      ("FullIngressClosure.CounterExterior","FullIngressClosure","counter_corridor","counterCorridor"),
      ("FullIngressClosure.CounterExterior","FullIngressClosure","counter_arena","counterArena"),
      ("FullIngressClosure.CounterExterior","FullIngressClosure","counter_source","counterSource"),
      ("FullIngressClosure.Environment","FullIngressClosure","Environment","Environment"),
      ("FullIngressClosure.Environment","FullIngressClosure","Environment.mk","environmentMk"),
      ("FullIngressClosure.SourceScan","FullIngressClosure","Corridor.order","corridorOrder"),
      ("FullIngressClosure.SourceArena","FullIngressClosure","Arena.gap","arenaGap"),
      ("FullIngressClosure.SelectTail","FullIngressClosure","select_tail","selectTail"),
      ("FullIngressClosure.CompletionClock","FullIngressClosure","installer_price","installerPrice") ] do
    let found:=env.constants.toList.filter fun (n,_) =>
      n.toString.startsWith ("_private."++mod++".") && n.toString.endsWith ("."++ns++"."++key)
    match found with
    | [(n,ci)] =>
      logInfo m!"private-term|{n}|type={ci.type}"
      modifyScope fun st => {st with openDecls:=.explicit (Name.str .anonymous aliasName) n :: st.openDecls}
    | _ => throwError "Nonunique complete literal installer path {mod}/{key}: {found.map Prod.fst}"
private theorem installer_path (k R S z n p g W Q : Nat) (source : Fin S → Bool) (T : Nat → Option Bool)
    (hr : S ≤ R) (hn : n ≤ R) (physical : p < S)
    (gFits : g ≤ S-p) (wFits : W ≤ S-p) (ellFits : bitLength n ≤ S-p)
    (frame : PhysicalFrame T S (S+z+2) (S+z+2+n+1) (FixedRawLengthFence.fencePos R) (S-p) n Q g (bitLength W) W)
    (cells : ∀ i,p ≤ i → ∀ hi : i < S,T i=some (source ⟨i,hi⟩)) :
    ∃ t,t ≤ 1073741824*(R+1)^3 ∧ PPath k p
      (SerializedBody.delimiter (FixedRawLengthFence.fencePos R) (S-p) n 12) t
      (pNode (BodyIngress.old k (CarryWindow.ready k)) (SerializedBody.delimiter (FixedRawLengthFence.fencePos R) (S-p) n 0) T)
      (pNode (BodyIngress.body k (SerializedBody.entry (SerializedBody.sourceMode source (p+bitLength W+W))))
        (S+z+2+n+1) (SerializedBody.prepared T S (p+bitLength W+W) (FixedRawLengthFence.fencePos R) (S-p) n g W)) := by
  let F:=FixedRawLengthFence.fencePos R
  let r:=S-p
  let D:=SerializedBody.delimiter F r n
  let P:=D 12
  let C:=counterTape T F r n g (bitLength W) W
  have corridor:=frameCorridor frame
  have arena:=frameArena frame
  have order:=corridorOrder corridor
  have gap:=arenaGap arena
  have lower : p ≤ D 0:=by change p ≤ F+1; omega
  have upper : D 12 ≤ P:=le_rfl
  have fitEll : bitLength W ≤ r:=(bitLength_le_self W).trans wFits
  have rR : r ≤ R:=by dsimp only [r]; omega
  obtain ⟨a,ha,front,regs⟩:=counterFront k R r n p g (bitLength W) W T rR hn gFits fitEll wFits ellFits
    (frameSix frame) (frameFields frame) lower
  have environment : Environment D T C S (S+z+2) (S+z+2+n+1) F Q p source := by
    refine environmentMk rfl (counterCorridor T r n g (bitLength W) W corridor arena)
      (counterArena T r n g (bitLength W) W arena) (counterSource T r n g (bitLength W) W source corridor arena cells) ?_
    intro i hi
    exact counterOriginal T F r n g (bitLength W) W i (by rcases hi with h | h; exact Or.inl (Nat.le_of_lt h); exact Or.inr h)
  obtain ⟨b,c,d,e,hb,hc,hd,he,tail⟩:=selectTail (k:=k) (lo:=p) (P:=P) source T C regs environment
    physical (by dsimp only [r]; omega) fitEll wFits le_rfl upper
  have path:=pAppend front tail
  refine ⟨_,?_,path⟩
  have price:=installerPrice R r n (bitLength W) W a b c d e rR hn fitEll wFits ha hb hc hd he
  omega
end FullIngressClosure
